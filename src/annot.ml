(*
 * Copyright (c) 2001-2002,
 *  Jeremey Condit      <jcondit@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * this module contains code necessary to insert annotations used by
 * proof-carrying code.
 *)

open Cil
open Trace
open Pretty

module N = Ptrnode

(* makeTypeString
 * produce a string to represent the given type, using the format expected
 * by proof-carrying code's safety policy for ccured *)
let rec makeTypeString = function
    TVoid(_) -> "void"
  | TInt(IChar, _) -> "cchar"
  | TInt(ISChar, _) -> "cchar"
  | TInt(IUChar, _) -> "cuchar"
  | TInt(IInt, _) -> "cint"
  | TInt(IUInt, _) -> "cuint"
  | TInt(IShort, _) -> "cshort"
  | TInt(IUShort, _) -> "cushort"
  | TInt(ILong, _) -> "clong"
  | TInt(IULong, _) -> "culong"
  | TInt(ILongLong, _) -> "clonglong"
  | TInt(IULongLong, _) -> "culonglong"
  | TFloat(FFloat, _) -> "cfloat"
  | TFloat(FDouble, _) -> "cdouble"
  | TFloat(FLongDouble, _) -> "clongdouble"
  | TEnum(_, _) -> "cint"
  | TPtr(t, al) ->
    let (k, _) = N.kindOfAttrlist al in
    let tybasestr =
        match k with
          N.Safe -> "safeptr"
        | N.Seq -> "seqptr"
        | N.FSeq -> "fseqptr"
        | _ -> "unknownptr" in
    let tyargs =
        begin try
        let Attr (_, tyargs) = List.hd (filterAttributes "tyargs" al) in tyargs
        with Failure _ -> []
        end in
    let tyargsstr = List.fold_right
            (fun t s -> match t with AStr x -> " @" ^ x ^ s | _ -> s) tyargs ""
    in
    "(" ^ tybasestr ^ " " ^ (makeTypeString t) ^ tyargsstr ^ ")"
  (* TODO: compute number of array elements *)
  | TArray(t, _, _) -> "(cstackarray " ^ makeTypeString t ^ " 0)"
  | TComp(ci, _) -> "(ccomp " ^ ci.cname ^ ")"
  | TFun(_, _, _, _) -> "function"
  | TNamed({ttype=t}, _) -> makeTypeString t
  | TBuiltin_va_list _ -> "builtin_va_list"

(* varInfoToAnnot
 * convert a single varinfo record to an assembly-language annotation
 * containing the information about that variable *)
let varInfoToAnnot (vi: varinfo) =
    let rec derefArray (t: typ) (e: exp) =
        match t with
            TArray(tsub, _, _) -> derefArray tsub (Lval (mkMem e NoOffset))
          | _ -> e
    in
    Asm ([], ["ann var " ^ vi.vname ^ ",%0," ^
              makeTypeString vi.vtype], [],
         [(None, "X",
           derefArray vi.vtype (Lval (Var vi, NoOffset)))], [], locUnknown)

(* beginAnnot
 * signifies the beginning of a block of annotations *)
let beginAnnot (s: string) =
    Asm ([], ["ann begin " ^ s], [], [], [], locUnknown)

(* endAnnot
 * signifies the end of a block of annotations *)
let endAnnot (s: string) =
    Asm ([], ["ann end " ^ s], [], [], [], locUnknown)

(* makeAnnot
 * produce the list of assembly language instructions corresponding to
 * annotations for a list of variables. *)
let makeAnnot (atype: string) (vil: varinfo list) =
    beginAnnot atype ::
    List.fold_left (fun al vi -> (varInfoToAnnot vi) :: al)
                   [endAnnot atype] vil

(* prependAsm
 * prepend a set of assembly-language annotation statements for each
 * variable in the varinfo list to the block *)
let prependAsm (atype: string) (vil: varinfo list) (bl: block) =
    {bl with bstmts = ((mkStmt (Instr (makeAnnot atype vil))) :: bl.bstmts)}

(* prependAsmStmt
 * prepend a statement containing the given list of instructions to a list
 * of statements.  moves the labels from the beginning of the original
 * statement list to the beginning of the new statement list. *)
let prependAsmStmt (il: instr list) = function
    [] -> [mkStmt (Instr il)]
  | st :: rest ->
    let newst = mkStmt (Instr il)
    in
    {newst with labels = st.labels} :: {st with labels = []} :: rest

(* idom/domlist
 * globals used to hold the immediate dominator function and a list of
 * statements that need to be labeled as dominators.  a bit of hack,
 * but it's ultimately cleaner this way. *)
let idom = ref (fun x -> x)
let domlist = ref []

(* annotateStmts
 * recursively add annotations to a statement *)
let rec annotateStmts (loop: bool) (locals: varinfo list) (sts: stmt list) =
    let patchStmtKind = function
        If(e, b1, b2, l) ->
        If(e, annotateBlock false locals b1, annotateBlock false locals b2, l)
      | Switch(e, b, sl, l) ->
        Switch(e, annotateBlock false locals b, sl, l)
      | Loop(b, l, lb1, lb2 ) ->
        Loop(annotateBlock true locals b, l, lb1, lb2)
      | Block(b) ->
        Block(annotateBlock false locals b)
      | sk -> sk
    in
    match sts with
        [] -> []
      | st :: rest ->
        let newsts = {st with skind = patchStmtKind st.skind} ::
                     annotateStmts false locals rest
        in
        if loop then
            prependAsmStmt (makeAnnot "inv loop" locals) newsts
        else if List.length st.preds > 1 then
            let domid = !idom st.sid in
            let atype = "inv domlabel" ^ (string_of_int domid)
            in
            domlist := domid :: !domlist;
            prependAsmStmt (makeAnnot atype locals) newsts
        else
            newsts

(* annotateBlock
 * recursively add annotations to a block *)
and annotateBlock (loop: bool) (locals: varinfo list) (bl: block) =
    {bl with bstmts = annotateStmts loop locals bl.bstmts}

(* domAnnot
 * produce a dominator annotation *)
let domAnnot (s: string) =
    Asm ([], ["ann dom " ^ s], [], [], [], locUnknown)

(* makeDomStmts
 * add dominator annotations to any statement in domlist *)
let rec markDomStmts (sts: stmt list) =
    let patchDomStmtKind = function
        If(e, b1, b2, l) -> If(e, markDomBlock b1, markDomBlock b2, l)
      | Switch(e, b, sl, l) -> Switch(e, markDomBlock b, sl, l)
      | Loop(b, l, lb1, lb2) -> Loop(markDomBlock b, l, lb1, lb2)
      | Block(b) -> Block(markDomBlock b)
      | sk -> sk
    in
    match sts with
        [] -> []
      | st :: rest ->
        let newsts = {st with skind = patchDomStmtKind st.skind} ::
                     markDomStmts rest
        in
        if List.exists (fun i -> i = st.sid) !domlist then
            let label = "domlabel" ^ (string_of_int st.sid)
            in
            prependAsmStmt [domAnnot label] newsts
        else
            newsts

(* makeDomBlock
 * recursively add dominator annotations to a block *)
and markDomBlock (bl: block) =
    {bl with bstmts = markDomStmts bl.bstmts}

(* annotateFun
 * annotate a single function *)
let annotateFun (func: fundec) =
    (trace "jc" (dprintf "annotating %s\n" func.svar.vname));
    idom := Dominator.computeDominance func;
    domlist := [];
    {func with sbody = prependAsm ("function " ^ func.svar.vname) func.sformals
                  (markDomBlock (annotateBlock false func.slocals func.sbody))}

(* annotateGlob
 * add annotations to all functions in the list of globals *)
let rec annotateGlob (globList: global list) =
    match globList with
        [] -> []
      | GFun(fundec, loc) :: rest ->
        GFun(annotateFun fundec, loc) :: annotateGlob rest
      | g :: rest ->
        g :: annotateGlob rest

(* annotate
 * add annotations to all functions in a file *)
let annotate (f: file) =
    {f with globals = annotateGlob f.globals}

(* ptrAttrCustom
 * custom attribute printer that filters out the special "tyargs"
 * attribute when printing *)
let ptrAttrCustom (Attr (t, _)) =
    if t = "tyargs" then Some nil else None

class ccuredPrinterClass = object
  inherit defaultCilPrinterClass as super

  method pAttr (a:attribute) =
    match ptrAttrCustom a with
      Some d -> d,false
    | None -> super#pAttr a
end

let ccuredPrinter = new ccuredPrinterClass
