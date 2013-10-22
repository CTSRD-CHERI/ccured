(*
 *
 * Copyright (c) 2001-2002,
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
 *)

open Cil
open Pretty
module E = Errormsg
module H = Hashtbl
module IH = Inthash
module MU = Markutil
module N = Ptrnode


(******** STATISTICS **********)
(* Collect statistics about the code *)
let counters : (string, int ref) H.t = H.create 23
class collectCureStats = object (self)
  inherit nopCilVisitor




  method vinst (i: instr) : instr list visitAction =
    let isCheck name =
      let prefix p s =
        let lp = String.length p in
        let ls = String.length s in
        lp <= ls && String.sub s 0 lp = p
      in
      prefix "CHECK_" name
    in
    let incrCount (name: string) =
      try
        let vr = H.find counters name in
        incr vr
      with Not_found -> begin
        let vr = ref 1 in
        H.add counters name vr
      end
    in
    match i with
      Call(_, Lval(Var fvi, NoOffset), _, _) when isCheck fvi.vname ->
        incrCount fvi.vname;
        SkipChildren
    | _ -> SkipChildren



end

(* weimer:
 * visitor routines to check and see if major types have changed *)
let typeSizeHT = Hashtbl.create 555
let compSizeHT = Hashtbl.create 555

let typeSizeSetVisitor = object
  inherit nopCilVisitor
  method vglob g =
    match g with
      GType (t, _) when t.tname <> "" -> begin
        let bs = try bitsSizeOf t.ttype / 8 with _ -> 0 in
        Hashtbl.add typeSizeHT t.tname bs;
        SkipChildren
      end
    | GCompTag (ci, l) when ci.cname <> "" -> begin
        let t = TComp(ci,[]) in
        let bs = try bitsSizeOf t / 8 with _ -> 0 in
        Hashtbl.add compSizeHT ci.cname bs;
        SkipChildren
      end
    | _ -> SkipChildren
end
let rememberTypeSizes (f:file): unit =
  visitCilFileSameGlobals typeSizeSetVisitor f

let warnIfSizeChanged tau ht name other_attrlist =
  let new_bs = try bitsSizeOf tau / 8 with _ -> 0 in
  let old_bs = Hashtbl.find ht name in
  if (new_bs <> old_bs) then begin
    ignore (E.log "****!!! Sizeof %s changed from %d to %d\n"
              name old_bs new_bs);
    let node = Ptrnode.nodeOfAttrlist (typeAttrs tau @ other_attrlist) in
    match node with
      Some(n) when Ptrnode.hasFlag n Ptrnode.pkInterface ->
        let p,i = n.Ptrnode.where in
        ignore (E.log "  and is used in interface function %a\n"
                  Ptrnode.d_place p)
    | _ -> ()
  end

let typeSizeCheckVisitor = object
  inherit nopCilVisitor
  method vglob g =
    match g with
    | GCompTag (ci, l) when ci.cname <> ""
                      && Hashtbl.mem compSizeHT ci.cname -> begin
        let t = TComp(ci,[]) in
        warnIfSizeChanged t compSizeHT ci.cname ci.cattr ;
        SkipChildren
      end
    | GType (t, l) when t.tname <> ""
                       && Hashtbl.mem typeSizeHT t.tname -> begin
        warnIfSizeChanged t.ttype typeSizeHT t.tname [] ;
        SkipChildren
      end
    | _ -> SkipChildren
end
let checkTypeSizes (f:file): unit =
  visitCilFileSameGlobals typeSizeCheckVisitor f

(**************************************************************************)
(**************************************************************************)

(* Look for global variables and functions that are used in a different module
   than they are defined. *)
let differentFile loc1 loc2: bool =
  (loc1 != locUnknown)
  && (loc2 != locUnknown)
  && (loc1.file <> loc2.file)

(* nonStaticVars holds the vids of any global vars or functions that can't be
   declared static. *)
let nonStaticVars: varinfo IH.t = IH.create 29
(* Ditto, for compinfos *)
let nonStaticComps: compinfo IH.t = IH.create 29

let globalFinder = object
  inherit nopCilVisitor
  method vvrbl (v:varinfo) =
    if v.vglob then begin
     (*  ignore (E.log " Considering global %s.\n" v.vname); *)
      try
        match H.find MU.allGlobals (Poly.stripPoly v.vname) with
          Some loc ->
            if (differentFile !currentLoc loc)
              && not (Wrappers.isAWrapper (Poly.stripPoly v.vname))
              && not (IH.mem nonStaticVars v.vid) then begin
(*                 ignore(E.log " %s not static; used in %a but defined in %a.\n" *)
(*                           v.vname d_loc !currentLoc d_loc loc); *)
                IH.add nonStaticVars v.vid v
              end
        | None -> () (* This is an undefined global (i.e. library).  Ignore *)
      with Not_found -> (* variable not even declared. *)
        ()
    end;
    SkipChildren
  method vtype (t:typ) =
    match t with TComp(ci, _) -> begin
      try
        let _, loc = H.find MU.allCompinfo ci.cname in
        if not (IH.mem nonStaticComps ci.ckey)
          && (differentFile !currentLoc loc) then begin
(*             ignore (E.log " Comp %s not static 'cause used in %a but defined in %a.\n" *)
(*                       ci.cname d_loc !currentLoc d_loc loc); *)
            IH.add nonStaticComps ci.ckey ci
          end;
        SkipChildren
      with Not_found ->
(*         ignore (warn "Comp info %s not registered.\n" ci.cname); *)
        SkipChildren
    end
    | _ -> DoChildren
end



(* How many nodes need ... *)
type stats = {
  totalOccurances: int ref;
  bounds: int ref;
  rtti: int ref;
  local: int ref;
  ptrptr: int ref; (* pointers to pointers *)
  openarray: int ref;
  union: int ref; (* comps only *)
  vararg: int ref; (* funcs only *)
}
let newStats (): stats = {
  totalOccurances = ref 0;
  bounds = ref 0;
  rtti = ref 0;
  local = ref 0;
  ptrptr = ref 0;
  openarray = ref 0;
  union = ref 0;
  vararg = ref 0;
}
let printStats out what s: unit =
  let doOne cnt dsc: unit =
    if !cnt <> 0 then
      ignore(fprintf out "   %3d  %s.\n" !cnt dsc)
  in
  ignore(fprintf out " %d %s found\n" !(s.totalOccurances) what);
  doOne s.bounds "need bounds";
  doOne s.rtti "RTTI";
  doOne s.local "ptr to stack";
  doOne s.ptrptr "involve nested pointers";
  doOne s.openarray "open arrays";
  doOne s.union "unions";
  doOne s.vararg "vararg functions";
  ()

let isSeq: N.opointerkind -> bool = function
  | N.Seq | N.FSeq | N.Index | N.Wild
  | N.SeqN | N.FSeqN | N.SeqR | N.FSeqR
  | N.IndexT | N.WildT | N.SeqT | N.FSeqT | N.SeqNT | N.FSeqNT
  | N.SeqC | N.FSeqC | N.SeqNC | N.FSeqNC | N.SeqRC | N.FSeqRC
      -> true
  | _ -> false


(* print with context.
   We do this so the context info is only printed if needed. *)
type context = { ctx: doc;
                 indent: int;
                 mutable contents: doc;
               }
let topLevel = {ctx=nil; indent=0; contents = nil;}
let current = ref topLevel

(* print something.  Also print the current context info, if it hasn't already been printed.*)
let doPrint (d:doc): unit =
  if (!current).contents = nil then begin
    (* print the context too. *)
    (!current).contents <- (!current).ctx
  end;
  (!current).contents <- (!current).contents ++ d


let withContext (d:doc) (f: 'a -> unit) (x: 'a): unit =
  let old = !current in
  let ctx =
    let ind = (!current).indent in
    text (String.make ind ' ') ++ d
  in
  let newStuff = {ctx=ctx; indent=old.indent+3; contents = nil} in
  current := newStuff;
  f x;
  current := old;
  (* print the new stuff in the old context, if there's anything to print. *)
  if newStuff.contents <> nil then
    doPrint newStuff.contents;
  ()

let dump (out:out_channel):unit =
  fprint out 60 (!current).contents;
  (!current).contents <- nil;
  ()

let doPrintInd (d:doc): unit =
  let ind = (!current).indent in
  doPrint (text (String.make ind ' ') ++ d)
let doPrintNode (nid:int) (s:string): unit =
  let d = dprintf "Node %d %s.\n" nid s in
  doPrintInd d

(* Friendlier printing of nodes. *)
let d_type = printType N.ccuredInferPrinter

let rec examineType (ctr:stats) t : unit =
  let t = unrollType t in
  match t with
    TVoid _
  | TBuiltin_va_list _
  | TInt _
  | TFloat _
  | TEnum _ -> ()
  | TPtr (bt, a) ->
      let k, _ = N.kindOfAttrlist a in
      let n = match  N.nodeOfAttrlist a with
         None -> E.s (bug "Missing node for %a" d_type t)
       | Some n -> n
      in
      if isSeq k then begin
        incr ctr.bounds;
        doPrintNode n.N.id "needs bounds"
      end;
      if N.isRTTI k then begin
        incr ctr.rtti;
        doPrintNode n.N.id "needs RTTI"
      end;
      if N.hasFlag n N.pkStack && not (hasAttribute "noescape" a) then begin
        incr ctr.local;
        doPrintNode n.N.id "points to the stack"
      end;
     (*  if isPointerType bt then incr ctr.ptrptr; *)
      examineType ctr bt
  | TArray (bt, lo, a) ->
      let n = match  N.nodeOfAttrlist a with
         None -> E.s (bug "Missing node for %a" d_type t)
       | Some n -> n
      in
      let isOpen = match lo with
          None  -> true
        | Some l -> isZero l
      in
      if isOpen then begin
        doPrintNode n.N.id "contains an open array";
        incr ctr.openarray
      end;
      (* if isPointerType bt then incr ctr.ptrptr; *)
      examineType ctr bt
  | TFun(rt, args, isva, a) ->
      if isva then begin
        incr ctr.vararg;
        doPrintInd (text "Vararg function.\n")
      end;
      withContext (dprintf "In return type [%a]:\n" d_type rt)
        (examineType ctr) rt;
      List.iter (fun (n, t, _) ->
                   withContext (dprintf "In formal \"%s\" [%a]:\n" n d_type t)
                     (examineType ctr) t
                )
        (argsToList args)
  | TComp _ -> ()(* We visit these separately. *)
  | TNamed _ -> E.s (bug "unrollType")

let printGlobalAnnotations (out: out_channel) (f:file): unit =
  visitCilFileSameGlobals globalFinder f;

  let functionStats: stats = newStats () in
  let variableStats: stats = newStats () in
  let doGlobal g: unit =
    match g with
      GFun (fdec, l) ->
        let vi = fdec.svar in
        if IH.mem nonStaticVars vi.vid then begin
          incr functionStats.totalOccurances;
          withContext (dprintf "\nIn global function %s (%a):\n" vi.vname
                         d_loc l)
            (examineType functionStats) vi.vtype
        end
    | GVar (vi, _, l) ->
        if IH.mem nonStaticVars vi.vid then begin
          incr variableStats.totalOccurances;
          withContext (dprintf "\nIn global %s (%a):\n" vi.vname
                         d_loc l)
            (examineType variableStats) vi.vtype
        end
    | _ -> ()
  in
  iterGlobals f doGlobal;
  let compStats: stats = newStats () in
  let doComp (ci:compinfo): unit =
    incr compStats.totalOccurances;
    if not ci.cstruct then begin
      doPrintInd (text "is a union.\n");
      incr compStats.union;
    end;
    List.iter (fun fi ->
                 withContext (dprintf "In field %s [%a]:\n"
                                fi.fname d_type fi.ftype)
                   (examineType compStats) fi.ftype)
      ci.cfields
  in
  IH.iter (fun _ ci ->
             withContext (dprintf "\nIn %s:\n" (compFullName ci))
               doComp ci
          )
    nonStaticComps;

  ignore(fprintf out
           "Summary of the annotation burden for \"%s\".\n" f.fileName);
  ignore(fprintf out
           "Remember that this excludes library functions with wrappers.\n");
  ignore(fprintf out
         "This also excludes any nodes that have already been annotated.\n\n");
  ignore(fprintf out "**************************************************\n");
  printStats out "Global variables" variableStats;
  printStats out "Global functions" functionStats;
  printStats out "Structs and unions" compStats;
  ignore(fprintf out "**************************************************\n\n");
  dump out;
  flush out;
  IH.clear nonStaticVars;
  IH.clear nonStaticComps;
  ()

(**************************************************************************)
(**************************************************************************)

(* similar to examineType, but for listGlobalAnnotations instead of
   printGlobalAnnotations. *)
let rec listExamineType ?(suppressBoundsWarning=false)
  (where: string) (t:typ): unit =
  let reportNodeDoc (what:doc): unit =
    let di_type = printType N.ccuredInferPrinter  in
    E.log "%a@[: node (%a) in %s %a@]\n" d_loc !currentLoc
      di_type t where insert what
  in
  let reportNode (what:string): unit =
    reportNodeDoc (text what)
  in
  let t = unrollType t in
  let nodeOf (a:attributes) : N.node =
    match  N.nodeOfAttrlist a with
      None -> E.s (bug "Missing node for %a" d_type t)
    | Some n -> n
  in
  match t with
    TVoid _
  | TBuiltin_va_list _
  | TInt _
  | TFloat _
  | TEnum _ -> ()

  | TPtr (bt, a)
  | TArray (bt, _, a) when hasAttribute "annotated" a ->
      listExamineType where bt;

  | TPtr (bt, a) ->
      listExamineType where bt;
      let k, _ = N.kindOfAttrlist a in
      if not suppressBoundsWarning && isSeq k then begin
        reportNode "is Seq/FSeq"
      end;
      if N.isRTTI k then begin
        reportNode "is RTTI"
      end;
      if isVoidType bt then begin
        let n = nodeOf a in
        let rep = N.get_rep n in
        if not(isVoidType rep.N.btype) then
          reportNodeDoc
            ((text "is a void* that CCured has inferred to be a ")
             ++ d_type () (TPtr(rep.N.btype,[])))
      end;
(*       if N.hasFlag n N.pkStack && not (hasAttribute "noescape" a) then begin *)
(*         reportNode n "points to the stack" *)
(*       end; *)
      ()
  | TArray (bt, lo, a) ->
      listExamineType where bt;
      let isOpen = match lo with
          None  -> true
        | Some l -> isZero l
      in
      if isOpen then begin
        reportNode "contains an open array"
      end
  | TFun(rt, args, isva, a) ->
(*       if isva then begin *)
(*         incr ctr.vararg; *)
(*         doPrintInd (text "Vararg function.\n") *)
(*       end; *)
      listExamineType "<function pointer return type>" rt;
      List.iter (fun (n, t, _) ->
                   listExamineType ("<function pointer formal "^n^">") t)
        (argsToList args)
  | TComp _ -> ()(* We visit these separately. *)
  | TNamed _ -> E.s (bug "unrollType")

(* listGlobalAnnotations lists all of the annotations needed by Deputy.
   It's similar to printGlobalAnnotations, but it lists the results one
   at a time on stdout, and it includes even static globals. *)
let listGlobalAnnotations (f:file): unit =
  E.log "\nListing annotations needed for Deputy.\n";
  let oldPCI = !print_CIL_Input in
  print_CIL_Input := true;

  (* Maintain a map from globals to the location of their first declaration.
     If a var has no location (probably because it's Poly), use the
     location of it's declaration.  *)
  let declarations: location IH.t = IH.create 50 in
  let setLoc vi: unit =
    if !currentLoc == locUnknown then begin
      if IH.mem declarations vi.vid then
        currentLoc := IH.find declarations vi.vid
    end else
      if not (IH.mem declarations vi.vid) then
        IH.add declarations vi.vid !currentLoc
  in
  let doGlobal g: unit =
    match g with
      GVarDecl (vi, l) when isFunctionType vi.vtype ->
        currentLoc := l;
        setLoc vi;
        (* E.log "visiting %s at %a\n" vi.vname d_loc l; *)
(*         if Wrappers.hasAWrapper (Poly.stripPoly vi.vname) then *)
(*           E.log "%a: @[extern function %s has a wrapper,\n   so some needed annotations may not be shown@]\n" d_loc l vi.vname; *)
        if not (hasAttribute "annotated" vi.vattr) then begin
          let rt, formals, _, _ = splitFunctionType vi.vtype in
          listExamineType "the return value" rt;
          List.iter (fun (n,t,_) ->
                       listExamineType ("formal \""^n^"\"") t)
            (argsToList formals);
        end
    | GFun (fdec, l) ->
        currentLoc := l;
        setLoc fdec.svar;
        (* E.log "visiting %s at %a\n" fdec.svar.vname d_loc l; *)
(*         if Wrappers.isAWrapper (Poly.stripPoly fdec.svar.vname) then *)
(*           E.log "%a: skipping wrapper %s\n" d_loc l fdec.svar.vname *)
(*         else *)
        begin
          let rt, formals, _, _ = splitFunctionType fdec.svar.vtype in
          listExamineType "the return value" rt;
          List.iter (fun vi -> listExamineType ("formal \""^vi.vname^"\"") vi.vtype)
            fdec.sformals;
          List.iter (fun vi ->
                       listExamineType ~suppressBoundsWarning:true
                       ("local \""^vi.vname^"\"") vi.vtype)
            fdec.slocals
        end
    | GVarDecl (vi, l)
    | GVar (vi, _, l) ->
        currentLoc := l;
        setLoc vi;
        listExamineType vi.vname vi.vtype
    | GCompTag (ci, l) when ci.cname = "__ccured_va_localinfo" ->
        ()
    | GCompTag (ci, l) ->
        currentLoc := l;
        List.iter
          (fun fi -> listExamineType ("field \""^fi.fname^"\"") fi.ftype)
          ci.cfields
    | _ -> ()
  in
  iterGlobals f doGlobal;
  E.log "Done lising annotations needed for Deputy.\n\n\n";
  print_CIL_Input := oldPCI;
  ()


(**************************************************************************)
(**************************************************************************)

let printChecks (f: file) =
  H.clear counters;
  ignore (visitCilFile (new collectCureStats) f);
  let allChecks = ref 0 in
  let l =
    H.fold (fun name counter acc ->
      allChecks := !allChecks + !counter;
      (name, !counter) :: acc) counters [] in
  (* Now sort for most frequent first *)
  let l = List.sort (fun (_, c1) (_, c2) -> (compare c2 c1)) l in
  H.clear counters;
  if !allChecks = 0 then
    ignore (E.log "No checks were inserted!\n")
  else begin
    ignore (E.log "Static count of CHECKs inserted:\n");
    List.iter
      (fun (n, c) -> ignore (E.log " %-30s %6d (%6.2f%%)\n"
                               n c (100.0 *. (float c) /. (float !allChecks))))
      l
  end
