(** See the copyright notice at the end of this file *)

(** Handle the CCured dependent types *)
open Cil
open Pretty

module H = Hashtbl
module E = Errormsg
module N = Ptrnode
module MU = Markutil

let hasSizeAttr attrs =
  hasAttribute "size" attrs || hasAttribute "count" attrs


(* Changes a formal to a local, and creates a new formal in its place.
   Returns the new formal.
   Whoever calls this should add code to the beginning of the function
   that will initialize v in terms of the new formal. *)
let copyFormal (f: fundec) (v:varinfo) : varinfo =
  (* Create a new formal: *)
  let form = copyVarinfo v (v.vname^"___in") in

  (* Make the old formal into a local. Now references to v in the function
     body will reference the local instead of the formal. *)
  let local = v in 
  f.slocals <- local::f.slocals;
  local.vtype <- typeRemoveAttributes ["size"; "count"] v.vtype;

  form

(* Returns the new formal *)
let processSizedFormal (f: fundec) (allparams: (string * exp) list)
  ~(formal:varinfo) ~(local:varinfo) (a: attrparam) : unit =

  let _, sz = Dependent.compileAttribute allparams ~this:local.vname a in

  let mkptr_size: varinfo = Dependent.getHelperFunction "__mkptr_size" in
  let initLocal = Call(Some (var local),
                       Lval (var mkptr_size),
                       [ Lval (var formal); sz ],
                       !currentLoc) in
  f.sbody.bstmts <- (mkStmtOneInstr initLocal)::f.sbody.bstmts;

  ()

(** Process a function declaration *)
let processFunction (f: fundec) : unit =
  (* Step 1: For all formals f with a SIZE/COUNT annotation, replace f in the
     parameter list with a new "f___in". *)
  let formals' = 
    Ccutil.mapNoCopy
      (fun v -> 
         if hasSizeAttr (typeAttrs v.vtype) then
           copyFormal f v
         else
           v)
      f.sformals
  in
  if formals' != f.sformals then begin
    (* Step 2: For each new "f___in", add an instruction to initialize f
       based on f___in.
       We do this after the duplicating all formals, in case there are circular
       dependencies (e.g. __this) *)
    let oldformals = f.sformals in
    setFormals f formals';
    (* Create a mapping from the old name "f" to the new paramter f___in.
       We do this because, if f was renamed and something depends on "f",
       we should treat that as a dependency on f___in instead.

       e.g. if f is annotated with with "__SIZE((e-f)*(sizeof T))", 
       compile that as:
              "f = __mkptr_size(f___in, (e-f___in)*(sizeof T))"  *)
    let allparams = List.map2
                      (fun oldf newf -> oldf.vname, Lval (var newf))
                      oldformals
                      formals'
    in 
    List.iter2
      (fun oldf newf -> 
         let doFormal: attrparam -> unit =
           processSizedFormal f allparams ~formal:newf ~local:oldf
         in
         Dependent.readAttrs ~doit:doFormal ~default:() newf.vtype)
      oldformals
      formals'
  end;
  ()


let processActual (insertInstrs: instr list -> unit) 
  (allparams: (string * exp) list) 
  (thisArg: exp) 
  (thisFormal_name: string)
  (thisFormal_type: typ)
  (a: attrparam)
  : exp =
  let _, sz = Dependent.compileAttribute allparams ~this:thisFormal_name a in
  let res: varinfo = 
    makeTempVar !MU.currentFunction ~name:("__deparg") thisFormal_type in
  let ptrof_size: varinfo = Dependent.getHelperFunction "__ptrof_size" in
  insertInstrs [Call (Some (var res), Lval (var ptrof_size), 
                      [ thisArg; sz ], !currentLoc)];
  Lval (var res)



let dependentVisitor : cilVisitor = object (self) inherit nopCilVisitor
  method vinst (i: instr) =
    match i with
      Call (reso, f, args, l) ->
        let _, formals, _, _ = splitFunctionType (typeOf f) in
        let formals = (argsToList formals) in
        if List.exists (fun (_,t,a) -> hasSizeAttr (typeAttrs t)) formals
        then begin
          (* allparams maps each formal name to an actual value *)
          let allparams =
            let rec loop formals actuals acc: ((string * exp) list) =
              match formals, actuals with 
                (name, t, a)::restf, arg::resta ->
                  loop restf resta ((name, arg)::acc)
              | [], _ -> (* Out of formals *)
                  acc
              | _, [] -> (* Out of actuals *)
                  E.s (error "To few arguments at %a" d_loc !currentLoc)
            in
            loop formals args []
          in

          (* Now process the actuals *)
          let rec loop formals actuals: exp list =
            match formals, actuals with 
              (name, t, a)::restf, arg::resta ->
                let doActual: attrparam -> exp =
                  processActual self#queueInstr allparams arg name t
                in
                let arg' = Dependent.readAttrs ~doit:doActual ~default:arg t in
                arg'::(loop restf resta)
            | [], _ -> (* Out of formals *)
                actuals
            | _, [] -> (* Out of actuals *)
                E.s (error "To few arguments at %a" d_loc !currentLoc)
          in
          let args' = loop formals args in
          ChangeTo [Call (reso, f, args', l)]
        end
        else 
          SkipChildren
    | _ -> 
        SkipChildren

  method vglob (g: global) : global list visitAction = 
    match g with

    | GFun(f, l) -> 
	MU.currentFunction := f; 
        if isFunctionType f.svar.vtype then
          processFunction f;
        DoChildren

    | _ -> 
        DoChildren
          
end


(* For each formal, move any size/count annotations on the formal to the
   type of the formal. *)
let prepassVisitor : cilVisitor = object (self) inherit nopCilVisitor
  method vvdec (v: varinfo) : varinfo visitAction = 
    if hasSizeAttr v.vattr then begin
      let a', t' = Dependent.moveSizeCountAttrs v.vattr v.vtype in
      v.vtype <- t';
      v.vattr <- a';
      DoChildren
    end
    else
      DoChildren

end


let doit (f: file) = 
  iterGlobals f (fun g -> ignore (visitCilGlobal prepassVisitor g));
  iterGlobals f (fun g -> ignore (visitCilGlobal dependentVisitor g));
  ()
  

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

