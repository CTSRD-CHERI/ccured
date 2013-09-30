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

module H = Hashtbl
module E = Errormsg
module N = Ptrnode

module MU = Markutil

let debugPoly = false

let polyId = ref (-1) 
let newPolyName (base: string) = 
  let res = "/*" ^ (string_of_int (!polyId + 1)) ^ "*/" ^ base in
  incr polyId;
  res
  

(* Split a name into a polymorphic prefix and a base name. The polymorphic 
 * prefix is the empty string if this is not a polymorphic name *)
let splitPolyName (name: string) : string * string = 
  let nl = String.length name in
  if nl = 0 then "", name else
  if String.get name 0 = '/' then
    let rec loop i = (* Search for the second / *)
      if i >= nl - 1 then "", name else 
      if String.get name i = '/' then 
         String.sub name 0 (i + 1), String.sub name (i + 1) (nl - i - 1)
      else 
        loop (i + 1)
    in
    loop 1
  else 
    "", name

(* Strip polymorphic prefix. Return the base name *)
let stripPoly (name: string) : string = 
  let _, n = splitPolyName name in n
  
let isPolyName (name: string) : bool = 
  String.get name 0 = '/'

(* A number of functions will be treated polymorphically. In that case store 
 * their original type. When we process the type of a polymorphic function we 
 * first store here the original type.  *)
(* NOTE: this hash is only accessed with strings that have been
 * passed through 'alphaBaseName', to strip any ___0 etc. suffixes *)
let polyFunc : (string, typ option ref) H.t = H.create 7


(* The same thing for polymorphic structs *)
let polyComps : (string, compinfo option ref) H.t = H.create 7


(* Remember the bodies of polymorphic functions *)
let polyBodies : (string, fundec) H.t = H.create 7


(* strip any ___0 or ___1 etc. suffix introduced during merging to
 * give distinct names to static (file-local) entities.  by using
 * this everywhere, we avoid the need to duplicate #pragma ccuredpoly
 * directives when such entities are split *)
let alphaBaseName (s:string) : string = Alpha.getAlphaPrefix s


let isPolyFunc (vi:varinfo) =
  H.mem polyFunc (alphaBaseName vi.vname)

let lookupPolyFunc (vi:varinfo) =
  H.find polyFunc (alphaBaseName vi.vname)


let isPolyComp (ci:compinfo) =
  H.mem polyComps (alphaBaseName ci.cname)


let makePolyFunc (s: string) =
  let lookup = alphaBaseName s in
  if not (H.mem polyFunc lookup) then begin
    if !E.verboseFlag then
      (* note that if someone explicitly marks a ___0 variant as
       * ccuredpoly we won't see this message, if the non-____0
       * variant's ccuredpoly is seen first *)
      ignore (E.log "Will treat %s as polymorphic\n" s);
    H.add polyFunc lookup (ref None)
  end

let makePolyComp (s: string) =
  let lookup = alphaBaseName s in
  if not (H.mem polyComps lookup) then begin
    if !E.verboseFlag then
      ignore (E.log "Will treat structure %s as polymorphic\n" s);
    H.add polyComps lookup (ref None)
  end


let processPragma = function
    Attr("ccuredpoly", funcs ) -> 
      List.iter 
        (function 
            (AStr s) -> begin
              (* See if we have a space in the name. Then we should have a 
               * "struct foo" or "union bar" *)
              try
                let space = String.index s ' ' in
                let pref = String.sub s 0 space in
                if pref = "struct" || pref = "union" then 
                  (* Skip spaces *)
                  let len = String.length s in
                  let rec skipSpaces i = 
                    if i = len then 
                      ignore (warn "Invalid name %s in ccuredpoly pragma" s)
                    else
                      if String.get s i = ' ' then 
                        skipSpaces (i + 1)
                      else begin
                        makePolyComp (String.sub s i (len - i))
                      end
                  in
                  skipSpaces (space + 1)
                else
                  ignore (warn "Invalid name %s in ccuredpoly pragma" s)
              with _ -> makePolyFunc s (* It must be a function name *)
                  end
          | _ -> ignore (warn "Invalid #pragma ccuredpoly"))
        funcs
        
        (* #pragma ccuredwrapper("foo_wrapper", of("foo")) should make
           foo_wrapper polymorphic.  *)
  | Attr("ccuredwrapper", AStr(s) :: _ ) -> makePolyFunc s 

        (* Allocation functions are also treated polymorphically *)
  | Attr("ccuredalloc", AStr(s) :: _) -> makePolyFunc s

        (* Make nocure functions polymorphic *)
  | Attr("ccuredleavealone", funcs) ->
      List.iter 
        (function 
            (AStr s) -> makePolyFunc s
          | _ -> ignore (unimp "ccuredleavealone pragma must contain only strings"))
        funcs

  | _ -> ()
              


(* Keep track of all instantiations that we did, so we can copy the bodies *)
let instantiations: (string * varinfo) list ref = ref []

(* To avoid going into in an infinite loop keep a track of the instantiations 
 * that are being done *)
let recursiveInstantiations: (string * varinfo) list ref = ref []

(* Take a look at the function and see if we must instantiate it. Return an 
 * instance and a boolean saying if the function is polymorphic . *)
let instantiatePolyFunc (fvi: varinfo) : varinfo * bool = 
  let dropNodeAttrs a = dropAttribute "_ptrnode" a in
  let old_name = fvi.vname in
  let newvi, ispoly = 
    match List.filter (fun (on, ovi) -> on = old_name) !recursiveInstantiations
    with 
    | (_, ovi) :: _  -> ovi, true (* Reuse the recursive instantiation *)
    | [] -> begin
        try
          if debugPoly then 
            ignore (E.log "trying instantiatePoly %s\n" old_name);
          (* sm: fixed bug where we were accessing polyFunc with fvi.vname directly *)
          let origtypref = (lookupPolyFunc fvi) in
          if debugPoly then
            ignore (E.log "Instantiating poly function %s\n" old_name);
          let origtype = (* Copy the type and remember it *)
            match !origtypref with
              Some t -> 
                if debugPoly then
                  ignore (E.log "  Not the first time. Copying: %a\n"
                            d_plaintype t);
                t
            | None -> 
                (* make a copy to return now *)
                let copiedtype = fvi.vtype in
                (* Make a copy to memoize and use to template new copies *)
                let copiedtype2 = fvi.vtype in
                if debugPoly then
                  ignore (E.log "  The first time. Made template: %a\n"
                            d_plaintype copiedtype);
                origtypref := Some copiedtype2;
                copiedtype
          in
          let newvi = 
            { fvi with vtype = origtype; (* Set it like this and doVarInfo 
                                          * will fix it *)
              vname = newPolyName fvi.vname;
              vattr = dropAttribute  
                           "nocure" 
                            (dropNodeAttrs fvi.vattr) }  in
          MU.theFile := GVarDecl (newvi, fvi.vdecl) :: !MU.theFile;
          instantiations := (old_name, newvi) :: !instantiations;
          newvi, true
        with Not_found -> 
          fvi, false    (* Not polymorphic *)
    end
  in
  if debugPoly && ispoly then begin
    ignore (E.log " After instantiatePoly: %s T=%a\n"
              newvi.vname d_plaintype newvi.vtype);
  end;
  newvi, ispoly

let rememberFunctionDefinition (fdec: fundec) = 
  assert(isPolyFunc fdec.svar);
  if debugPoly then 
    ignore (E.log "Found body of polymorphic function %s\n" fdec.svar.vname);
  H.add polyBodies fdec.svar.vname fdec;
  if !N.printVerboseOutput then   
    GText ("// Body of polymorphic " ^ fdec.svar.vname ^ " was dropped\n")
  else
    GText ("//\n")




(* We want to coalesce the polymorphic functions with the same mangling. Map 
 * from the stripped name (with mangling but without the polymorphic prefix) 
 * to the varinfo to the representative *)
let polyFuncRepresentative: (string, varinfo) H.t = H.create 111

(* Return exactly the same if this is a representative *)
let getPolyFuncRepresentative (vi: varinfo) : varinfo = 
  let n = stripPoly vi.vname in
  if n = vi.vname then 
    vi
  else begin
    try
      H.find polyFuncRepresentative n
    with Not_found -> begin
      H.add polyFuncRepresentative n vi;
      vi
    end
  end


(* The same for compinfo *)
let polyCompRepresentative: (string, compinfo) H.t = H.create 111

(* Return exactly the same if this is a representative *)
let getPolyCompRepresentative (ci: compinfo) : compinfo = 
  let n = stripPoly ci.cname in
  if n = ci.cname then 
    ci
  else begin
    try
      H.find polyCompRepresentative n
    with Not_found -> begin
      H.add polyCompRepresentative n ci;
      ci
    end
  end

(* This function is called at the end to create copies of the bodies of the 
 * polymorphic instances and to mark them recursively. The marking is done 
 * using the doNewFunc provided by the caller. We assume that doNewFunc will 
 * eventually call instantiatePolyFunc when it sees an invocation of a 
 * polymorphic function in the copied body *)
let finishInstantiations (doNewFunc: fundec -> unit) = 
  
  (* Now we must process the polymorphic functions. While we do that we might 
   * create new polymorphic instantiations. Careful about infinite loops *)
  let rec loopInstantiations (recs: (string * varinfo) list) (* parents *) = 
    (* See what new instantiations we got *)
    let newinst = List.rev !instantiations in (* Do them in order *)
    instantiations := [];
    List.iter (depthFirst recs) newinst
      
  and depthFirst (recs: (string * varinfo) list) (* Parents *)
                 ((oldname, newvi) as thisone)
      : unit = 
    assert (!instantiations == []);
    let recs' = thisone :: recs in
    recursiveInstantiations := recs'; (* Set the parents for instantiatePoly *)
    (try  
      let body = H.find polyBodies oldname in
      if debugPoly then 
        ignore (E.log "Copying body of function %s\n" newvi.vname);
      let f' = copyFunction body newvi.vname in
      (* We must use newvi as the svar but we have to preserve the 
      * sharing with sformals *)
      setFunctionType f' newvi.vtype;
      newvi.vtype <- f'.svar.vtype;
      f'.svar <- newvi;
      doNewFunc f'
      
    with Not_found -> 
      if debugPoly then
        ignore (E.log "Poly function %s does not have a body or model\n" 
                  oldname)); (* This one does not have a body, or a model *)
    loopInstantiations recs'
  in
  (* Now do the instantiations *)
  loopInstantiations []


(** Called to instantiate a compinfo *)
let rec instantiatePolyComp
    (ci: compinfo)
    (finishNewOnes: compinfo -> unit) : compinfo = 
  if not (isPolyComp ci) then ci else
  (* Keep track of those compinfos that we have made copies of,in this 
   * invocation *)
  let recursiveStructs : (string, compinfo) H.t = H.create 13 in
  (* It is to be made polymorphic. Call our helper function *)
  let rec instAux (ci: compinfo) = 
    (* See if we have done it already *)
    try
      H.find recursiveStructs ci.cname
    with Not_found -> begin
      (* Doing it for the first time *)
      (* We first make a copy of the compinfo *)
      let copyFields (newci: compinfo) = 
        (* Remember the compinfo in case there is recursion *)
        H.add recursiveStructs ci.cname newci;
        (* Now copy the fields and recursively instantiate their types *)
        let rec instType (t: typ) =
          match t with 
            TComp (ci', a) when isPolyComp ci' -> TComp (instAux ci', a)
          | TComp _ -> t
            (* Go down inside pointer, array and function types *)
          | TPtr (t0, a) -> 
              let t0' = instType t0 in 
              if t0' != t0 then TPtr(t0', a) else t
          | TArray (t0, leno, a) -> 
              let t0' = instType t0 in
              if t0' != t0 then TArray (t0', leno, a) else t
            (* Go inside named types *)
          | TNamed (ti, a) -> 
              let t0' = instType ti.ttype in
              if t0' != ti.ttype then 
                typeAddAttributes a t0' (* Don't use the named type anymore *)
              else
                t
          | TFun (t0, args, va, a) -> 
              let t0' = instType t0 in
              if t0' != t0 then TFun (t0', args, va, a) else t
          | _ -> t
        in
        (* Created the field information *)
        let fields = 
          List.map 
            (fun cifld -> 
              (cifld.fname, instType cifld.ftype, 
               cifld.fbitfield, cifld.fattr, cifld.floc))
            ci.cfields in
        fields
      in
      let newci = 
        mkCompInfo ci.cstruct (newPolyName ci.cname) copyFields ci.cattr in
      (* Apply the callback to handle this one *)
      finishNewOnes newci;
      newci
    end
  in
  instAux ci
  
  

 
let initFile () =
  H.clear polyFunc;
  H.clear polyComps;
  polyId := 0;
  instantiations := [];
  H.clear polyBodies;
  H.clear polyFuncRepresentative;
  recursiveInstantiations := []
