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
module MU = Markutil
module N = Ptrnode

let funinfoToVarinfo (fi: MU.funinfo) : varinfo  =
  match fi with 
    MU.Declared vi -> vi
  | MU.Defined fdec -> fdec.svar

let nodeOfType t = 
  match unrollType t with 
    TPtr(_, a) -> begin
      match N.nodeOfAttrlist a with
        Some n -> n
      | None -> N.dummyNode
    end
  | _ -> N.dummyNode

(** Add compatibility edge between two types *)
let markCompatibleTypes (who: string) (parent: string) (loc: location)
                        (t1: typ) (t2: typ) (ek: N.edgekind) = 
  let n1 = nodeOfType t1 in
  let n2  = nodeOfType t2 in
  match n1 == N.dummyNode, n2 == N.dummyNode with
    true, true -> () (* scalar -> scalar *)
  | false, false -> (* pointer to pointer *)
      let _ = N.addEdge n1 n2 ek None in 
      let _ = N.addEdge n2 n1 ek None in
      ()
  | _, _ -> 
      ignore (E.warn "%a: trying to markCompatibleTypes: %a and %a (%s)\n(because %s overrides %s)\n"
                d_loc loc d_type t1 d_type t2
                (match ek with N.ESameKind N.EEK_trustedCast -> "ETrustedCast"
                               | _ -> "ECast") 
                who parent)
  

(** Add compatibility edges between two function types *)
let markOverrideFunctionType  (who: string) (loc: location) (ftype: typ) = 
  match filterAttributes "override" (typeAttrs ftype) with 
  | [ Attr(_, [AStr parent]) ] -> begin
      try
        let pvi = 
          try funinfoToVarinfo (H.find MU.allFunctions parent) 
          with Not_found -> 
            ignore (E.warn "%a: Cannot find definition of overriden %s\n" d_loc loc parent);
            raise Not_found
        in
        (* Now add compatibility edges *)
        let rt1, args1, isva1, _ = splitFunctionType ftype in
        let rt2, args2, isva2, _ = splitFunctionType pvi.vtype in
        let args1 = argsToList args1 in
        let args2 = argsToList args2 in
        if List.length args1 <> List.length args2 then begin
          ignore (E.warn 
                    "%a: Trying to override function (%s) with different # of arguments for parent %s" 
                    d_loc loc who parent);
          raise Not_found
        end;
        let isfst = ref true in
        (* Two methods that override eachother must be compatible on all 
         * arguments, except the first one. But even the first one must be of 
         * the same kind *)
(*
        ignore (E.log "Found override of %s\n" pvi.vname);
*)
        markCompatibleTypes who parent loc rt1 rt2 
          (N.ESameKind N.EEK_trustedCast);
        List.iter2 
          (fun (_, at1, _) (_, at2, _) -> 
            markCompatibleTypes who parent loc at1 at2 
              (if !isfst then (N.ESameKind N.EEK_trustedCast)
               else (N.ECast N.EEK_cxxOverride));
            isfst := false)
          args1 args2

      with Not_found -> ()
  end

  | _ ->  () (* This one does not override anything *)

        
      
  
    
        
(* Scan all the functions and fix the overrides *)
let fixOverrides () = 
  H.iter 
    (fun fname fi -> 
      (* Get the varinfo *)
      let vi = funinfoToVarinfo fi in
      markOverrideFunctionType vi.vname vi.vdecl vi.vtype)
    MU.allFunctions


let fixFunctionPointerVar (vi: varinfo) (loc: location) =
  match vi.vtype with 
    TPtr(((TFun _) as tfun), _) -> 
      markOverrideFunctionType vi.vname loc tfun
  | _ -> ()
