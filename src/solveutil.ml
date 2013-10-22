(*
 *
 * Copyright (c) 2001-2002,
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
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

(*
 * A set of solver utilities and wrappers.
 *
 * This includes implementations of "type_congruent" and "subtype", as well
 * as solver-wrappers.
 *)
open Cil
open Ptrnode
open Pretty
open Trace
module E = Errormsg

(* Check that p is a prefix of s *)
let prefix p s =
  let lp = String.length p in
  let ls = String.length s in
  lp <= ls && String.sub s 0 lp = p

let safe_voidstar = false

(* Apply a function to all successors and predecessors in the graph. But
 * ignore EPointsTo edges. *)
let rec depth_first_bidir
    (f: node -> bool) (* Says whether we need to recurse *)
    (n: node) =
  if f n then begin
    List.iter (fun e ->
                 if e.ekind <> EPointsTo &&
                    e.ekind <> EArgs then depth_first_bidir f e.eto)
      n.succ;
    List.iter (fun e ->
                 if e.ekind <> EPointsTo &&
                    e.ekind <> EArgs then  depth_first_bidir f e.efrom)
      n.pred;
  end



(* set of functions to tag *)
let wild_solve_tag_these_functions : (string,bool) Hashtbl.t = (Hashtbl.create 17)

(* This "solver" turns almost all nodes WILD *)
let wild_solve (node_ht : (int,node) Hashtbl.t) = begin
  (* called when we're considering whether to tag a global function; *)
  (* if the function definitely should be tagged, this sets the node *)
  (* to Wild and throws Not_found *)
  let checkFunc (funcName: string) (n: node) : unit =
  begin
    (*(trace "tagFuncs" (dprintf "considering forcing %s to be tagged\n" funcName));*)
    if (Hashtbl.mem wild_solve_tag_these_functions funcName) then begin
      (trace "tagFuncs" (dprintf "forcing %s to be tagged\n" funcName));
      n.kind <- Wild;           (* tag this function *)
      n.why_kind <- UserSpec;   (* say the user made us do it *)
      raise Not_found;          (* avoid the "Default" kind we otherwise get *)
    end
    (* matth: don't tag main, even if wild_solve_tag_all_functions is true *)
    else if funcName = !Globinit.mainname then begin
      (trace "tagFuncs"
	 (dprintf "entrypoint %s will not be tagged.\n" funcName));
      n.kind <- Safe;
      n.why_kind <- Special("Main function not tagged.",n.loc);
      raise Not_found
    end
  end in

  (* for every node.. *)
  Hashtbl.iter (fun id n ->
    try (* Raise Not_found if we cannot make it Wild. We leave it alone then *)
      if n.kind = ROString then raise Not_found;

      (* matth:  The arguments to main must be thin.  This attribute
       *   is set in Markptr.fixupMain.  *)
      if n.kind = Safe && hasAttribute "main_input" n.attr then
	raise Not_found;

      (* Make the return type of stringof to be Safe *)
      (match n.where with
        PGlob stringof, 1 when Poly.stripPoly stringof = "__stringof"
                          || Poly.stripPoly stringof = "__stringof_ornull" ->
          n.kind <- Safe;
          raise Not_found

      | _ -> ());

      (* Do not make WILD those functions that are not cast and are not used
       * without prototype; exceptions:
       *   - untagged_functions forces them all untagged
       *   - tag_all_functions forces them all to be tagged *)
      if (match unrollType n.btype with TFun _ -> true | _ -> false) &&
         (* Only functions, not functions embedded in pointers *)
         (match n.where with
             PGlob funcName, 0 ->
               (checkFunc funcName n);
               (trace "tagFuncs" (dprintf "not tagging %s\n" funcName));
               true
           | PStatic _, 0 -> true
           | _ -> false) then begin
        (* we're considering whether to tag a function *)
        (* are we forcing them all tagged? *)
        if !wild_solve_tag_all_functions then begin
          (* don't throw an exception *)
        end
        else begin
          (* was it only used safely? *)
          let onlyEPointsToOrEArgsEdges (el: edge list) =
            List.for_all (fun e -> e.ekind = EPointsTo ||
                                   e.ekind = EArgs) el
          in
          if (not (hasFlag n pkNoPrototype)
             && onlyEPointsToOrEArgsEdges n.succ
             && onlyEPointsToOrEArgsEdges n.pred) then
            begin
              n.kind <- Safe;
              n.why_kind <- Default;
              raise Not_found
            end;
          (* sm: or, are we in the mode where functions are never tagged? *)
          if !wild_solve_untagged_functions then begin
            (*(trace "sm" (dprintf "avoiding tagging a function\n"));*)
            n.kind <- Safe;
            n.why_kind <- Special("WILD solver untagged function",locUnknown);
            raise Not_found
          end;
        end;
      end;

      (* Do not make WILD the va_lists *)
      (match unrollType n.btype with
        TComp(ci, _)
          when ci.cstruct && prefix "__ccured_va_list" ci.cname ->
            n.kind <- Safe; n.why_kind <- Default; raise Not_found
      | _ -> ());
      (* Do not make WILD the return value of ccured_va_arg *)
      (match n.where with
        PGlob("__ccured_va_arg"), 1 ->
          n.kind <- Safe; n.why_kind <- Default; raise Not_found
      | _ -> ());
      n.kind <- Wild ;
      n.why_kind <- Default
    with Not_found -> ()) node_ht;

  (* Now scan one more time and make sure that we turn all predecessors and
   * successors of SAFE nodes into SAFE nodes *)
  Hashtbl.iter
    (fun id n ->
      if n.kind = Safe then begin
        n.kind <- Wild; (* To ensure that we recurse *)
        depth_first_bidir
          (fun n' ->
            if n'.kind <> Safe && n'.kind <> ROString then
              begin  n'.kind <- Safe; n'.why_kind <- Default; true end
            else false) n
      end)
    node_ht;

  false

end

(* This solver-wrapper should be run after another actual solver. It makes
 * everything either WILD or SAFE (or ROSTRING). *)
let wild_safe_solve (node_ht : (int,node) Hashtbl.t) = begin
  Hashtbl.iter (fun id n ->
    if n.kind <> Safe &&
      (n.kind <> ROString || n.why_kind <> PrintfArg) then begin
      n.kind <- Wild
    end
  ) node_ht ;
  false
end



(* read a file containing names of functions to tag, storing the *)
(* names in the wild_solve_tag_these_functions hash table *)
let readTagFunctionFile (fname: string) : unit =
begin
  (* open the file *)
  (trace "sm" (dprintf "opening tag file %s\n" fname));
  let channel: in_channel = (open_in fname) in
  try
    (* read each line until EOF *)
    while true do
      let line: string = (input_line channel) in
      (trace "sm" (dprintf "read %s from tag file\n" line));
      (* store it in hashtable *)
      (Hashtbl.add wild_solve_tag_these_functions line true);
    done
  with End_of_file -> ();
  (trace "sm" (dprintf "finished reading tag file %s\n" fname));
end
