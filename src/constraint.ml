(*
 * Copyright (c) 2001-2002,
 *  Aman Bhargava
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
 * Aman's constraint representation and solver
 * Intended for use for array bounds checking elimination
 *)

let debug = false
let showsolution = true

(******************************************************************************)
(* Types *)

type limit =
  | Int of int
  | Sym of string
  | NegInfinity
  | Infinity

type t =
  | LT of  limit * limit
  | LTE of limit * limit

type set = t list

let set_contains = List.mem
let set_fold_right = List.fold_right
let set_fold_left = List.fold_left



(******************************************************************************)
(* Functions *)

let mk a op b =
  match op with
  | "<" -> LT (a,b)
  | ">" -> LT (b,a)
  | "<=" -> LTE (a,b)
  | ">=" -> LTE (b,a)
  | _ -> failwith "Don't know how to make this constraint"

let lim_tostring = function
  | Int n -> string_of_int n
  | Sym  s -> (* "'" ^ *) s
  | NegInfinity -> "-INF"
  | Infinity -> "INF"

let tostring = function
  | LT (a,b) -> (lim_tostring a) ^ " < " ^ (lim_tostring b)
  | LTE (a,b) -> (lim_tostring a) ^ " <= " ^ (lim_tostring b)


let pr = Printf.printf;

(******************************************************************************)
(* Solvers *)

(* Fringe:
   We maintain a memoized set of theorems that are being worked on or
   are already proved or disproved
*)
type fringe_t = {fval : t; mutable fsolution : bool option}
let fringe : fringe_t list ref = ref []

let fringe_contains (x : t) =
  List.exists (fun a -> a.fval = x) !fringe

let fringe_find (x : t) =
  List.find (fun a -> a.fval = x) !fringe

let fringe_add (x : t) : fringe_t =
  let fr = {fval=x; fsolution=None} in
  fringe := fr :: !fringe;
  fr

(* The constraints and all the limit values for a given run of the solver *)
let slimits : limit list ref = ref []

(* Initialize the fringe and the values for one run of the solver *)
let initSolver constraints =
  fringe := [];
  slimits := [Infinity;NegInfinity];
  let add_to_slimits lim =
    if not (List.mem lim !slimits) then
      match lim with
      | (Sym _) as lim -> slimits := lim :: !slimits
      | (Int _) as lim -> slimits := lim :: !slimits
      | _ -> ()
  in
  List.iter (function c ->
    fringe := {fval=c; fsolution=Some true} :: !fringe;
    match c with
    | LT (a,b) -> add_to_slimits a; add_to_slimits b;
    | LTE (a,b) ->add_to_slimits a; add_to_slimits b;)
    constraints


(* Try to prove a less-than relation *)
let rec rsolveLT (ca : limit) (cb : limit) : bool =
  match ca, cb with
  | NegInfinity, _ -> cb != NegInfinity
  | _, NegInfinity -> false
  | _, Infinity -> ca != Infinity
  | Infinity, _ -> false
  | Int ia, Int ib -> ia < ib
  | _,_ ->
      let lt = (LT (ca,cb)) in
      try match fringe_find lt with
      | {fsolution = None} as fr -> fr.fsolution <- Some false; false
      | {fsolution = Some sol}   -> sol
      with _ ->
	let fr = fringe_add lt in
	let sol =
	  List.exists
	    (fun lim ->
	      ((rsolveLT ca lim) && (rsolveLTE lim cb)) ||
	      ((rsolveLTE ca lim) && (rsolveLT lim cb)))
	    !slimits
	in
	fr.fsolution <- Some sol;
	if debug then Printf.printf "Solve %s = %b\n"  (tostring lt) sol;
	sol


(* Try to prove an equal-to relation *)
and rsolveEQ (ca : limit) (cb : limit) : bool =
  (rsolveLTE ca cb &&
  rsolveLTE cb ca)

(* Try to prove a less-than-or-equal relation *)
and rsolveLTE (ca : limit) (cb : limit) : bool =
  match ca, cb with
  | NegInfinity, _ -> cb != NegInfinity
  | _, NegInfinity -> false
  | _, Infinity -> ca != Infinity
  | Infinity, _ -> false
  | Int ia, Int ib -> ia <= ib
  | _,_ ->
      let lt = (LTE (ca,cb)) in
      try match fringe_find lt with
      | {fsolution = None} as fr -> fr.fsolution <- Some false; false
      | {fsolution = Some sol}   -> sol
      with _ ->
	let fr = fringe_add lt in
	let sol =
	  rsolveLT ca cb ||
	  ca = cb ||
	  List.exists
	    (fun lim ->
	      ((rsolveEQ ca lim) && (rsolveLTE lim cb)) ||
	      ((rsolveEQ cb lim) && (rsolveLTE ca lim)))
	    !slimits
	in
	fr.fsolution <- Some sol;
	if debug then Printf.printf "Solve %s = %b\n"  (tostring lt) sol;
	sol



(* Invoke the solver. Try to prove a theorem with the given constraints *)
let solve constraints theorem =
  initSolver constraints;
  let ret =
    match theorem with
    | LT  (a,b) -> rsolveLT  a b
    | LTE (a,b) -> rsolveLTE a b
  in
  if debug || showsolution then begin
    Printf.printf "(solve) %s \t= %b\n" (tostring theorem) ret;
    flush stdout
  end;
  ret

(* Solve a == b *)
let solveEQ constraints a b =
  initSolver constraints;
  let ret =
    (rsolveLTE a b) && (rsolveLTE b a)
  in
  if debug || showsolution then begin
    Printf.printf "(solve) %s == %s \t= %b\n" (lim_tostring a) (lim_tostring b) ret;
    flush stdout
  end;
  ret



(******************************************************************************)
(* Test *)

let test () =
  let constraints = [
    mk (Sym "b") "<" (Int 10);
    mk (Sym "b") ">" (Int 8);
    mk (Sym "a") ">" (Int 3);
    mk (Sym "a") "<" (Int 7);
    mk (Sym "x") "<=" (Sym "a");
    mk (Sym "x") ">=" (Sym "a");
    mk (Sym "x") "<=" (Sym "y");
    mk (Sym "x") ">=" (Sym "y");
  ] in
  pr "Constraints:\n";
  List.iter (fun c -> pr "%s\n" (tostring c)) constraints;
  flush stdout;
  ignore (solve constraints (mk (Sym "a") "<" (Int 8)));
  ignore (solve constraints (mk (Sym "b") ">=" (Int 8)));
  ignore (solve constraints (mk (Sym "a") "<" (Sym "b")));
  ignore (solve constraints (mk (Sym "a") "<=" (Sym "b")));
  ignore (solve constraints (mk (Sym "a") ">" (Sym "b")));
  ignore (solve constraints (mk (Sym "a") ">=" (Sym "b")));
  ignore (solveEQ constraints (Sym "a") (Sym "y"));
  pr "s/a/y/g\n";
  ignore (solve constraints (mk (Sym "y") "<" (Int 8)));
  ignore (solve constraints (mk (Sym "b") ">=" (Int 8)));
  ignore (solve constraints (mk (Sym "y") "<" (Sym "b")));
  ignore (solve constraints (mk (Sym "y") "<=" (Sym "b")));
  ignore (solve constraints (mk (Sym "y") ">" (Sym "b")));
  ignore (solve constraints (mk (Sym "y") ">=" (Sym "b")));
  ignore (solveEQ constraints (Sym "y") (Sym "y"));
  pr "Limits known: ";
  List.iter (fun a -> pr "%s " (lim_tostring a)) !slimits;
  pr "\nMemoization buffer: size = %d\n" (List.length !fringe);
(*
  List.iter (fun a -> pr "(memo) %s \t= %s\n"
      (tostring a.fval)
      (match a.fsolution with None -> "?" | Some true -> "true" | _ -> "false"))
    !fringe;
*)
  ()


;; test () ;;
