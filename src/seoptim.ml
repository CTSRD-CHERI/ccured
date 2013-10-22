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

(* An optimizer based on symbolic evaluation (to account for simple
 * assignments) *)
open Cil
open Pretty
open Clist

module E = Errormsg
module H = Hashtbl
module CC = Curechecks
module N = Ptrnode

let debug = false


(* A list of functions to be forcefully removed from the file. This only work
 * for functions that return void *)
let forcefullyRemove : string list ref = ref []
let forcefullyRemoveAll : bool ref = ref false


(** This function is called for a CHECK_... function name. *)
let mustDrop (n: string) =
  !forcefullyRemoveAll ||
   (List.exists (fun x -> x = n) !forcefullyRemove)
(*
  (!forcefullyRemove <> [] &&
   not (List.exists (fun x -> x = n) !forcefullyRemove))
*)
(* Keep some stats: seen and eliminated *)
let seen : (string, int ref * int ref) H.t = H.create 29

let keepOne (name: string) =
  try
    let s, _ = H.find seen name in
    incr s
  with Not_found -> H.add seen name (ref 1, ref 0)

let elimOne (name: string) =
  if debug then
    ignore (E.log "Dropping %s at %t\n" name d_thisloc);
  try
    let s, e = H.find seen name in
    incr s; incr e
  with Not_found -> H.add seen name (ref 1, ref 1)


(* The checks that we have seen. Indexed by the name of the check and the
 * list of arguments. The data is an indication of whether any argument
 * depends on memory  *)
let checks : (string * exp list, bool) H.t = H.create 29

let resetChecks () = H.clear checks


(* Register file. Maps identifiers of local variables to expressions. We also
 * remember if the expression depends on memory or depends on variables that
 * depend on memory *)
let regFile : (int, exp * bool) H.t = H.create 29

let resetRegisterFile () = H.clear regFile

let setRegister (id: int) (v: exp * bool) : unit =
  H.remove regFile id;
  H.add regFile id v

let setMemory () =
  (* Get a list of all mappings that depend on memory *)
  let depids = ref [] in
  H.iter (fun id v -> if snd v then depids := id :: !depids) regFile;
  (* And remove them from the register file *)
  List.iter (fun id -> H.remove regFile id) !depids;

  (* Do the same thing for the checks *)
  let depkeys = ref [] in
  H.iter (fun key v -> if v then depkeys := key :: !depkeys) checks;
  List.iter (fun key -> H.remove checks key) !depkeys


let dependsOnMem = ref false

(* can the contents of this variable be affected by a memory write? *)
let varDependsOnMem v: bool =
  v.vglob  (* FIXME: we don't track which global vars have their addresses
              taken, but we should so we don't have to be so conservative
              here. *)
  || (match N.nodeOfAttrlist v.vattr with
        Some n when N.hasFlag n N.pkStack ->
          if debug then
            ignore (E.log "%s depends on memory because its addr escaped.\n"
                      v.vname);
          true
      | _ -> false)


  (* Rewrite an expression based on the current register file *)
class rewriteExpClass : cilVisitor = object
  inherit nopCilVisitor

  method vexpr = function
    | Lval (Var v, NoOffset) -> begin
        if varDependsOnMem v then dependsOnMem := true;
        try
          let defined = H.find regFile v.vid in
          if (snd defined) then dependsOnMem := true;
          ChangeTo (fst defined)
        with Not_found -> DoChildren
    end

    | Lval (Var v, _) ->
        if varDependsOnMem v then dependsOnMem := true;
        DoChildren

    | Lval (Mem _, _) -> dependsOnMem := true; DoChildren

    | _ -> DoChildren


end

let rewriteVisitor = new rewriteExpClass

(* Rewrite an expression and return the new expression along with an
 * indication of whether it depends on memory *)
let rewriteExp (e: exp) : exp * bool =
  dependsOnMem := false;
  let e' = visitCilExpr rewriteVisitor e in
  e', !dependsOnMem

(** Convert expressions into a weighted sum. The weights are all integers and
 * the expressions they are applied have no casts. We compare expressions
 * based on their address, except for special cases. The first integer is a
 * constant. *)
type weightedSum = int * (int * exp) list

let d_weighted () ((c, sum) : weightedSum) : doc =
  let c' = if c <> 0 then num c else nil in
  let d_one (f, e) =
    (if f = 1 then nil else num f ++ text "*") ++ d_exp () e in
  let sum' = docList ~sep:(chr '+') d_one () sum in
  let sep = if c' != nil && sum != [] then text "+" else nil in
  c' ++ sep ++ sum'

let weightedToExp ((c, sum) : weightedSum) : exp =
  if sum = [] then
    integer c
  else
    let mkAdd (e1: exp) (e2: exp) =
      if isZero e1 then e2 else
      BinOp(PlusA, e1, mkCast e2 !upointType, !upointType)
    in
    let rec doSum (acc: exp) = function
        [] -> acc
      | (1, e) :: rest -> doSum (mkAdd acc e) rest
      | (-1, e) :: rest ->
          doSum (BinOp(MinusA, acc, mkCast e !upointType, !upointType)) rest
      | (f, e) :: rest ->
          doSum (mkAdd acc (BinOp(Mult, integer f, mkCast e !upointType,
                                  !upointType))) rest
    in
    doSum (integer c) sum

(* Compare two expressions *)
let sameExp (e1: exp) (e2: exp) =
  if e1 == e2 then true else
  begin
    match e1, e2 with
      Const(CInt64(i1, _, _)), Const(CInt64(i2, _, _)) -> i1 = i2
    | StartOf (Var v1, NoOffset), StartOf (Var v2, NoOffset) -> v1 == v2
    | AddrOf (Var v1, NoOffset), AddrOf (Var v2, NoOffset) -> v1 == v2
    | _, _ -> false
  end


(* Add something to a weighted sum *)
let rec addToWeightedSum (sum: weightedSum) (f: int) (e: exp) : weightedSum =
  let rec loop rest =
    match rest with
      [] -> [(f, e)]
    | (f', e') :: rest' when sameExp e e' ->
        let f'' = f + f' in
        if f'' <> 0 then (f'', e') :: rest' else rest'

    | (f', e') :: rest' -> (f', e') :: loop rest'
  in
  let c, rest = sum in
  c, loop rest

(* Add a constant to a weighted sum *)
let addConstantToWeightedSum (sum: weightedSum) (c: int) : weightedSum =
  let c', rest' = sum in
  c + c', rest'

(* Add two weighted sums: s1 + factor * s2 *)
let rec addWeightedSums (s1: weightedSum)
                        (factor: int) (s2: weightedSum): weightedSum =
  let c1, l1 = s1 in
  let c2, l2 = s2 in
  (* Recurse over l2 *)
  let rec loop = function
      [] -> (c1 + factor * c2, l1)
    | (f', e') :: rest1 ->
        addToWeightedSum (loop rest1) (factor * f') e'
  in
  loop l2

(* Convert an expression to a weighted sum *)
let rec e2w (acc: weightedSum) (factor: int) (e: exp) =
  try
    (* Find the scaling factor for a pointer *)
    let pointerScale (t: typ) =
      match unrollType t with
        TPtr(t, _) -> (7 + bitsSizeOf t) / 8
      | _ -> E.s (bug "e2w: pointerScale")
    in
    match e with
      CastE(_, e) -> e2w acc factor e (* Ignore casts *)
    | Const(CInt64(i, _, _)) ->
        addConstantToWeightedSum acc (factor * (Int64.to_int i))
    | SizeOf t ->
        addConstantToWeightedSum acc (factor * (7 + bitsSizeOf t) / 8)
    | SizeOfE e ->
        addConstantToWeightedSum acc (factor * (7 + bitsSizeOf (typeOf e)) / 8)
    | BinOp(PlusA, e1, e2, _) ->
        e2w (e2w acc factor e1) factor e2
    | BinOp(MinusA, e1, e2, _) ->
        e2w (e2w acc factor e1) (- factor) e2
    | BinOp((PlusPI|IndexPI), e1, e2, t) ->
        let sz = pointerScale t in
        e2w (e2w acc factor e1) (factor * sz) e2
    | BinOp((MinusPI), e1, e2, t) ->
        let sz = pointerScale t in
        e2w (e2w acc factor e1) ((- factor) * sz) e2

    | AddrOf (b, off) ->
        let baseaddr = (* Find the base address *)
          match b with
            Var v -> AddrOf (Var v, NoOffset)
          | Mem addr -> addr
        in
        (* Now we have addr + offset *)
        let btype =
          match typeOf baseaddr with
            TPtr(bt, _) -> bt
          | _ -> E.s (bug "expToWeighed: addrOf")
        in
        let rec offsetToWeighted (acc: weightedSum)
                                (factor: int)
                                (bt: typ) (off: offset) : weightedSum =
          match off with
            NoOffset -> acc
          | Field(fi, off') ->
              let fieldoff, _ = bitsOffset bt (Field(fi, NoOffset)) in
              offsetToWeighted
                (addConstantToWeightedSum acc (factor * (fieldoff / 8)))
                factor fi.ftype off'

          | Index(idx, off') ->
              (* Find the new base type *)
              let bt' =
                match unrollType btype with
                  TArray(bt, _, _) -> bt
                | _ -> E.s (bug "expToWeighed: Index")
              in
              let scale = (7 + bitsSizeOf bt') / 8 in
              offsetToWeighted (e2w acc (factor * scale) idx) factor bt' off'
        in
        offsetToWeighted (e2w acc factor baseaddr) factor btype off


    | StartOf lv ->
        e2w acc factor (AddrOf (addOffsetLval (Index(zero, NoOffset)) lv))

    | _ -> addToWeightedSum acc factor e

  with _ -> addToWeightedSum acc factor e


(* Compare a weighted with 0 *)
let weighted_z ((c, sum): weightedSum) = c = 0 && sum = []

let isConstant (c, sum) = sum = []

let expToWeighted (e: exp) = e2w (0, []) 1 e

(*** For each kind of check we have a class of checks that are relevant ***)

let optimOneCheck (which: varinfo) (* CHECK_... *)
                  (args: exp list)
                  (l: location) : instr clist option =
  match which.vname, args with
    "CHECK_BOUNDSNULL", [b; e; p; plen] -> begin
      let bw = expToWeighted b in
      let ew = expToWeighted e in
      let pw = expToWeighted p in
      let plenw = expToWeighted plen in
      (* Get p - b *)
      let p_b = addWeightedSums pw (-1) bw in
      (* Get e - pLen - b *)
      let e_pLen_b = addWeightedSums ew (-1) (addWeightedSums plenw 1 bw) in
      (* If the latter is a constant then we optimize *)
      ignore (E.log "Call to BOUNDSNULL:\n\tp_b=%a\n\te_plen_b=%a\n"
                d_weighted p_b d_weighted e_pLen_b);
      match e_pLen_b, p_b with
        (c, []), (0, [(f, e)]) ->
          Some (single (Call(None, Lval(Var CC.checkGeuFun.svar, NoOffset),
                             [ integer (c / f); mkCast e !upointType ], l)))
      | (c, []), _ ->
          Some (single (Call(None, Lval(Var CC.checkGeuFun.svar, NoOffset),
                             [ weightedToExp e_pLen_b;
                               weightedToExp p_b ], l) ))
      | _ -> None
    end

  | _ -> None


let doOneInstr (acc: instr clist) (i: instr) : instr clist =
  match i with
  | Set ((Var v, NoOffset), e, _) ->
      setRegister v.vid (rewriteExp e);
      if varDependsOnMem v then   (* e.g. a write to a global variable *)
        setMemory ();
      CConsR (acc, i)

  | Set ((Var v, _), e, _) ->
      if varDependsOnMem v then   (* e.g. a write to a global variable *)
        setMemory ();
      CConsR (acc, i)

  | Set ((Mem _, _), _, _) ->
      setMemory ();
      CConsR (acc, i)


  | Call (None, Lval(Var check, NoOffset), args, l)
      when (String.length check.vname >= 6 &&
            String.sub check.vname 0 6 = "CHECK_")
    ->
      currentLoc := l;
      let keepIt =
        if mustDrop check.vname then
          false
        else begin
          if debug then ignore (E.log "Looking at call to %s\n" check.vname);
          (* Rewrite the arguments *)
          let dependsOnMem = ref false in
          let args' = List.fold_right
              (fun a acc ->
                let a', dm = rewriteExp a in
                if dm then dependsOnMem := true;
                a' :: acc) args []
          in
          if H.mem checks (check.vname, args') then
            false
          else begin
            H.add checks (check.vname, args') !dependsOnMem;
            true
          end
        end
      in
      if keepIt then begin
        keepOne check.vname;
(*        match optimOneCheck check args l with
          None -> CConsR (acc, i)
        | Some il -> append acc il
*)
        CConsR (acc, i)
      end else begin
        elimOne check.vname;
        acc
      end

  | Call (ret, _, _, _) -> begin
      (match ret with
         Some(Var v, _) -> H.remove regFile v.vid
       | _ -> ());

      (* The call could clobber any memory value. *)
      setMemory ();
      CConsR (acc, i)
    end

  | i -> CConsR (acc, i)


class basicBlockOptimClass : cilVisitor = object
    inherit nopCilVisitor

    method vstmt (s: stmt) =
      match s.skind with
        Instr il ->
          resetRegisterFile (); resetChecks ();
          let il' = toList (List.fold_left doOneInstr empty il) in
          resetRegisterFile (); resetChecks (); (* To make the GC happy *)
          s.skind <- Instr il';
          SkipChildren

      | _ -> DoChildren

  method vexpr _ = SkipChildren
  method vtype _ = SkipChildren
end

let basicBlockOptim = new basicBlockOptimClass

let optim (f: file) : file =
  H.clear seen;
  Stats.time "seoptim" (visitCilFileSameGlobals basicBlockOptim) f;
  if true || !E.verboseFlag then begin
    let totalChecks = ref 0 in
    let elimChecks  = ref 0 in
    ignore (E.log "Symbolic execution-based optimizer statistics :@!") ;
    H.iter (fun name (seen, elim) ->
      totalChecks := !totalChecks + !seen;
      elimChecks := !elimChecks + !elim;
      ignore (E.log "  %-30s seen %d, eliminated %d (%6.2f%%)\n"
                name !seen !elim
                (100.0 *. (float_of_int !elim) /. (float_of_int !seen)));
      ) seen;
      ignore (E.log "  %-30s seen %d, eliminated %d (%6.2f%%)\n"
                "Total" !totalChecks !elimChecks
                (100.0 *. (float_of_int !elimChecks)
                   /. (float_of_int !totalChecks)));
  end;
  f
