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
open Clist

module E = Errormsg
module H = Hashtbl

(* An optimizer based on
 * (1) Symbol Evaluation
 * (2) knowing what the some of the checks are actually doing.
 *
 * For example, the check in:
 *
 *    char array[512];
 *    // CHECK_BOUNDS(base, base_end, pointer, read_size)
 *    CHECK_BOUNDS(array, array + 512, &array[128], 1)
 *
 * Can be eliminated since:
 *  array <= &array[128]  _AND_  &array[128] + 1 <= array + 512
 *)
let debug = false

(* Structural equality testing that won't loop forever on CIL expressions: *)
let (=?) = Util.equals

(* Keep some stats: seen and eliminated *)
let seen : (string, int ref * int ref) H.t = H.create 29

let keepOne (name: string) =
  try
    let s, _ = H.find seen name in
    incr s
  with Not_found -> H.add seen name (ref 1, ref 0)

let elimOne (name: string) =
  if debug then
    ignore (E.log "CheckOptim is dropping %s at %t@!" name d_thisloc);
  try
    let s, e = H.find seen name in
    incr s; incr e
  with Not_found -> H.add seen name (ref 1, ref 1)

(*
 * Symbolic Evaluation
 *)
let boolify b = if b then one else zero

let type_under_pointer tau = match unrollType tau with
	| TPtr(under_tau,_) -> under_tau
	| _ -> failwith "eval: type_under_pointer of non-pointer"

(* Evaluate expressions with special handling for 64-bit integer values *)

let base_address = ref zero

let rec eval_exp exp s =
  (* E.warn "eval_exp %a" d_exp exp ;  *)
  let result =
    match exp with
      Const(c) -> exp
    | Lval(l) -> eval_lval l s
    | SizeOf(TVoid _) -> one
    | SizeOf(t) -> eval_exp (sizeOf t) s
    | SizeOfE(e) -> eval_exp (sizeOf (typeOf e)) s
    | SizeOfStr str -> eval_exp (integer (1 + String.length str)) s
    | AlignOf(t) -> failwith "eval_exp: alignof"
    | AlignOfE(e) -> failwith "eval_exp: alignof"
    | UnOp(op,e1,t) -> begin
	let ev1 = eval_exp e1 s in
	match op,ev1 with
	  Neg,Const(CInt64(i,ik,so)) -> Const(CInt64(Int64.neg i,ik,so))
	| BNot,Const(CInt64(i,ik,so)) -> Const(CInt64(Int64.lognot i,ik,so))
	| LNot,Const(CInt64(i,ik,so)) -> boolify (i = Int64.zero)
	| _,_ -> UnOp(op,ev1,t)
    end
    | BinOp(PlusPI,e1,e2,t)
    | BinOp(IndexPI,e1,e2,t) ->
	let under_tau = type_under_pointer (typeOf e1) in
	let mult_factor = BinOp(Mult,e2,sizeOf under_tau,voidType) in
	eval_exp (BinOp(PlusA,e1,mult_factor,t)) s
    | BinOp(MinusPI,e1,e2,t) ->
	let under_tau = type_under_pointer (typeOf e1) in
	let mult_factor = BinOp(Mult,e2,sizeOf under_tau,voidType) in
	eval_exp (BinOp(MinusA,e1,mult_factor,t)) s
    | BinOp(op,e1,e2,t) -> begin
	let ev1 = eval_exp e1 s in
	let ev2 = eval_exp e2 s in
	try begin
	  let i,ik,j,jk = match ev1,ev2 with
	    Const(CInt64(i,ik,so)), Const(CInt64(j,jk,so')) -> i,ik,j,jk
	  | _ -> failwith "not an int"
	  in
	  match op with
	    PlusA   (* arithemtic + *) -> Const(CInt64(Int64.add i j,ik,None))
	  | PlusPI  (* pointer + integer *)
	  | IndexPI -> failwith "eval: pointer + integer"
	  | MinusA
	  | MinusPP -> Const(CInt64(Int64.sub i j,ik,None))
	  | MinusPI -> failwith "eval: pointer - integer"
	  | Mult -> Const(CInt64(Int64.mul i j,ik,None))
	  | Div -> Const(CInt64(Int64.div i j,ik,None))
	  | Mod -> Const(CInt64(Int64.rem i j,ik,None))
	  | Shiftlt ->
              Const(CInt64(Int64.shift_left i (Int64.to_int j),ik,None))
	  | Shiftrt ->
              Const(CInt64(Int64.shift_right i (Int64.to_int j),ik,None))
	  | Lt -> boolify (i < j)
	  | Gt -> boolify (i > j)
	  | Le -> boolify (i <= j)
	  | Ge -> boolify (i >= j)
	  | Eq -> boolify (i = j)
	  | Ne -> boolify (i <> j)
	  | BAnd | LAnd -> Const(CInt64(Int64.logand i j,ik,None))
	  | BXor -> Const(CInt64(Int64.logxor i j,ik,None))
	  | BOr | LOr -> Const(CInt64(Int64.logor i j,ik,None))
	end
	with Failure _ ->
	  BinOp(op,ev1,ev2,t)
    end
    | Question(p,e1,e2,t) -> begin
      let pv = eval_exp p s in
      match pv with
        Const(CInt64(0L,_,_))
      | Const(CReal(0.0,_,_))
      | Const(CChr('\000')) -> eval_exp e2 s
      | Const(CInt64(_,_,_))
      | Const(CReal(_,_,_))
      | Const(CChr(_)) -> eval_exp e1 s
      | Const(CEnum(pe,_,_)) -> eval_exp (Question(pe,e1,e2,t)) s
      | _ -> Question(pv,e1,e2,t)
    end
    | CastE(t,e) -> eval_exp e s
    | AddrOf(lv) -> let (addr,tau) = lval_denotes lv s in addr
    | AddrOfLabel(_) -> failwith "eval_exp: addrOfLabel"
    | StartOf(l) -> eval_lval l s
  in
  if result =? !base_address then zero else result
and eval_lval lv s = Lval(lv)
and base_type_of_array_type tau = match tau with
  TArray(base_type,_,_) -> base_type
| _ -> failwith "base_type_of_array_type: not an array"
and lval_denotes (lb,lo) s =
  let rec offset_fun lo = match lo with
    NoOffset -> (fun (addr,tau) -> (addr,tau))
  | Field(f,off) -> (fun (addr,tau) ->
      let startbits, widthbits =
        bitsOffset (TComp(f.fcomp,[])) (Field(f,NoOffset)) in
      let disp = kinteger IInt (startbits / 8) in
      let this_result = BinOp(PlusA,addr,disp,voidType) in
      (offset_fun off) (this_result, f.ftype))
  | Index(e,off) -> (fun (addr,tau) ->
      let element_type = base_type_of_array_type tau in
      let size_exp = sizeOf element_type in
      let e' = eval_exp e s in
      let disp = BinOp(Mult,e',size_exp,voidType) in
      let this_result = BinOp(PlusA,addr,disp,voidType) in
      (offset_fun off) (this_result,element_type))
  and lbase_fun lb = match lb with
  | Var(vi) when Lval(lb, NoOffset) =? !base_address ->
      (zero, vi.vtype)
  | Var(vi) -> (AddrOf((lb,NoOffset)), (vi.vtype))
  | Mem(e) ->
      let tau = typeOfLval (lb,NoOffset) in
      let e' = eval_exp e s in
      (e',tau)
  in
  let (addr,tau) = (offset_fun lo) (lbase_fun lb) in
  (addr,tau)

    (* Can we verify that the given expression will always evaluate to 1? *)
let can_we_prove exp =
  try
    let result = eval_exp exp () in
    result = one
  with Failure _ ->
    false

      (* Currently we handle three kinds of checks. *)
let doOneInstr (acc : instr clist) (i : instr) : instr clist =
  match i with
  | Call(None,Lval(Var check, NoOffset), [base; bend; p], loc) when
    check.vname = "CHECK_SEQ2FSEQ" -> begin
      (* if p < base, fail *)
      base_address := zero ;
      base_address := eval_exp base ();
      match can_we_prove (BinOp(Ge,p,base,voidPtrType)) with
        true -> elimOne check.vname ; acc
      | false -> keepOne check.vname ; CConsR (acc, i)
    end

  | Call(None,Lval(Var check, NoOffset), [arg], loc) when
    check.vname = "CHECK_POSITIVE" -> begin
      (* if arg < 0, fail *)
      base_address := zero ;
      match can_we_prove (BinOp(Ge,arg,zero,voidPtrType)) with
        true -> elimOne check.vname ; acc
      | false -> keepOne check.vname ; CConsR (acc, i)
    end

  | Call(None,Lval(Var check, NoOffset), [b; bend; p; plen;
                                           foraccess; noint ],
         loc) when
    check.vname = "CHECK_SEQ2SAFE" -> begin
      (* if p < b, fail
       * if p + plen > bend, fail *)
      base_address := zero ;
      base_address := eval_exp b ();
      let elim_lbound = can_we_prove (BinOp(Le,b,p,voidPtrType)) in
      let right = BinOp(PlusPI,p,plen,voidPtrType) in
      let elim_ubound = can_we_prove (BinOp(Le,right,bend,voidPtrType)) in
      (*
      E.warn "@!Considering (%b %b) %a" elim_lbound elim_ubound
        d_instr i ; flush stdout ; flush stderr;
        *)
      match elim_lbound, elim_ubound with
        true, true -> elimOne check.vname ; acc
      | _, _ -> keepOne check.vname ; CConsR (acc, i)
    end
  | i -> CConsR (acc, i)


class checkOptimClass : cilVisitor = object
  inherit nopCilVisitor
  method vstmt (s: stmt) =
    match s.skind with
      Instr il ->
        let il' = toList (List.fold_left doOneInstr empty il) in
        s.skind <- Instr il' ;
        SkipChildren
    | _ -> DoChildren
  method vexpr _ = SkipChildren
  method vtype _ = SkipChildren
end

let checkOptim = new checkOptimClass

let optim (f: file) : file =
  Stats.time "choptim" (visitCilFileSameGlobals checkOptim) f;
  if true || !E.verboseFlag then begin
    let totalChecks = ref 0 in
    let elimChecks  = ref 0 in
    ignore (E.log "Check-based optimizer statistics :@!") ;
    H.iter (fun name (seen, elim) ->
      totalChecks := !totalChecks + !seen;
      elimChecks := !elimChecks + !elim;
      ignore (E.log "  %-30s seen %d, eliminated %d (%6.2f%%)@!"
                name !seen !elim (100.0 *. (float_of_int !elim) /.
                (float_of_int !seen)));
      ) seen;
      ignore (E.log "  %-30s seen %d, eliminated %d (%6.2f%%)@!"
                "Summary" !totalChecks !elimChecks
                (100.0 *. (float_of_int !elimChecks) /.
                (float_of_int !totalChecks)));
  end;
  f
