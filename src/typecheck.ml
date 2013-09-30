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

(*
 * Type-check a fully annotated CCured program.
 *)

open Ptrnode
open Cil
module E = Errormsg

let bitsSizeOfOpt tau =
  try Some(bitsSizeOf tau)
  with SizeOfError _ -> None

(* Variants of Type.equal and Type.subtype *)
let type_equal ~(compat: chain -> typ -> typ -> unit) ~(t1: typ) ~(t2: typ) = 
  Type.equal 
    ~compat:compat 
    ~failure:(fun _ _ _ -> ())
    ~why_t1_t2:mkRIdent 
    ~t1:t1 
    ~t2:t2

let type_subtype ~(compat: chain -> typ -> typ -> unit) ~(small: typ) ~(big: typ) : bool = 
  Type.subtype 
    ~compat:compat 
    ~failure:(fun _ _ _ -> ())
    ~why_small_big:mkRIdent
    ~small:small
    ~big:big
        
(* For a probably-pointer P, we want to determine:
 *  (a) the Cil.type associated with *P     OPTION
 *  (b) the pointer kind associated with P  (possibly unknown)
 *  (c) the pointer kind associated with &P (possibly unknown)
 *)
let best_of a b = (* favors a *)
  match a,b with
    Unknown,_ -> b
  | _,_ -> a

let rec kind_of_ptr_type t =
  let targ, al = match unrollType t with
    | TPtr(targ,al) -> Some(targ), al
    | TArray(targ,_,al) -> Some(targ), al

    | TFun(_,_,_,al) -> Some(t), al 

    | TVoid(al)
    | TBuiltin_va_list al
    | TInt(_,al)
    | TFloat(_,al)
    | TEnum(_,al)
    | TComp(_,al)
    | TNamed(_,al) -> None, al 
  in 
  let kind, _ = kindOfAttrlist al in 
  let parent_kind = match nodeOfAttrlist al with
    Some(child) -> let parent_opt = Ptrnode.nodeThatPointsTo child in
                   (match parent_opt with
                      Some(parent_node) -> parent_node.kind
                    | None -> Unknown)
  | None -> Unknown
  in 
  (targ, kind, parent_kind)

and kind_of_ptr_exp e =
  match e with
  | UnOp(op,e1,tau) -> kind_of_ptr_type tau
  | BinOp(op,e1,e2,tau) -> kind_of_ptr_type tau
(*  | Question(e1,e2,e3) -> kind_of_ptr_exp e2 *)
  | CastE(tau,e) -> kind_of_ptr_type tau 
  | Lval(lv) -> kind_of_ptr_lval lv 
  | AddrOf(lv) -> 
      let _,_,c = kind_of_ptr_lval lv in
      Some(typeOfLval lv),c,Unknown
  | StartOf(lv) -> kind_of_ptr_lval lv
  | Const(CStr _) -> Some charType,String,Unknown
  | _ -> kind_of_ptr_type (typeOf e)
and kind_of_ptr_lval l = match l with
  | Var(vi),o -> begin
      let kind,_ = kindOfAttrlist vi.vattr in  (* & information *)
      let a,b,c = kind_of_ptr_type vi.vtype in 
      kind_of_ptr_offset o (a,b,(best_of kind c))
      end
  | Mem(e),o -> begin   (* means l = ( *e ).o *)
    let et = typeOf e in 
    let lt = typeOfLval l in
    let  _,eb,ec = kind_of_ptr_type et in
    let la,lb,lc = kind_of_ptr_type lt in
    kind_of_ptr_offset o (la,(best_of lb ec),(best_of eb lc))
    end
and kind_of_ptr_offset o (a,b,c) =
  match o with
  | NoOffset -> (a,b,c)
  | Field(fi,o') -> 
      let a,b,c = kind_of_ptr_type fi.ftype in
      let kind,_ = kindOfAttrlist fi.fattr in
      kind_of_ptr_offset o' (a,b,(best_of kind c))
  | Index(e,o') -> begin
      match a with
        Some(tau) -> let a',b',_ = kind_of_ptr_type tau in 
                     kind_of_ptr_offset o' (a',b',b)
      | None -> kind_of_ptr_offset o' (None,Unknown,Unknown)
      end

(* Check to make sure that the given type (and everything it can point to)
 * is WILD. *)
let typechecked_wild = Hashtbl.create 511  
let rec typecheck_wild_type t =  
  if Hashtbl.mem typechecked_wild t then
    ()
  else begin
    Hashtbl.add typechecked_wild t true ;
    match unrollType t with
      TVoid(al) -> ()
    | TInt(i,al) -> ()
    | TFloat(f,al) -> ()
    | TEnum(e,al) -> ()
    | TPtr(t2,al) -> let kind,why = kindOfAttrlist al in
                     (if kind <> Wild then ignore
                      (warn "typecheck:@?%a should be Wild" d_type t)) ;
                     typecheck_wild_type t2 
    | TComp(ci,al) -> List.iter (fun fi -> typecheck_wild_type fi.ftype)
                          ci.cfields
    | TFun(t,vl,vararg,al) -> 
        typecheck_wild_type t ;
        List.iter (fun (_, vit, _) -> typecheck_wild_type vit) 
          (argsToList vl)
    | TArray(t2,_,al) -> let kind,why = kindOfAttrlist al in
                     (if kind <> Wild then ignore
                      (warn "typecheck:@?%a should be Wild" d_type t)) ;
                     typecheck_wild_type t2 
    | TNamed(_) -> failwith "unrollType"
    | TBuiltin_va_list _ -> failwith "typecheck: va_list"
  end

(* Consistency checking on a type.
 * Right now this just checks that WILD pointers point to WILD things. 
 * other_list is a list of types that should be WILD if the given type
 * is WILD. *)
let typecheck_type tau other_list = 
  match unrollType tau with
    TPtr(t,al) -> let kind,why = kindOfAttrlist al in 
                  if kind = Wild then begin
                    typecheck_wild_type t ;
                    List.iter (fun tau -> typecheck_wild_type tau) other_list
                  end
  | _ -> ()

let typecheck_pointer_arithmetic a b e =
  (* a = pointer, b = integer, e = whole expression *)
  try
    let _, ptr_kind, _ = kind_of_ptr_exp a in
    let okay = 
    match ptr_kind with
    | Safe -> false
    | Seq | SeqN | Ptrnode.Index -> true
    | FSeq | FSeqN | String | ROString -> (* must be positive *)
      begin
      match isInteger (constFold true b) with 
        Some(i) when i >= Int64.zero -> ()
      | Some _ | None -> ignore
          (warn "typecheck:@?not positive arith on %a pointer in %a" 
            d_opointerkind ptr_kind d_exp e)
      end ; true 
    | Wild -> true
    | _ -> false
    in if not okay then ignore
      (warn "typecheck:@?bad arithmetic on %a %a pointer %a in@!%a" 
        d_opointerkind ptr_kind d_type (typeOf a) d_exp a d_exp e)
  with _ -> ignore
      (warn "typecheck:@?no qualifier for %a in %a" 
        d_exp a d_exp e)

(* Consistency checking on a variable declaration.
 * Right now this just checks its type. *)
let typecheck_varinfo vi other_list = typecheck_type vi.vtype other_list

let checking = ref true 

(* Euclid's algorithm for the GCD *)
let rec gcd a b = 
  if a = 0 || b = 0 then 1
  else if b > a then gcd b a 
  else match a mod b with
    0 -> b
  | r -> gcd b r 

(* Make sure casts/assignments work correctly. 
 * 
 *)
let isInterestingType tau =
  isPointerType tau || isFunctionType tau || isArrayType tau

let check_cast (context : Pretty.doc) to_type from_exp = begin
  let from_type = typeOf(from_exp) in 
  if isInterestingType to_type || isInterestingType from_type then 
  try begin
    let to_target, to_kind, _ = kind_of_ptr_type to_type in
    let from_target, from_kind, _ = kind_of_ptr_exp from_exp in 
    let check_compat _ p1 p2 =
      let _,p1kind,_ = kind_of_ptr_type p1 in
      let _,p2kind,_ = kind_of_ptr_type p2 in
      if p1kind <> p2kind then begin
        ignore (warn 
      ("typecheck:@?inner pointer kind mismatch@!%a ptr %a@!%a ptr %a@!%a")
            d_opointerkind p1kind d_type p1
            d_opointerkind p2kind d_type p2
            Pretty.insert context) ;
      end
    in 
    let to_target, from_target = (match to_target, from_target with
      Some(a),Some(b) -> unrollType a,unrollType b
    | Some(a),None    -> unrollType a,(TVoid([]))
    | None,Some(b)    -> (TVoid([])), unrollType b
    | None,None       -> (TVoid([]),TVoid([]))) 
    in 
    (* check a cast from one pointer to another *)
    let okay = 
    Stats.time "typecheck switch" (fun () -> 
    match from_kind, to_kind with
      Safe, Safe ->
        type_subtype ~compat:check_compat ~small:to_target ~big:from_target

    | Safe, Seq 
    | Safe, FSeq ->
        begin
          match bitsSizeOfOpt from_target, bitsSizeOfOpt to_target with
            Some(a),Some(b) when b <> 0 -> 
                let n = (a / b) + 1 in
                type_subtype 
                    ~compat:check_compat 
                    ~small:from_target 
                    ~big:(TArray(to_target, Some(integer n), [])) 
          | _ -> 
              (ignore (warn 
                         "typecheck:@?cannot determine sizes of both:@! %a@! %a@!%a"
                         d_type to_type d_type from_type
                         Pretty.insert context)) ; 
              false
        end 

    | Seq, Safe 
    | SeqN, Safe
    | FSeq, Safe 
    | FSeqN, Safe 
    | String, Safe
    | ROString, Safe 
    | Ptrnode.Index, Safe -> 
        begin
          match bitsSizeOfOpt from_target, bitsSizeOfOpt to_target with
            Some(a),Some(b) when a <> 0 -> 
                let n = (b / a) + 1 in
                type_subtype ~compat:check_compat 
                  ~small:to_target 
                  ~big:(TArray(from_target, Some(integer n), [])) 
          | _ -> 
              (ignore (warn 
                         "typecheck:@?cannot determine sizes of both:@! %a@! %a@!%a"
                         d_type to_type d_type from_type
                         Pretty.insert context)) ; 
              false
        end 

    (* SEQ-SEQ casts *)
    | Seq, Seq    (* no N at all *)
    | FSeq, FSeq 
    | Seq, FSeq  
    | FSeq, Seq 

    | Ptrnode.Index, Ptrnode.Index  (* Index involved *)
    | Ptrnode.Index, Seq
    | Ptrnode.Index, FSeq
    | Ptrnode.Index, SeqN
    | Ptrnode.Index, FSeqN
    | Ptrnode.Index, String

    | SeqN, Seq    (* cast away the N *)
    | FSeqN, FSeq 
    | SeqN, FSeq  
    | FSeqN, Seq 

    | FSeqN, FSeqN (* N on both sides *)
    | SeqN, SeqN 
    | SeqN, FSeqN 
    | FSeqN, SeqN 

    | String, Seq (* string source *)
    | String, FSeq
    | String, SeqN 
    | String, FSeqN 

    | SeqN, String  (* string dest *)
    | FSeqN, String 
    | SeqN, ROString  
    | FSeqN, ROString 

    | ROString, ROString (* string-string cast *)
    | String, String 
    | String, ROString 
      ->  (match to_target with TVoid _ -> true | _ -> false) ||  
          begin
          match bitsSizeOfOpt from_target, bitsSizeOfOpt to_target with
            Some(from_size),Some(to_size) -> 
              let the_gcd = gcd from_size to_size in 
              let from_factor = to_size / the_gcd in 
              let to_factor = from_size / the_gcd in 
              type_equal
                ~compat:check_compat
                ~t1:(TArray(from_target, Some(integer from_factor), []))
                ~t2:(TArray(to_target, Some(integer to_factor), [])) 

          | _ -> (ignore (warn 
            "typecheck:@?cannot determine sizes of both:@! %a@! %a@!%a"
            d_type to_type d_type from_type Pretty.insert context)) ; false
          end 

    | Wild, Wild -> true (* always OK *)

    | Wild, ROString -> true (* always OK *)

    | String, Wild -> begin (* constant strings like "hello" are OK *)
                        match from_exp with
                          Const(CStr _) -> true
                        | _ -> false
                        end

    | Unknown, _ when isArithmeticType from_type &&
                 not (isArithmeticType to_type) -> 
        if not (isZero from_exp) && 
          (to_kind = Safe || to_kind = String || to_kind = ROString) then 
          ignore (warn 
          ("typecheck:@?non-zero value %a of type %a cast into %a type %a@!%a")
            d_exp from_exp d_type from_type 
            d_opointerkind to_kind 
            d_type to_type Pretty.insert context) ;
        true

    | _, Unknown when isArithmeticType to_type && (* ptr to integer *)
                 not (isArithmeticType from_type) -> true

    | _, _ -> ignore
      (warn "typecheck:@?unfamiliar %a -> %a cast@?%a : %a -> %a@!%a" 
        d_opointerkind from_kind d_opointerkind to_kind 
        d_exp from_exp 
        d_type from_type d_type to_type Pretty.insert context) ; true

    ) () in if not okay then ignore
        (warn "typecheck:@?bad %a -> %a cast@?%a -> %a@!%a" 
          d_opointerkind from_kind d_opointerkind to_kind 
          d_type from_type d_type to_type Pretty.insert context)
  end with problem -> ignore
    (warn "typecheck:@?cannot check %a -> %a cast@!%a" 
      d_type from_type d_type to_type Pretty.insert context)
end

let is_polymorphic_function f =
  match f with
    Lval(Var(vi),NoOffset) when String.contains vi.vname '/' -> true
  | _ -> false 

let current_function_type = ref None

(* Consistency checking for code. *)
class typecheck = object
  inherit nopCilVisitor 
  method vexpr e = begin
    match e with
      CastE(to_type, from_exp) -> check_cast (d_exp () e) to_type from_exp
    | BinOp(PlusPI,a,b,_) 
    | BinOp(MinusPI,a,b,_) -> (* pointer is always on the left *)
        typecheck_pointer_arithmetic a b e 
    | _ -> () 
    end ; 
    DoChildren

  method vinst i = 
    match i with 
    | Set(lv,exp,_) -> 
      if (isPointerType (typeOfLval lv)) then begin
        check_cast (d_instr () i) (typeOfLval lv) exp
      end ; DoChildren

    | Call(_,f,_,_) when is_polymorphic_function f -> DoChildren

    | Call(lvopt,f,args,_) -> begin
      match typeOf f with
      | TFun(ret_type, formal_vi_list, vararg, al) -> begin
        (* check the actual arguments *)
        (try 
          List.iter2 (fun (_, formal_vit, _) actual_exp ->
            check_cast (d_instr () i) (formal_vit) actual_exp)
            (argsToList formal_vi_list) args
        with _ -> ()) ; 
        (* finally, check the lvalue against the return type *)
        match lvopt with
          Some(lv) -> 
            check_cast (d_instr () i) (typeOfLval lv) (CastE(ret_type, f))
        | None -> ()
        end
      | tau -> ignore (warn "typecheck:@?call to non-function type %a@!%a"
              d_type tau d_instr i)
      end; DoChildren
    | Asm _ -> DoChildren
  method vstmt s = 
    match s.skind with
    | Return(Some(e),l) -> begin
      match !current_function_type with
        Some(TFun(ret_type,_,_,_)) ->
          check_cast (d_stmt () s) ret_type e
      | Some(tau) -> ignore (warn "typecheck:@?return inside non-function@!%a"
          d_stmt s)
      | None -> ignore (warn "typecheck:@?return not inside a function@!%a"
          d_stmt s)
      end;
      DoChildren
    | _ -> DoChildren
  method vblock b = 
    if hasAttribute "nocure" b.battrs then
      SkipChildren
    else
      DoChildren
  method vfunc f = 
    typecheck_varinfo f.svar (List.map (fun vi -> vi.vtype) f.sformals) ;
    List.iter (fun vi -> typecheck_varinfo vi []) f.sformals ;
    List.iter (fun vi -> typecheck_varinfo vi []) f.slocals ;
    DoChildren
  method vglob g = match g with
      GFun(fundec,_) -> 
        current_function_type := Some(fundec.svar.vtype) ; 
        (if !checking then DoChildren else SkipChildren)
    | GType(tau,_) -> (if !checking then typecheck_type tau.ttype [] ) ;
                          SkipChildren
    | GPragma(a, _) -> begin
        match a with
          | Attr("ccured", [ACons("on",_)]) -> checking := true
          | Attr("ccured", [ACons("off",_)]) -> checking := false
          | _ -> () 
      end ; DoChildren
    | _ -> DoChildren
end

let typechecker = new typecheck 
  
(* The main entry point to our typechecker *)
let typecheck_file f =
  checking := true ; ignore (visitCilFile typechecker f) 
