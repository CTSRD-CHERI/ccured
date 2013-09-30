
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
open Trace

open Clist

module H = Hashtbl
module E = Errormsg
module N = Ptrnode 
module MU = Markutil
module OU = Optutil

(**** We know in what function we are ****)
let currentFunction : fundec ref  = ref dummyFunDec
let currentFile     : file ref = ref dummyFile
let currentFileId     = ref 0

let logScalars = ref false


let stackChecks = ref true	    (* include checks like CHECK_STOREPTR *)
let returnStackChecks = ref false   (* Include CHECK_RETURNPTR? We turned 
                                     * this off, because in the presence of 
                                     * inlining (as in gcc 4) we do not have 
                                     * a good way to check this. We get too 
                                     * many false alarms. *)



let optimizeStackChecks = false

let lu = locUnknown
let isSome = function Some _ -> true | _ -> false


(* make a function type (non-vararg with no attributes) *)
let funType (ret_t: typ) 
            (args: (string * typ) list) = 
  TFun(ret_t, 
       Some (List.map (fun (n,t) -> (n, t, [])) args),
       false, [])

(**** Stuff that we use while converting to new CIL *)
let call lvo f args : stmt = mkStmtOneInstr (Call(lvo,f,args, !currentLoc))


(*** Helpers *)            
let castVoidStar e = mkCast e voidPtrType

  
(****** the CHECKERS ****)


let mkCheck (n: string) ?(rt: typ option) 
                        (args: (string * typ) list) : fundec = 
  let fdec = emptyFunction n in
  let rt = 
    match rt with 
      None -> voidType
    | Some t -> t
  in
  fdec.svar.vtype <- funType rt args;
  fdec.svar.vstorage <- Static;
  fdec
  
let checkNull =
  let fdec = mkCheck "CHECK_NULL" [ ("p", voidPtrType) ] in 
  fun (what: exp) ->
    (* Optimize here the case when what is the address of a global *)
    let rec certainlyNotNull = function
        CastE (_, x) -> certainlyNotNull x
      | AddrOf (Var x, _) -> true
      | _ -> false
    in
    if certainlyNotNull what then 
      mkEmptyStmt ()
    else
      call None (Lval(var fdec.svar)) [ castVoidStar what ]

let checkSafeEnd : exp -> exp -> exp * stmt clist =
  let fdec = mkCheck "CHECK_SAFE_END" ~rt:voidPtrType 
      [ ("p", voidPtrType); ("e", voidPtrType) ] in 
  fun (safe: exp) (tentative_end: exp) ->
    (* Optimize here the case when 'what' is the address of a global *)
    let rec certainlyNotNull = function
        CastE (_, x) -> certainlyNotNull x
      | AddrOf (Var x, _) -> true
      | _ -> false
    in
    if certainlyNotNull safe then 
      tentative_end, empty
    else if isZero safe then 
      zero, empty
    else begin
      (* Must make a temporary variable *)
      let true_end = makeTempVar !currentFunction voidPtrType in

      Lval (var true_end),
      single (call (Some (var true_end)) (Lval(var fdec.svar)) 
                [ castVoidStar safe; 
                  castVoidStar tentative_end ])
    end
        

let checkFunctionPointerFun =
  mkCheck "CHECK_FUNCTIONPOINTER" [ ("p", voidPtrType);
                                    ("b", voidPtrType); 
                                    ("nr", intType) ]


let checkFetchLength =
  let fdec = mkCheck "CHECK_FETCHLENGTH" ~rt:uintType 
      [ ("p", voidPtrType); ("b", voidPtrType); ("noint", intType) ] in
  fun tmplen ptr base (noint: bool) ->
    call (Some (var tmplen)) (Lval (var fdec.svar))
      [ castVoidStar ptr;
        castVoidStar base;
        if noint then one else zero ]

(* Prepare the nullterm functions *)
let fetchNulltermEnd1 = mkCheck "CHECK_FETCHNULLTERMEND1" ~rt:voidPtrType
    [ ("s", charPtrType) ] 
let fetchNulltermEnd2 = mkCheck "CHECK_FETCHNULLTERMEND2" ~rt:voidPtrType
    [ ("s", voidPtrType) ]
let fetchNulltermEnd4 = mkCheck "CHECK_FETCHNULLTERMEND4" ~rt:voidPtrType
    [ ("s", voidPtrType) ]
let fetchNulltermEndGen = mkCheck "CHECK_FETCHNULLTERMEND_GEN" ~rt:voidPtrType
    [ ("s", voidPtrType);  ("sz", intType)  ]

(** Given the size, return the function to be called and the tail of the 
 * arguments *)
let checkFetchNulltermEnd (sz: int) : fundec * exp list = 
  match sz with 
  | 1 -> fetchNulltermEnd1, []
  | 2 -> fetchNulltermEnd2, []
  | 4 -> fetchNulltermEnd4, []
  | _ -> fetchNulltermEndGen, [ integer sz ]

let checkStringMax =
  mkCheck "CHECK_STRINGMAX" ~rt:uintType 
    [ ("p", voidPtrType); ("b", voidPtrType)]

let checkRttiCast =
  mkCheck "CHECK_RTTICAST" [ ("src_rtti", MU.rttiType);
                             ("dest_rtti", MU.rttiType) ]

let checkRttiUnionTag =
  let fdec = emptyFunction "CHECK_RTTIUNIONTAG" in
  fdec.svar.vstorage <- Static;
  fdec.svar.vtype <- 
     funType voidType [ ("src_rtti", MU.rttiType);
                        ("dest_rtti", MU.rttiType) ];
  fdec

let checkSeq2FSeqFun =
  let fdec = emptyFunction "CHECK_SEQ2FSEQ" in
  fdec.svar.vtype <- funType voidType [ ("b", voidPtrType);
                                        ("e", voidPtrType);
                                        ("p", voidPtrType) ];
  fdec.svar.vstorage <- Static;
  fdec

let checkFetchIndexEndFun =
  let fdec = emptyFunction "CHECK_FETCH_INDEX_END" in
  fdec.svar.vtype <- funType voidPtrType [ ("p", voidPtrType);
                                           ("b", voidPtrType);
                                           ("noint", intType) ];
  fdec.svar.vstorage <- Static;
  fdec

let checkGeuFun = 
  mkCheck "CHECK_GEU" [ ("e1", uintType);("e2", uintType) ]

let checkFSeqAlignFun =
  mkCheck "CHECK_FSEQALIGN" [ ("sz", uintType);
                              ("p", voidPtrType);
                              ("e", voidPtrType);
                            ]

let checkSeqAlignFun =
  mkCheck "CHECK_SEQALIGN" [ ("sz", uintType);
                             ("p", voidPtrType);
                             ("b", voidPtrType);
                             ("e", voidPtrType);
                           ]

let checkIndexAlignFun =
  mkCheck "CHECK_INDEXALIGN" [ ("sz", uintType); ("b", voidPtrType); ]

(* sm: check ubound, or allow NULL pointer (modified from above) *)
let checkFSeq2SafeFun =
  let fdec = emptyFunction "CHECK_FSEQ2SAFE" in
  fdec.svar.vtype <- funType voidType [ ("bend", voidPtrType);
                                        ("p", voidPtrType);
                                        ("srcl", uintType);
                                        ("destl", uintType);
                                        ("foraccess", intType);
                                        ("noint", intType) ];
  fdec.svar.vstorage <- Static;
  fdec

(* sm: check bounds, or allow NULL pointer, but not any other integer *)
let checkSeq2SafeFun =
  let fdec = emptyFunction "CHECK_SEQ2SAFE" in
  fdec.svar.vtype <- funType voidType [ ("b", voidPtrType);
                                        ("bend", voidPtrType);
                                        ("p", voidPtrType);
                                        ("srcl", uintType);
                                        ("pl", uintType);
                                        ("foraccess", intType);
                                        ("noint", intType) ];
  fdec.svar.vstorage <- Static;
  fdec


let checkFSeqnWrite =
  mkCheck "CHECK_FSEQN_WRITE" [ ("bend", voidPtrType);
                                ("p", voidPtrType);
                                ("len", uintType);
                                ("noint", intType);
                                ("isnul", intType) ]

let checkSeqnWrite =
  mkCheck "CHECK_SEQN_WRITE" [ ("b", voidPtrType);
                              ("bend", voidPtrType);
                              ("p", voidPtrType);
                              ("len", uintType);
                              ("noint", intType);
                              ("isnul", intType) ]

let checkStringWrite =
  mkCheck "CHECK_STRING_WRITE" [ ("p", voidPtrType);
                                 ("isnul", intType) ]


      
let checkSeq2Safe (b: exp) 
                  (bend: exp) 
                  (p: exp) 
                  (dest_baset: typ) 
                  (foraccess: bool)
                  (noint: bool)  : stmt clist = 
  (* Look for some special cases *)
  let src_baset = 
    match unrollType (typeOf p) with
      TPtr(x, _) -> x
    | _ -> E.s (bug "checkSeq2Safe: expected pointer type in source")
  in
  try
    match b, bend, p with 
    | StartOf array_lv, _, _ -> begin (* Access into an array *)
        match OU.normalizeAddr bend, 
              OU.normalizeAddr p, 
              OU.normalizeExp (SizeOf(dest_baset)) with 
        | Some (StartOf array_lv_end, 0, _, off_end),
          Some (StartOf array_lv_p, s_p, i_p, off_p), (* a + s * i + off *)
          Some (0, _, sz)
            when (Util.equals array_lv_end array_lv)
                && (Util.equals array_lv_p array_lv)
            && (s_p = 0 || s_p = sz) ->
              (* Ought to check that off_end is the length of the array *)
              begin
                if (off_end < sz) then begin
                  ignore (warn "checkSeq2Safe: not enough room: element size=%d and array length = %d" sz off_end);
                  raise Not_found; (* leave the check in. It will fail! *)
                end else if s_p = 0 then begin
                  if off_p < 0 || off_p + sz > off_end then begin
                    ignore (warn "checkSeq2Safe: array access out of bounds: accessing [%d-%d] in an array of %d bytes" off_p (off_p + sz - 1) off_end);
                    raise Not_found (* leave the check in. It will fail! *)
                  end else 
                    empty (* Nothing else to check *)
                end else begin
                  (* Ocaml rounds division towards 0 *)
                  let ufloor x sz = 
                    if x >= 0 then (x + sz - 1) / sz
                    else (x - sz + 1) / sz
                  in
                  single (call None (Lval (var checkGeuFun.svar))
                            [ mkCast (integer ((off_end / sz) - 1))
                                uintType ;
                              (if off_p = 0 then 
                                mkCast i_p uintType
                              else
                                BinOp(PlusA, 
                                      mkCast i_p uintType,
                                      integer (ufloor off_p sz),
                                      uintType))
                            ])
                end
              end
        | _, _, _ -> raise Not_found
    end
          
    | _, _, _ -> raise Not_found
  with Not_found -> 
    single (call None (Lval (var checkSeq2SafeFun.svar))
              [ castVoidStar b;  
                castVoidStar bend;
                castVoidStar p; 
                SizeOf (src_baset);
                SizeOf (dest_baset);
                if foraccess then one else zero;
                if noint then one else zero ])
  
                  

let checkBoundsLenFun =
  let fdec = emptyFunction "CHECK_BOUNDS_LEN" in
  fdec.svar.vtype <- funType voidType [ ("b", voidPtrType);
                                        ("bl", uintType);
                                        ("p", voidPtrType);
                                        ("srcl", uintType);
                                        ("pl", uintType) ];
  fdec.svar.vstorage <- Static;
  fdec

(* A run-time function to coerce scalars into pointers. Scans the heap and
 * (in the future the stack) *)
let logScalarId = ref 0
let logScalarFunction =
  let fdec = emptyFunction "LOG_SCALAR" in
  fdec.svar.vtype <- funType voidPtrType [ ("log_id", intType);
                                             ("l", ulongType)
                                         ];
  fdec

let logScalar (p: exp) : stmt clist =
  if !logScalars then begin
    incr logScalarId;
    single (call None
              (Lval(var logScalarFunction.svar)) 
              [ integer !logScalarId; mkCast p (TInt(IULong, [])) ])
  end else 
    empty
    
(* Create (if we haven't already) a volatile int whose address we can take to
 * establish the top of the stack frame.  Hopefully its address will be an
 * accurate  estimate of the frame address, even when GCC decides to 
 * inline this function. This doesn't work on MSVC, which 
 * reorders stack variables. *)
let getFirstLocal () : varinfo =
  let f = !currentFunction in
  match f.slocals with
    fstvar :: rest when fstvar.vname = "___first_local" ->
      (* we've already created ___first_local *)
      fstvar
  | _ -> 
      (* we need to create ___first_local *)
      let fstvar = 
        makeLocalVar f ~insert:false "___first_local" 
          (TInt(IInt, [Attr("volatile", []);])) in
      f.slocals <- fstvar :: f.slocals;
      fstvar


(* returns either the value of the frame pointer or the
 * address of the first local variable.
 * May also return a function call that needs to be inserted
 * before the return expression is evaluated.
 *)
let getTopOfFrame () : exp * (instr option) = 
  if !Cil.msvcMode then begin
    (* Use the frame pointer.  This obviously doesn't work if you optimize
     * the frame pointer away. *)

    (* CHECK_GETFRAME is acutally a macro that will set putWhere = ebp *)
    let fdec = emptyFunction "CHECK_GETFRAME" in
    fdec.svar.vtype <- funType voidType [ "putWhere", charPtrType ];
    fdec.svar.vstorage <- Static;

    let tmp = makeTempVar !currentFunction charPtrType in
    let tmpLval = Lval(var tmp) in
    let getFPcall = Call(None, (Lval(var fdec.svar)), [ tmpLval ],
			 !currentLoc) in
    tmpLval, Some getFPcall
  end 
  else begin
    (* Use the address of the first stack var. This doesn't work on MSVC.*)
    let firstLocal = getFirstLocal () in
    mkAddrOf (var firstLocal), None
  end

(* Check a read *)
let checkWildPointerRead =
  let fdec = emptyFunction "CHECK_WILDPOINTERREAD" in
  fdec.svar.vtype <- funType voidType [ ("b", voidPtrType);
                                        ("nrWords", uintType);
                                        ("p", voidPtrType) ];
  fdec.svar.vstorage <- Static;

  fun base where len ->
    call None (Lval(var fdec.svar))
      [ castVoidStar base; len; castVoidStar where]

let checkWildPointerWrite =
  let fdec = emptyFunction "CHECK_WILDPOINTERWRITE" in
  fdec.svar.vtype <- funType voidType [ ("b", voidPtrType);
                                        ("nrWords", uintType);
                                        ("p", voidPtrType);
                                        ("wb", voidPtrType);
                                        ("wp", voidPtrType);
				        ("pTopOfFrame", voidPtrType) ];
  fdec.svar.vstorage <- Static;

  fun base where whatbase whatp len ->
    match getTopOfFrame () with
      top, None ->
	mkStmtOneInstr (Call(None, (Lval(var fdec.svar)),
			     [ castVoidStar base; 
			       len;
			       castVoidStar where;
			       castVoidStar whatbase; 
			       castVoidStar whatp;
			       castVoidStar top ],
			     !currentLoc))
    | top, Some getFramePtrCall ->
	mkStmt (Instr [getFramePtrCall;
		       Call(None, (Lval(var fdec.svar)),
			    [ castVoidStar base; 
					      len;
			      castVoidStar where;
			      castVoidStar whatbase; 
			      castVoidStar whatp;
			      castVoidStar top ],
			    !currentLoc)])

let checkWildPointerWrite_noStackCheck =
  let fdec = emptyFunction "CHECK_WILDPOINTERWRITE_NOSTACKCHECK" in
  fdec.svar.vtype <- funType voidType [ ("b", voidPtrType);
                                        ("nrWords", uintType);
                                        ("p", voidPtrType);
                                        ("wb", voidPtrType);
                                        ("wp", voidPtrType) ];
  fdec.svar.vstorage <- Static;

  fun base where whatbase whatp len ->
    call None (Lval(var fdec.svar))
      [ castVoidStar base; len;
        castVoidStar where;
        castVoidStar whatbase; castVoidStar whatp;]

let checkStorePtr : exp -> exp -> stmt =
  let fdec = emptyFunction "CHECK_STOREPTR" in
  fdec.svar.vtype <- funType voidType [ ("where", voidPtrType);
                                        ("p", voidPtrType);
					("pTopOfFrame", intPtrType); ];
  fdec.svar.vstorage <- Static;

  fun where whatp -> 
    if !stackChecks then begin
      (* Check that the pkEscape flag is set *)
      if optimizeStackChecks then 
        (match N.nodeOfAttrlist (typeAttrs (typeOf whatp)) with
          Some n -> 
            if not (N.hasFlag n N.pkEscape) then 
              ignore (warn "Node %d does not have the escape attribute set"
                        n.N.id)
        | None -> 
            ignore (warn "Cannot find the node of written %a\n" d_exp whatp));
      match getTopOfFrame () with
        top, None ->
	  mkStmtOneInstr (Call(None, (Lval(var fdec.svar)),
			       [ castVoidStar where;
				 castVoidStar whatp;
				 castVoidStar top],
			       !currentLoc))
      | top, Some getFramePtrCall ->
	  mkStmt (Instr [getFramePtrCall;
			 Call(None, (Lval(var fdec.svar)), 
			      [castVoidStar where;
			       castVoidStar whatp;
			       castVoidStar top],
			      !currentLoc) ])
    end else mkEmptyStmt ()
       
let checkReturnPtr =
  let fdec = emptyFunction "CHECK_RETURNPTR" in
  fdec.svar.vtype <- funType voidType [ ("p", voidPtrType);
                                        ("pTopOfFrame", intPtrType); ];
  fdec.svar.vstorage <- Static;

  fun whatp ->
    if !stackChecks && !returnStackChecks then begin
      match getTopOfFrame () with
        top, None ->
	  mkStmtOneInstr (Call(None, (Lval(var fdec.svar)),
			       [ castVoidStar whatp; 
				 castVoidStar top ],
			       !currentLoc))
      | top, Some getFramePtrCall ->
	  mkStmt (Instr [getFramePtrCall;
			 Call(None, (Lval(var fdec.svar)), 
				[ castVoidStar whatp; 
				  castVoidStar top ],
			      !currentLoc)])
    end
    else mkEmptyStmt ()

let checkZeroTagsFun =
  let fdec = emptyFunction "CHECK_ZEROTAGS" in
  fdec.svar.vtype <- funType voidType [ ("b", voidPtrType);
                                        ("bl", uintType);
                                        ("p", voidPtrType);
                                        ("size", uintType) ];
  fdec.svar.vstorage <- Static;
  fdec

let checkFindHomeFun =
  let fdec = emptyFunction "CHECK_FINDHOME" in
  fdec.svar.vtype <- funType voidPtrType [ ("kind", intType);
                                           ("p", voidPtrType) ];
  fdec.svar.vstorage <- Static;
  fdec


let checkFindHomeEndFun =
  let fdec = emptyFunction "CHECK_FINDHOMEEND" in
  fdec.svar.vtype <- funType voidPtrType [ ("kind", intType);
                                           ("p", voidPtrType);
                                           ("ea", TPtr(voidPtrType,[]))];
  fdec.svar.vstorage <- Static;
  fdec


(***** Pointer arithemtic *******)
let checkPositiveFun =
  let fdec = emptyFunction "CHECK_POSITIVE" in
  fdec.svar.vtype <- funType voidType [ ("x", intType) ];
  fdec.svar.vstorage <- Static;
  fdec

let checkFSeqArithFun = 
  let fdec = emptyFunction "CHECK_FSEQARITH" in
  fdec.svar.vtype <- funType voidType [ ("p", voidPtrType);
                                        ("plen", uintType);
                                        ("p_x", voidPtrType);
                                        ("bend", voidPtrType);
                                        ("checkAlign", intType);
                                      ];
  fdec.svar.vstorage <- Static;
  fdec


(* A combination of pointer arithmetic and safety check *)
let checkFSeqArith2SafeFun = 
  mkCheck "CHECK_FSEQARITH2SAFE" 
    [ ("p", voidPtrType);
      ("bend", voidPtrType);
      ("ppi", voidPtrType);
      ("srclen", uintType);
      ("plen", uintType);
      ("foraccess", intType);
      ("noint", intType);
      ("checkAlign", intType);
    ]
  
let checkSeqArithFun =
  let fdec = emptyFunction "CHECK_SEQARITH" in
  fdec.svar.vtype <- funType voidType [ ("sz", uintType);
                                        ("p", voidPtrType);
                                        ("b", voidPtrType);
                                        ("e", voidPtrType);
                                      ];
  fdec.svar.vstorage <- Static;
  fdec

(* A few constants *)
let registerAreaTaggedInt = 0
let registerAreaSizedInt  = 1
let registerAreaSeqInt    = 2


let registerAreaFun =   
  let fdec = emptyFunction "CHECK_REGISTERAREA" in
  fdec.svar.vtype <- funType voidType [ ("kind", intType);
                                        ("b", voidPtrType);
                                        ("e", voidPtrType) ];
  fdec.svar.vstorage <- Static;
  fdec

let unregisterFrameFun =
  let fdec = emptyFunction "CHECK_UNREGISTERFRAME" in
  fdec.svar.vtype <- TFun(voidType, Some [ ], false, []);
  fdec.svar.vstorage <- Static;
  fdec

