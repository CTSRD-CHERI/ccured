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


let lu = locUnknown

let currentFile = ref dummyFile
let currentResultType = ref voidType

let boxing = ref true


let noStackOverflowChecks = ref false

(* Remember the structures we have marked already. This way we detect forward 
 * references *)
let markedCompInfos: (int, unit) H.t = H.create 17

(* Remember the nodes for which the PointsTo information is unreliable 
 * because they point to forward-declared structures *)
let mustRecomputePointsTo: (int, N.node) H.t = H.create 17


let callId = ref (-1)  (* Each call site gets a new ID *)


let allocFunctions: (string, unit) H.t = H.create 17

(* weimer: utility function to ease the transition between our flag formats *)
let setPosArith n why = begin N.setFlag n N.pkPosArith why end 
let setArith n why = begin N.setFlag n N.pkArith why  end 
let setUpdated n why = begin N.setFlag n N.pkUpdated why end
let setIntCast n why = begin N.setFlag n N.pkIntCast why end
let setInterface n why = begin N.setFlag n N.pkInterface why end
let setNoProto n why = begin N.setFlag n N.pkNoPrototype why end
let setReferenced (n : N.node) why : unit = 
begin
  (*(trace "sm" (dprintf "setting referenced at %a\n" d_loc n.N.loc));*)
  (N.setFlag n N.pkReferenced why)
end
let setEscape n why = begin N.setFlag n N.pkEscape why end
let setStack n why = begin N.setFlag n N.pkStack why end
let default_why () = N.ProgramSyntax(!currentLoc) 

(* Add a prototype for __builtin_alloca to the file.  cabs2cil uses this for
   variable-sized functions, and user code may use it as well.  Unfortunately,
   we can't put this in an include file because cabs2cil discards the
   declarations of __builtin functions.     *)
let addAlloca () : unit =
  if not !msvcMode then begin
    let name = "__builtin_alloca" in
    let vi = makeGlobalVar name
               (TFun(voidPtrType, Some [("len", !typeOfSizeOf, [])], false,[]))
    in
    let prag = Attr("ccuredalloc", [AStr(name); 
                                    ACons("nozero", []);
                                    ACons("sizein", [AInt 1]) ]) in
    (!currentFile).globals <- GVarDecl(vi, locUnknown) 
                             :: GPragma (prag, locUnknown)
                             :: (!currentFile).globals;
  end


(* We keep track of a number of type that we should not unroll *)
let dontUnrollTypes : (string, bool) H.t = H.create 19

let rec mustUnrollTypeInfo (ti: typeinfo) : bool = 
  (not (H.mem dontUnrollTypes ti.tname)) &&
  (match ti.ttype with 
  | TPtr _ -> true
  | TArray _ -> true
  | TFun _ -> true
  | TNamed (ti', _) -> mustUnrollTypeInfo ti'
    (* We will also unroll types that name a polymorphic structure *)
  | TComp (ci, _) -> Poly.isPolyComp ci 
  | _ -> false)


(* if some enclosing context [like the attributes for a field] says that
 * this array should be sized ... we do not want to forget it! *)
let addArraySizedAttribute arrayType enclosingAttr =
  if filterAttributes "sized" enclosingAttr <> [] then
    typeAddAttributes [Attr("sized",[])] arrayType
  else
    if hasAttribute "safeunion" enclosingAttr then
      typeAddAttributes [Attr("safeunion",[])] arrayType
    else
      arrayType

(* Grab the node from the attributs of a type. Returns dummyNode if no such 
 * node *)
let nodeOfType t = 
  match unrollType t with 
    TPtr(_, a) -> begin
      match N.nodeOfAttrlist a with
        Some n -> n
      | None -> N.dummyNode
    end
  | _ -> N.dummyNode


(* Pass also the place and the next index within the place. Returns the 
 * modified type and the next ununsed index *)
let rec doType (t: typ) (p: N.place) 
               (nextidx: int) : typ * int = 
  match t with 
    (TVoid _ | TInt _ | TFloat _ | TEnum _ ) -> t, nextidx
  | TBuiltin_va_list _ -> t,nextidx
(*
      E.s (error "Encountered the __builtin_va_list type. This means that you have not used the <stdarg.h> or <vararg.h> macros. We can't help you")

*)  
  | TPtr (bt, a) -> begin
      match N.nodeOfAttrlist a with
        Some n -> TPtr (bt, a), nextidx (* Already done *)
      | None -> 
          let bt', i' = doType bt p (nextidx + 1) in
          let n = N.getNode p nextidx bt' a in
          (* See if the bt is a forward referenced TComp *)
          (match unrollType bt with 
            TComp(ci, _) when not (H.mem markedCompInfos ci.ckey) -> 
              H.add mustRecomputePointsTo n.N.id n

          | _ -> ());
          TPtr (bt', n.N.attr), i'
  end
  | TArray(bt, len, a) -> begin
      (* wes: we want a node for the array, just like we have a node for
       * each pointer *)
      match N.nodeOfAttrlist a with
        Some n -> TArray (bt, len, a), nextidx (* Already done *)
      | None -> 
          let bt', i' = doType bt p (nextidx + 1) in
          let n = N.getNode p nextidx bt' a in
          n.N.is_array <- true;
          TArray (bt', len, n.N.attr), i'
  end
          
  | TComp(c, at)-> 
      if Poly.isPolyComp c then begin
        (* We must make a copy of it. If we need to create new ones we must 
         * mark them and add them to the file *)
        let c' = Poly.instantiatePolyComp c 
            (fun c'' -> 
              markCompInfo c'' !currentLoc;
              (* Add a global definition for it *)
              MU.theFile := GCompTag (c'', !currentLoc) :: !MU.theFile) in
        TComp(c', at), nextidx
      end else
        t, nextidx (* A reference to a regular composite type, leave alone *)

    (* Strip the type names so that we have less sharing of nodes. However, 
     * we do not need to do it if the named type is a structure, and we get 
     * nicer looking programs. We also don't do it for base types *)
  | TNamed (bt, a) -> 
      if mustUnrollTypeInfo bt then begin
        let t', nextidx' = doType bt.ttype p nextidx in
        t', nextidx'
      end else
        (* A type reference. Leave alone. We'll handle the type inside when 
         * we do the GType *)
        t, nextidx
        
  | TFun (restyp, args, isva, a) -> 
      let noproto = hasAttribute "missingproto" a in
      let restyp = 
        if noproto && not (isPointerType restyp) then 
          voidPtrType
        else restyp 
      in
      let restyp', i0 = doType restyp p nextidx in
      let args', i' = match args with 
        None -> None, i0
      | Some argl -> 
          let argl', i' =  
            List.fold_left 
              (fun (args', nidx) (an, at, aa) -> 
                let t', i' = doType at p nidx in
                ((an,t',aa) :: args', i')) ([], i0) argl 
          in
          Some (List.rev argl'), i'
      in
      let newtp = TFun(restyp', args', isva, a) in
      let newtp' = Vararg.processFormatAttribute newtp in
      newtp', i'

and doField (f: fieldinfo) : N.node = 
  let fftype = addArraySizedAttribute f.ftype f.fattr in 
  let t', i' = doType fftype (N.PField f) 1 in
  (* Now create the node corresponding to the address of the field *)
  let nd = N.newNode (N.PField f) 0 t' f.fattr in
  f.fattr <- addAttributes f.fattr nd.N.attr ; 
  f.ftype <- t';
  nd
  
    
(** This is called once for each compinfo DEFINITION. Do not call for 
 * declarations. It will process the fields and will add the nodes 
 * corresponding to the address of the fields. *)
and markCompInfo (comp: compinfo) (comptagloc: location) : unit = 
  (* We must do its fields *)
  List.iter (fun f -> ignore (doField f)) comp.cfields;
  (* Keep track of the compinfo we have done. We do this after we have done 
   * the fields, just in case some of the fields refer to the whole structure.
   *)
  H.add markedCompInfos comp.ckey ();

  (* Now handle unions specially *)
  if not comp.cstruct then 
    Taggedunion.markUnionComp comp comptagloc;

  ()

(* Create a field successor. Just get the node from the field attributes. 
 * Also add an EOFFSET edge from the pointer to struct to pointer to field. *)
let fieldOfNode (n: N.node) (fi: fieldinfo) : N.node =
  if N.useOffsetNodes then begin
    (* Make a new node *)
    let fieldn = N.getNode (N.POffset (n.N.id, fi.fname)) 0 fi.ftype [] in
    (* And add the ESafe edge *)
    let _ = N.addEdge n fieldn N.EOffset (Some !currentLoc) in 
(*
    ignore (E.log "Created the node %d offset %s for %d\n" 
              fieldn.N.id fi.fname n.N.id);
*)
    fieldn
  end else begin
    (* In the original scheme we have one node for the address of a field. 
     * The problem with this is that it is shared to much and contributes to 
     * the spreading of WILDness *)
    match N.nodeOfAttrlist fi.fattr with
      Some fieldn -> 
        (* Add an EOffset edge from n to fieldn *)
        let _ = N.addEdge n fieldn N.EOffset (Some !currentLoc) in 
        fieldn
          
    | None -> 
        (* We should have created nodes for all fieldinfo *)
        E.s (bug "Field %s.%s does not have a node"
               (compFullName fi.fcomp) fi.fname)
  end

let startOfNode (n: N.node) : N.node =
  match unrollType n.N.btype with
    TArray (bt, len, a) -> 
      let next = 
        match N.nodeOfAttrlist a with
          Some oldn -> 
            (* ignore (E.log "Reusing node %d\n" oldn.N.id); *)
            oldn
        | _ -> 
            E.s (bug "Array type does not have a node")
            (* Somehow I hope that we never come here. This should be true if 
            * all TArray got a node attribute already 
            ignore (warn "Creating a node for array @first\n");
            let next = N.newNode (N.POffset(n.N.id, "@first")) 0 bt a in
            (* !!! We should be remembering this one somewhere *)
            next *)
      in              
      let _ = N.addEdge n next N.EIndex (Some !currentLoc) in 
      next

  | _ -> n (* It is a function *)
  



(* Compute the sign of an expression. Extend this to a real constant folding 
 * + the sign rule  *)
type sign = SPos | SNeg | SAny | SLiteral of int64

let rec signOf = function
    Const(CInt64(n, _, _)) -> SLiteral n
  | Const(CChr c) -> signOf (Const (charConstToInt c))
  | SizeOf _ -> SPos (* We do not compute it now *)
  | UnOp (Neg, e, _) -> begin
      match signOf e with
        SPos -> SNeg
      | SLiteral n -> SLiteral (Int64.neg n)
      | SNeg -> SNeg
      | _ -> SAny
  end
  | UnOp (LNot, e, _) -> SPos
  | BinOp (PlusA, e1, e2, _) -> begin
      match signOf e1, signOf e2 with
        SPos, SPos -> SPos
      | SLiteral n, SPos when n >= Int64.zero -> SPos
      | SPos, SLiteral n when n >= Int64.zero -> SPos
      | SLiteral n1, SLiteral n2 -> SLiteral (Int64.add n1 n2)
      | SNeg, SNeg -> SNeg
      | SLiteral n, SNeg when n <= Int64.zero -> SNeg
      | SNeg, SLiteral n when n <= Int64.zero -> SNeg
      | _ -> SAny
  end
  | BinOp (MinusA, e1, e2, _) -> begin
      match signOf e1, signOf e2 with
        SPos, SNeg -> SPos
      | SLiteral n, SNeg when n >= Int64.zero -> SPos
      | SPos, SLiteral n when n <= Int64.zero -> SPos
      | SLiteral n1, SLiteral n2 -> SLiteral (Int64.sub n1 n2)
      | SNeg, SPos -> SNeg
      | SLiteral n, SPos when n <= Int64.zero -> SNeg
      | SNeg, SLiteral n when n >= Int64.zero -> SNeg
      | _ -> SAny
  end
  | _ -> SAny


(* Do varinfo. We do the type and for all variables we also generate a node 
 * that will be used when we take the address of the variable (or if the 
 * variable contains an array) *)
let doVarinfo (vi : varinfo) : unit = 
  (* Compute a place for it *)
  let original_location = !currentLoc in (* weimer: better places *)
  if vi.vdecl <> locUnknown then 
    currentLoc := vi.vdecl ; 
  let place = 
    if vi.vglob then
      if vi.vstorage = Static then 
        N.PStatic (!currentFile.fileName, vi.vname)
      else
        N.PGlob vi.vname
    else
      N.PLocal (!currentFile.fileName, !MU.currentFunction.svar.vname, 
                vi.vname)
  in
  let vi_vtype = addArraySizedAttribute vi.vtype vi.vattr in 
  (* Do the type of the variable. Start the index at 1 *)
  let t', _ = doType vi_vtype place 1 in
  vi.vtype <- t';
(*  ignore (E.log "Did varinfo: %s. T=%a\n" vi.vname
            d_plaintype vi.vtype); *)
  (* Associate a node with the variable itself. Use index = 0 *)
  let n = N.getNode place 0 vi.vtype vi.vattr in

  (* Add this to the variable attributes. Note that this node might have been 
   * created earlier. Merge the attributes and make sure we get the _ptrnode 
   * attribute  *)
  vi.vattr <- addAttributes vi.vattr n.N.attr;
(*  ignore (E.log "varinfo: T=%a. A=%a\n" 
            d_plaintype vi.vtype (d_attrlist true) vi.vattr) *)

  (* sg: not global and not static means a variable goes on the stack *)
  if (not vi.vglob) && (vi.vstorage <> Static) then
  currentLoc := original_location ; 
  (* Now see if this is a function pointer then we might have to look at the 
   * overrides *)
  (match unrollTypeDeep vi.vtype with 
    TPtr(TFun _, _) -> Markcxx.fixFunctionPointerVar vi !currentLoc
  | _ -> ()
  );
  currentLoc := original_location ; 
  ()

(* Check a sizeof argument *)
let checkSizeOfArgument (t: typ) = 
  (* Now give a warning if this type contains pointers *)
  let containsExposedPointers t = 
    existsType 
      (function 
          TPtr _ -> ExistsTrue
              (* Pointers inside named structures are not exposed *)
        | TComp (comp, _) 
            when (String.length comp.cname > 1 &&
                  String.get comp.cname 0 <> '@') -> ExistsFalse
                      (* Pointers behind names are not exposed *)
        | TNamed _ -> ExistsFalse
        | _ -> ExistsMaybe) t 
  in
  if containsExposedPointers t then begin
    (* Take a look at the node and see if it is disconnected *)
    let extra_msg = 
      match N.nodeOfAttrlist (typeAttrs t) with 
        Some n -> (* It is Ok if this node has edges that are not 
          * EPointsTo *)
          if List.exists (fun e -> e.N.ekind <> N.EPointsTo) n.N.succ ||
          List.exists (fun e -> e.N.ekind <> N.EPointsTo) n.N.pred 
          then
            "Type has a connected node."
          else
            "Type has a disconnected node."
              
      | None -> "Type does not have a node."
    in
    ignore (warn "Encountered sizeof(%a) when type contains pointers. Use sizeof expression. %s" d_type t extra_msg);
  end
  
(* Do an expression. Return an expression, a type and a node. The node is 
 * only meaningful if the type is a TPtr _. In that case the node is also 
 * refered to from the attributes of TPtr. Otherwise the node is N.dummyNode
  *)
let rec doExp ?(inSizeof:bool = false) (e: exp): exp * typ * N.node = 
  let markAddrOfLocal lv lvn : unit =
    (* when taking the address of an lvalue, check whether we're taking the
       address of a local var. *)
    let locals = (!MU.currentFunction).slocals in
    let formals = (!MU.currentFunction).sformals in
    (match lv with 
         (Var vi), _ when
           (List.mem vi locals || List.mem vi formals)
           && not (hasAttribute "heapify" vi.vattr)
           ->
             (* Taking the address of a local variable*)
             setStack lvn (default_why ())
       | _ -> ())
  in
  match e with 
    Lval lv -> 
      let lv', lvn = doLvalue lv false in
      (* We are reading from it, so mark it as referenced *)
      setReferenced lvn (default_why ());
      Lval lv', lvn.N.btype, nodeOfType lvn.N.btype

  | AddrOf (lv) -> 
      (* Maybe we are taking the address of a function *)
      let lv1 = 
        match lv with 
          Var v, NoOffset when isFunctionType v.vtype -> 
            let newvi, ispoly = Poly.instantiatePolyFunc v in
            (* If we did create a new instance, we must also process the new 
             * varinfo *)
            if ispoly then 
              doVarinfo newvi;
            Var newvi, NoOffset
        | _ -> lv
      in
      let lv', lvn = doLvalue lv1 false in
      markAddrOfLocal lv lvn;
      AddrOf (lv'), TPtr(lvn.N.btype, lvn.N.attr), lvn

  | StartOf lv -> 
      let lv', lvn = doLvalue lv false in
      let next = startOfNode lvn in
      markAddrOfLocal lv next;
      StartOf lv', TPtr(next.N.btype, next.N.attr), next

  | UnOp (uo, e, tres) -> (* tres is an arithmetic type *)
      UnOp(uo, doExpAndCast e tres, tres), tres, N.dummyNode

  | SizeOf (t) ->
      let t', _ = doType t (N.anonPlace()) 1 in
      checkSizeOfArgument t';
      SizeOf (t'), !typeOfSizeOf, N.dummyNode

  | SizeOfE (e) -> 
      let e', et', en' = doExp ~inSizeof:true e in
      SizeOfE(e'), !typeOfSizeOf , N.dummyNode

  | SizeOfStr (s) -> 
      e, !typeOfSizeOf, N.dummyNode

  | AlignOf (t) ->
      let t', _ = doType t (N.anonPlace()) 1 in
      checkSizeOfArgument t';
      AlignOf (t'), !typeOfSizeOf, N.dummyNode

  | AlignOfE (e) -> 
      let e', et', en' = doExp ~inSizeof:true e in
      AlignOfE(e'), !typeOfSizeOf , N.dummyNode

        (* pointer subtraction. do the subexpressions *)
  | BinOp (MinusPP, e1, e2, tres) -> 
      let e1', _, _ = doExp e1 in
      let e2', _, _ = doExp e2 in
      BinOp(MinusPP, e1', e2', tres), tres, N.dummyNode

        (* arithmetic binop. *)
  | BinOp (((PlusA|MinusA|Mult|Div|Mod|Shiftlt|Shiftrt|
             Lt|Gt|Le|Ge|Eq|Ne|BAnd|BXor|BOr|LAnd|LOr) as bop), 
           e1, e2, tres) -> 
             BinOp(bop, doExpAndCast e1 tres,
                   doExpAndCast e2 tres, tres), tres, N.dummyNode

       (* pointer arithmetic *)
  | BinOp (((PlusPI|MinusPI|IndexPI) as bop), e1, e2, tres) -> 
      let e1', e1t, e1n = doExp e1 in
      let sign = 
        signOf 
          (match bop with PlusPI|IndexPI -> e2 | _ -> UnOp(Neg, e2, intType)) 
      in
      (match sign with
        SLiteral z -> 
          if z < Int64.zero then setArith e1n (default_why ()) else
          if z > Int64.zero then setPosArith e1n (default_why ()) else
          ()

      | SPos -> setPosArith e1n (default_why ())

      | _ -> 
          if bop = IndexPI then (*  Was created from p[e] *)
             setPosArith e1n (default_why ())
          else 
             setArith e1n (default_why ()) );
      if sign = SLiteral Int64.zero then
        e1', e1t, e1n
      else
        BinOp (bop, e1', doExpAndCast e2 intType, e1t), e1t, e1n
      
      
  | CastE (newt, e) -> 
      let newt', _ = doType newt (N.anonPlace ()) 1 in
      CastE (newt', doExpAndCast e newt'), newt', nodeOfType newt'

  | Const (CStr s) as e -> 
      (* Add a cast in front of strings. This way we have a place where 
       * to attach a node. *)
      let newt', _ = doType charPtrType (N.anonPlace ()) 1 in
      CastE (newt', e), newt', nodeOfType newt'

  | Const (CWStr s) as e -> 
      (* Add a cast in front of strings. This way we have a place where 
       * to attach a node. *)
      let newt', _ = doType (TPtr(!wcharType, [])) (N.anonPlace ()) 1 in
      CastE (newt', e), newt', nodeOfType newt'

  | Const _ -> (e, typeOf e, N.dummyNode)



(* Do initializers. *)
and doInit (vi: varinfo) (i: init) (l: location) : init * typ = 

  (* Baseoff is the offset to the current compound *)
  let rec doOne (baseoff: offset) off (what: init) : init * typ = 
    let off' = addOffset off baseoff in
    match what with 
    | SingleInit ei -> begin
        (* Fake an assignment *)
        let lv', ei' = doSet (Var vi, off') ei l in
        SingleInit ei', typeOfLval lv'
    end
    | CompoundInit (t, initl) -> 
        let t', _ = doType t (N.anonPlace ()) 1 in
        let initl' = 
          foldLeftCompound 
            ~implicit:false
            ~doinit:(fun newoff what t acc -> 
                        let what', _ = doOne off' newoff what in
                        (newoff, what') :: acc)
            ~ct:t' ~initl:initl ~acc:[] in
        CompoundInit (t', List.rev initl'), t'

  in
  doOne NoOffset NoOffset i


and doSet (lv: lval) (e: exp) (l: location) : lval * exp = 
  let lv', lvn = doLvalue lv true in
      (* We are writing to it, so mark it as referenced *)
  setReferenced lvn (N.ProgramSyntax(l)) ; 
  (*      ignore (E.log "Setting lv=%a\n lvt=%a (ND=%d)\n" 
        d_plainlval lv' d_plaintype lvn.N.btype lvn.N.id);  *)
  let e' = doExpAndCast e lvn.N.btype in
      (* sg: If assigning thru a pointer or to a global, mark adresses in e' 
      * as pkEscape. The former is a conservative approximation since 
      * depending on where lv can point, the value may probably not escape *)
  (match lv' with
    Mem _, _ -> expMarkEscape e' (* thru a pointer *)
  | Var vi, _ -> 
      if vi.vglob then expMarkEscape e' else () ); (* to a global *)
      
  lv', e'

and expMarkEscape (e : exp) : unit = 
	(*ignore (printf "--%a--\n" d_plainexp e); *)
  match e with 
    
    Lval lv -> 	
      let lvnode = nodeOfType (typeOfLval lv) (*get node for lv*)
      in setEscape lvnode (default_why ())
        
  | StartOf lv -> 
      let lvnode = (* like typeOf, but keeps attrs of arrays *)
	(match unrollType (typeOfLval lv) with
	  TArray (t,_,al) -> nodeOfType (TPtr(t, al))
	| _ -> E.s (E.bug "expMarkEscape: StartOf on a non-array") )
      in
      setEscape lvnode(default_why ())
        
  | AddrOf lv  -> 
      let _, alvnode = doLvalue lv false (* gets node for &lv *)
      in setEscape alvnode(default_why ())
        
  | CastE(_, e1)   -> expMarkEscape e1
  | UnOp((Neg|BNot), e1, _) -> expMarkEscape e1 
        
  | BinOp( (Lt|Gt|Le|Ge|Eq|Ne(*|LtP|GtP|LeP|GeP|EqP|NeP*)), _, _, _) -> ()
  | BinOp(_, e1, e2, _) -> expMarkEscape e1; expMarkEscape e2 
  | _ -> ()
        

(*      
  (* Baseoff is the offset to the current compound *)
  let rec initone (baseoff: offset) off what t acc = 
    let off' = addOffset off baseoff in
    match what with
        (* Just like in an assignment but ignore the statments *)
        let lv', lvn = doLvalue (Var vi, off') true in
        let ei' = doExpAndCast ei lvn.N.btype in

        mkStmt (Instr [Set ((Var vi, off'), ei, locUnknown)]) 
        :: acc
  in
  let inits = 
    initone NoOffset NoOffset init vi.vtype finit.sbody.bstmts in 

  match i with 
  | SingleInit e -> 
      let e', t, n = doExp e in
      if n != N.dummyNode then 
        E.s (bug "Found pointer initializer: %a\n" d_init i);
      SingleInit e', t
          
  | CompoundInit (t, initl) -> 
      let t', _ = doType t (N.anonPlace ()) 1 in
      if nodeOfType t' != N.dummyNode then
        E.s (bug "found pointer initializer: %a\n" d_init i);
        (* Construct a new initializer list *)
      let doOneInit (off: offset) (ei: init) (tei: typ) acc = 
        let ei', _ = doInit ei l in
        (off, ei') :: acc
      in
      let newinitl = 
        List.rev (foldLeftCompound ~doinit:doOneInit ~ct:t' 
                                   ~initl:initl ~acc:[]) in
      CompoundInit (t', newinitl), t'
*)
(* Do an lvalue. We assume conservatively that this is for the purpose of 
 * taking its address. Return a modifed lvalue and a node that stands for & 
 * lval. Just ignore the node and get its base type if you do not want to 
 * take the address of. *)
and doLvalue ((base, off) : lval) (iswrite: bool) : lval * N.node = 
  let base', startNode = 
    match base with 
      Var vi -> begin 
        (* ignore (E.log "doLval (before): %s: T=%a\n"
                  vi.vname d_plaintype vi.vtype); *)
        (* doVarinfo vi; It was done when the variable was declared !!! *)
        let vn = 
          match N.nodeOfAttrlist vi.vattr with Some n -> n | _ -> N.dummyNode
        in
        (* Now grab the node for it 
        ignore (E.log "doLval: %s: T=%a (ND=%d)\n"
                  vi.vname d_plaintype vi.vtype vn.N.id); 
*)
        base, vn
      end
    | Mem e -> 
        let e', et, ne = doExp e in
        if iswrite then
          setUpdated ne (default_why ());
        Mem e', ne
  in
  let newoff, newn = doOffset off startNode in
  (base', newoff), newn
        
(* Now do the offset. Base types are included in nodes. *)
and doOffset (off: offset) (n: N.node) : offset * N.node = 
  match off with 
    NoOffset -> off, n


  | Field(fi, resto) -> 
      (* We might need to change the fi in case we are in a polymorphic 
      * structure *)
      let fi' = 
        match unrollType n.N.btype with 
          TComp (nci, _) when nci != fi.fcomp -> 
            let fi' = 
              try 
                List.find (fun fi' -> fi'.fname = fi.fname) nci.cfields
              with Not_found -> 
                E.s (bug "Cannot find field %s in instance %s (replacement for %s)\n"
                       fi.fname (compFullName nci) (compFullName fi.fcomp))
            in
            fi'
              
        | _ -> fi
      in
      let nextn = fieldOfNode n fi' in
      let newo, newn = doOffset resto nextn in
      Field(fi', newo), newn

  | Index(e, resto) -> begin
      let nextn = startOfNode n in
      setPosArith nextn (default_why ()) ;
      let newo, newn = doOffset resto nextn in
      let e', et, _ = doExp e in
      Index(e', newo), newn
  end


  
(* Now model an assignment of a processed expression into a type *)
and expToType (e,et,en) t (callid: int) : exp = 
  let debugExpToType = false (* !currentLoc.line = 24 *) in
  let etn = nodeOfType et in
  let destn  = nodeOfType t in
  if debugExpToType then 
    ignore (E.log "expToType e=%a (NS=%d) -> TD=%a (ND=%d)\n"
              d_plainexp e etn.N.id d_plaintype t destn.N.id); 
  match etn == N.dummyNode, destn == N.dummyNode with
    true, true -> e (* scalar -> scalar *)
  | false, true -> e (* Ignore casts of pointer to non-pointer *)
  | false, false -> (* pointer to pointer *)
(*
      if isZero e then begin
        let _ = N.addEdge etn destn N.ENull (Some !currentLoc) in 
        e
      end else begin *)
        if debugExpToType then
          ignore (E.log "Setting %a : %a -> %d\n"
                    d_plainexp e d_plaintype et destn.N.id); 
        let _ = N.addEdge etn destn (N.ECast N.EEK_cast) (Some !currentLoc) in 
        e

  | true, false -> (* scalar -> pointer *)
      (* Check for zero *)
      (if isZero e then
        () (* setNull destn *)
      else
        setIntCast destn (default_why ()));
      e
    
and doExpAndCast e t = 
  (* Get rid of cascades of casts of 0 *)
  let e' = if isZero e then zero else e in
  expToType (doExp e') t (-1)

and doExpAndCastCall e t callid = 
  (* Get rid of cascades of casts of 0 *)
  let e' = if isZero e then zero else e in
  expToType (doExp e') t callid





(*****************************************************************)


(* return the first few items of a list *)
let rec list_first l n = begin
  if n >= 0 then (List.hd l) :: (list_first (List.tl l) (n-1))
  else []
end


(* Some utility functions for decomposing a function call so that we can 
 * process them in a special way *)
type callArgDescr = 
    { caOrig: exp; (* The original actual, without the cast that was added to 
                    * match it with the formal type *)
      caOrigType: typ; (* Type of caOrig *)
      caOrigNode: N.node; (* The node corresponding to caOrigType, if TPtr *)
      caFormal: (string * typ * attributes);  (* The formal varinfo *)
      caFormalType: typ; (* The type of the corresponding formal *)
      caFormalNode: N.node; (* The node corrsponding to caFormalNode,if TPtr *)
    } 

let decomposeCall 
    (reso: lval option)
    (f: exp)
    (args: exp list) : (* result *) callArgDescr * 
                       (* args *) callArgDescr list = 
  (* Fetch the function type *)
  let rt, formals = 
    match unrollType (typeOf f) with
      TFun (rt, formals, _, _) -> rt, argsToList formals
    | _ -> E.s (E.bug "decomposingCall to a non-function")
  in
  if List.length formals <> List.length args then 
    E.s (E.bug "decomposeCall: mismatch of argument list length");
  (* A function to split a pointer type into base type, attribute and 
  * node of attributes *)
  let splitPtrType (t: typ) = 
    match unrollType t with
      TPtr(bt, a) -> begin
        bt, a, 
        (match N.nodeOfAttrlist a with
          Some n -> n
        | None -> N.dummyNode)
      end
    | _ -> voidType, [], N.dummyNode
  in
  let argDescr = 
    List.map2
      (fun a ((fn,ft,fa) as f) ->
        (* Get the types of the arguments. But be prepared to strip the top 
         * level cast since it could have been added by cabs2cil *)
        let orig = stripCasts a in
        let origt = typeOf orig in
        let orig_bt, orig_a, orig_n = splitPtrType origt in
        (* So the same for the formal *)
        let form_bt, form_a, form_n = splitPtrType ft in
        { caOrig = orig; caOrigType = origt; caOrigNode = orig_n;
          caFormal = f; caFormalType = ft; caFormalNode = form_n })
      args formals
  in
  (* Now the return type *)
  let rt_bt, rt_a, rt_n = splitPtrType rt in
  let resDescr = 
    match reso, rt with 
      None, TVoid _ -> 
        { caOrig = zero; caOrigType = voidType; caOrigNode = N.dummyNode;
          caFormal = ("", voidType, []); 
          caFormalType = voidType; caFormalNode = N.dummyNode }
    | None, _ -> { caOrig = zero; caOrigType = voidType; 
                   caOrigNode = N.dummyNode;
                   caFormal = ("", voidType, []); 
                   caFormalType = rt; caFormalNode = rt_n }
    | Some _, TVoid _ -> E.s (E.bug "decomposeCall: assigned subroutine")
    | Some lv, _ -> 
        let origt = typeOfLval lv in
        let orig_bt, orig_a, orig_n = splitPtrType origt in
        { caOrig = Lval (lv); caOrigType = origt; 
          caOrigNode = orig_n; caFormal = ("", voidType, []); 
          caFormalType = rt; caFormalNode = rt_n }
  in
  resDescr, argDescr


let rec doBlock blk = 
  if hasAttribute "nocure" blk.battrs then 
    blk
  else 
    { bstmts = List.map doStmt blk.bstmts; battrs = blk.battrs }

and doStmt (s: stmt) : stmt = 
  try
    (match s.skind with 
      Goto _ | Break _ | Continue _ -> ()
    | Return (None, _) -> ()
    | Return (Some e, l) -> 
        currentLoc := l;
        let e' = doExpAndCast e !currentResultType in
        (*sg:need to mark exp as escaped*)
        expMarkEscape e';
        s.skind <- Return (Some e', l)
    | Instr il -> 
        s.skind <- Instr (mapNoCopyList doInstr il)
    | Loop (b, l, lb1, lb2) -> 
        currentLoc := l;
        s.skind <- Loop (doBlock b, l, lb1, lb2)
    | Block b -> s.skind <- Block (doBlock b)
    | If(e, b1, b2, l) -> 
        currentLoc := l;
        s.skind <- If (doExpAndCast e intType, doBlock b1, doBlock b2, l)
    | Switch (e, b, cases, l) -> 
        currentLoc := l;
        s.skind <- Switch(doExpAndCast e intType, doBlock b, cases, l)
    | TryFinally (b, h, l) -> 
        currentLoc := l;
        s.skind <- TryFinally(doBlock b, doBlock h, l)
    | TryExcept (b, (il, e), h, l) -> 
        currentLoc := l;
        s.skind <- TryExcept(doBlock b, (mapNoCopyList doInstr il, 
                                         doExpAndCast e intType), 
                             doBlock h, l));

    s
  with e -> begin
    ignore (E.log "Markptr: statement error (%s) at %t\n" 
              (Printexc.to_string e) d_thisloc);
    E.hadErrors := true;
    s
  end

and doInstr (i:instr) : instr list = 
  try 
    match i with
    | Asm (attrs, tmpls, outs, ins, clob, l) -> 
        currentLoc := l;
        if !N.allowInlineAssembly then 
          ignore (warn "CCured cannot handle inline assembly soundly. Make sure you know what you are doing here!\n  Here are the instruction: %a" 
                    (docList ~sep:line text) tmpls)
        else
          E.s (error "You did not turn on the handling of inline assembly. \n Here are the instructions: %a" (docList ~sep:line text) tmpls);
        let outs' = 
          List.map
            (fun (i,n, o) -> 
              let o', lvn = doLvalue o true in
              setReferenced lvn (default_why ()); 
              (i,n, o'))
            outs 
        in
        let ins' = 
          List.map
            (fun (i,n, e) -> 
              let e', _, _ = doExp e in
              (i,n, e'))
            ins
        in
        [Asm(attrs, tmpls, outs', ins', clob, l)]

    | Set (lv, e,l) -> 
        currentLoc := l;
        let lv', e' = doSet lv e l in
        [Set(lv', e',l)]
          
    | Call (reso, orig_func, args, l) as i -> begin
        currentLoc := l;
        (match orig_func with
          Lval(Var vf, NoOffset) -> 
            if not (H.mem MU.calledFunctions vf.vname) then
              H.add MU.calledFunctions vf.vname vf
        | _ -> ());
        match interceptFunctionCalls i with
          Some il -> mapNoCopyList doInstr il
        | None -> doFunctionCall reso orig_func args l
    end
  with e -> begin
    ignore (E.log "Markptr: instruction error (%s) at %t\n" 
              (Printexc.to_string e) d_thisloc);
    E.hadErrors := true;
    [i]
  end


and interceptFunctionCalls = function
  | i -> None
      
and doFunctionCall 
    (reso: lval option)
    (orig_func: exp)
    (args: exp list) 
    (l: location) = 
  incr callId; (* A new call id *)
  (*      ignore (E.log "Call %a args: %a\n" 
                d_plainexp orig_func
                (docList (fun a -> d_plaintype () (typeOf a)))
  args); *)
  let func, ispoly = (* check and see if it is polymorphic *)
    match orig_func with
      (Lval(Var(v),NoOffset)) -> 
        let newvi, ispoly = Poly.instantiatePolyFunc v in
        newvi.vdecl <- !currentLoc; (*matth: give the variable a location
				      so that errors in doVarinfo make sense.*)
        doVarinfo newvi;

	(*See if this is a wrapper helper*)
	Wrappers.addFormalConstraints newvi;

        (* See if this is our friend the "__trusted_cast".  We don't look at
	 * __trusted_deepcast here, because we set no compatibility edges for
	 * that function. *)
        if Poly.stripPoly newvi.vname = "__trusted_cast" ||
           Poly.stripPoly newvi.vname = "trusted_cast" then begin
          match newvi.vtype with
            TFun((TPtr(TVoid _, ra) as rt), 
                 Some [ (an, TPtr(TVoid _, apa), aa) ], false, fa) -> begin
                   (* If the argument of trusted_cast is a scalar, then 
                    * change the type of trusted_cast to take a scalar 
                    * argument *)
                   match args with 
                     [ a ] -> begin
                       let at = typeOf (stripCasts a) in
                       match unrollType at with 
                         TInt _ | TEnum _ -> begin
                           newvi.vtype <- TFun(rt, 
                                               Some [(an, !upointType, aa)],
                                               false, fa)
                         end
                       | _ -> begin
                           (* Add a TCast edge *)
                           match N.nodeOfAttrlist apa, 
                                 N.nodeOfAttrlist ra with 
                             Some an, Some rn -> 
                               let e = N.addEdge an rn 
                                   (N.ESameKind N.EEK_trustedCast) (Some l) in
                               e.N.eloc <- l
                           | _, _ -> 
                               E.s (bug "Cannot find nodes in type of __trusted_cast")
                       end
                     end
                   | _ -> E.s (bug "Wrong number of arguments in call to trusted_cast")
                 end
          | tau -> E.s (bug "Unexpected type %a for __trusted_cast\n" d_type tau )
        end;
        if ispoly then begin
          Lval (Var newvi, NoOffset), true
        end else (* Not polymorphic *) orig_func, false
    | _ -> orig_func, false
  in
  (* Do the function as if we were to take its address *)
  let (pfunc, pfunct, pfuncn) = 
    match func with 
      Lval lv -> doExp (mkAddrOf lv)
    | _ -> E.s (unimp "Called function is not an lvalue")
  in
  (* Now fetch out the real function and its type. We must do this after we 
   * process the function itself because it may be an expression. *)
  let func' = Lval (mkMem pfunc NoOffset) in
  let (rt, formals, isva, noProto) = 
    match unrollType (typeOf func') with
      TFun(rt, formals, isva, a) -> 
        rt, argsToList formals, isva, hasAttribute "missingproto" a
    | _ -> E.s (bug "Call to a non-function")
  in
  let preinstr, args' = 
    if isva then 
      (* This might add prototypes to MU.theFile *)
      Vararg.prepareVarargArguments 
        (fun t -> 
          let vi = makeTempVar !MU.currentFunction t in 
          doVarinfo vi;
          vi) 
        func' (List.length formals) args
    else
      [], args
  in
  (* If the function has more actual arguments than formals then mark 
  * the function node as used without prototype  *)
  let make_it_wild = 
    if not isva && (noProto ||
                    List.length args' <> List.length formals) then 
      begin
	(* Bark if it is polymorphic. No prototype + polymorphism (or 
	 * allocation) do not work together *)
	if ispoly then 
          E.s (error "Calling polymorphic (or allocation) function %a without proper prototype, or with the wrong number of arguments." 
		 d_exp func)
	else if noProto then 
     	  ignore (warn "Calling function %a without proper prototype: will be WILD.\n  %a has type %a"
                    d_exp func 
                    d_exp func 
		    d_type (unrollType (typeOf func')) )
	else
	  ignore (warn "Calling function %a with %d arguments when expecting %d: will be WILD.\n  %a has type %a"
                    d_exp func (List.length args') (List.length formals)
                    d_exp func d_type (unrollType (typeOf func')) ) ;
	setNoProto pfuncn (default_why ());
	true
      end 
    else false
  in
  (* Now check the arguments *)
  let rec loopArgs formals args = 
    match formals, args with
      [], [] -> []
    | [], a :: args -> 
        (* We ran out of formals. This is either in a vararg functions or 
         * else this is bad, so we make sure to mark that the argument is 
         * used in a function without prototypes *)
        (* Do the arguments because they might contain pointer types *)
        let a', _, an = doExp a in
        if an != N.dummyNode && not isva  then
          setNoProto an (default_why ()) ;
        a' :: loopArgs [] args
                
    | (_, ft, _) :: formals, a :: args -> 
        (* See if this is a polymorphic argument. Then strip the cast to 
         * void* *)
        let a' = 
          match ispoly, unrollType ft with
            true, TPtr(TVoid _, _) -> true
          | _, _ -> false
        in
        (*            ignore (E.log "Call arg %a: %a -> %s\n" 
                      d_exp a' d_plaintype (typeOf a') fo.vname); *)
        let a' = doExpAndCastCall a ft !callId in
        a' :: loopArgs formals args
                
    | _, _ -> E.s (E.unimp "Markptr: not enough arguments in call to %a" 
                     d_exp orig_func)
  in  
  (* Now scan the arguments again and add EArgs edges *)
  (* Now do the arguments *)
  let args'' = loopArgs formals args' in
  List.iter (fun a' -> 
    let a'n = nodeOfType (typeOf a') in
    if a'n != N.dummyNode then 
      ignore(N.addEdge pfuncn a'n N.EArgs (Some l))) args'';

  let reso' = 
    (* Now check the return value*)
    match reso, unrollType rt with
      None, TVoid _ -> None
    | Some _, TVoid _ -> 
        ignore (warn "void value is assigned.");
        None

    | None, _ -> None (* "Call of function is not assigned" *)
    | Some dest, _ -> begin
        (* Do the lvalue, just so that the type is done *)
        let dest', lvn = doLvalue dest true in
        setReferenced lvn (default_why ()); 

        (* Add the cast from the return type to the destination of the call. 
         * Make up a phony expression and a node so that we can call 
         * expToType.  *)
(*
        ignore (E.log "Call to %a. \n\trt=%a\n\ttypeOFLval(dest') = %a\n"
                  d_exp func' d_type rt d_plaintype (typeOfLval dest'));
*)
        let dest't = typeOfLval dest' in
        (* Also add an EArgs edge *)
        let dest'n = nodeOfType dest't  in
        if dest'n != N.dummyNode then 
          ignore(N.addEdge pfuncn dest'n N.EArgs (Some l));
        (* For allocation functions do not connect the returned value to the 
         * result because the returned value is an integer *)
        (match func' with 
          Lval(Var f, NoOffset) 
            when H.mem allocFunctions (Poly.stripPoly f.vname) -> ()
        | _ -> 
            ignore (expToType (mkString ("a call return"),
                               rt, N.dummyNode) dest't 
                      !callId));
        Some dest'
    end 
  in
  (* We need to mark all instructions that we have generated *)
  let preinstr' = mapNoCopyList doInstr preinstr in
  preinstr' @ [Call(reso', func', args'', l)]


let doFunctionBody (fdec: fundec) = 
  MU.currentFunction := fdec;
  (* See if this is a vararg function. Must do this first because we might 
   * change a lot of temporaries, which we want to process *)
  Vararg.processVarargBody fdec;
  (* Go through the formals and copy their type and attributes from 
  * the type of the function. Then add the nodes for the address of the 
  * formals. Then restore the sharing with the function type. *)
  let rt, targs, isva, fa = splitFunctionTypeVI fdec.svar in
  let rec scanFormals targs sformals = 
    match targs, sformals with
      [], [] -> ()
    | (tan, tat, taa) :: targs, sf :: sformals -> 
        sf.vtype <- tat;
        let n = 
          N.getNode (N.PLocal(!currentFile.fileName, 
                              !MU.currentFunction.svar.vname, tan))
            0 tat taa in
        sf.vattr <- addAttributes taa n.N.attr;
        scanFormals targs sformals
    | _ -> E.s (bug "scanFormals(%s) non-matching formal lists"
                  fdec.svar.vname)
  in
  scanFormals (argsToList targs) fdec.sformals;
  (* Restore the sharing by writing the type *)
  setFormals fdec fdec.sformals;
  currentResultType := rt;
  (* Do the other locals *)
  List.iter doVarinfo fdec.slocals;
  (* Do the body *)
  fdec.sbody <- doBlock fdec.sbody


  
(* Now do the globals *)
let doGlobal (g: global) : global = 
  try
    match g with
    | GPragma (a, l) as g -> begin
        (* Most of the pragmas have been processed. Only a few have to be 
        * processed at the same time with the other globals *)
        currentLoc := l;
        (match a with
        | Attr("ccured", [ACons("on", _)]) -> boxing := true
        | Attr("ccured", [ACons("off", _)]) -> boxing := false
        | _ -> ());
        g
    end
    | GText _ | GAsm _ | GEnumTag _ | GCompTagDecl _ | GEnumTagDecl _ -> g
              
              (* We process here only those types that we must not unroll. 
               * The others we'll process as we see them used.*)
    | GType (t, l) when !boxing -> 
        currentLoc := l;
        (* See if we have the "nounroll" attribute *)
        if hasAttribute "nounroll" (typeAttrs t.ttype) then 
          H.add dontUnrollTypes t.tname true;
        if not (mustUnrollTypeInfo t) then begin
          let t', _ = doType t.ttype (N.PType t.tname) 1 in
          t.ttype <- t';
          g
        end else 
          if !N.printVerboseOutput then 
            GText ("// Definition of unrolled type "^t.tname^" was removed")
          else
            GText ("//")
              
    | GCompTag (comp, l) when !boxing -> 
        currentLoc := l;
        if not (Poly.isPolyComp comp) then begin
          markCompInfo comp l;
          g
        end else begin
          (* It is polymorphic, so nobody should be using this copy 
          * anymore *)
          if !N.printVerboseOutput then
            GText("// definition of polymorphic struct " ^ comp.cname ^ 
                  " used to be here")
          else
            GText("//")
        end
            
    | GVarDecl (vi, l) when !boxing -> 
        currentLoc := l;
        (* ignore (E.log "Found GVarDecl of %s. T=%a\n" vi.vname
                    d_plaintype vi.vtype); *)
        let ispoly = Poly.isPolyFunc vi in
        if not ispoly then doVarinfo vi; 
        if not ispoly then 
          g
        else
          if !N.printVerboseOutput then 
            GText ("// declaration of polymorphic " ^ vi.vname^" dropped")
          else
            GText ("//")
              
    | GVar (vi, init, l) when !boxing -> 
        currentLoc := l;
        doVarinfo vi; 
        (match init.init with
          None -> ()
        | Some i -> 
            let i', _ = doInit vi i l in
            init.init <- Some i');
        g
              
    | GFun (fdec, l) when !boxing ->
        currentLoc := l;
        let dobox = not (hasAttribute "nocure" fdec.svar.vattr) in
        if dobox then begin
          (* If it is polymorphic then remember it for later. *)
          if Poly.isPolyFunc fdec.svar then begin
            Poly.rememberFunctionDefinition fdec 
          end else begin
            doVarinfo fdec.svar;
            doFunctionBody fdec;
            g
          end
        end else
          g
            
            
    | g -> 
        if not !boxing then g else 
        E.s (bug "Unmatched clause in markPtr::doGlobal")


  with e -> begin
    (* Try to describe the global *)
    ignore (E.log "Markptr: global error (%s) on %a at %t\n" 
              (Printexc.to_string e) d_shortglobal g d_thisloc);
    E.hadErrors := true;
    g
  end


(********************************************************)

      
(* Now do the file *)      
let markFile fl = 
  if not !noStackOverflowChecks then 
    Stackoverflow.addCheck fl;
  currentFile := fl;
  boxing := true;
(*  disableModelCheck := false; *)
  E.hadErrors := false;

  (* Handle dependent types *)
  Dependent.doit fl;
  Depfunc.doit fl;

  Poly.initFile ();
  Taggedunion.init ();
  
  MU.init();
  N.initialize ();
  H.clear mustRecomputePointsTo;
  H.clear markedCompInfos;
  (* Add some prototypes *)
  Vararg.initFile ();
  Vararg.pMarkField := (fun f -> ignore (doField f));
  Wrappers.initFile ();
  addAlloca ();
  H.clear dontUnrollTypes;
  H.clear allocFunctions;

  Taggedunion.processTaggedUnions fl;


  (* Registers the function declarations and definitions. We must do this 
   * before looking at the rest of the program to ensure that we can process 
   * the pragmas related to functions even before we see the definition or 
   * the declaration of the function itself. *)  
  let registerFunctions = function
      GPragma ((Attr(an, _) as a), l) -> 
        currentLoc := l;
        (* Watch for obsolete pragmas *)
        (match an with
           "boxvararg" | "boxvararg_printf" | "boxmodelof"
         | "boxpoly" | "ccuredwrapperof" | "boxalloc" | "nobox" | "box"
             -> E.s (error "Pragma %s is not legal anymore" an)
         | _ -> ());
        Wrappers.processPragma a;
        MU.processPragma a l

    | GFun(fdec, l) -> 
        currentLoc := l;
        (* Build the list of functions *)
        MU.registerFunction (MU.Defined fdec);
        MU.registerGlobalDefinition fdec.svar l

    | GType (ti, l) -> 
        currentLoc := l;
        MU.registerTypeinfo ti

    | GCompTag (ci, l) -> 
        currentLoc := l;
        MU.registerCompinfo ci l

    | GVarDecl (vi, l) -> begin
        currentLoc := l;
        MU.registerGlobalDeclaration vi;
        (* See if this is a function that is not yet defined *)
        match unrollType vi.vtype with
          TFun _ when not (H.mem MU.allFunctions vi.vname) -> 
            MU.registerFunction (MU.Declared vi)
        | _ -> ()
    end

    | GVar (vi, _, l) -> 
        currentLoc := l;
        MU.registerGlobalDefinition vi l

    | _ -> ()
  in
  
  iterGlobals fl registerFunctions;
  
  (* Once we have registered the functions, we can process the other pragmas. 
   *)
  let processOtherPragmas = function
    | GPragma (a, l) as g -> begin
        currentLoc := l;
        (match a with
        | Attr("ccuredalloc", AStr(s) :: _) -> 
            (* Set the return type of an allocator to be integer so that we 
             * do not have problems when we box the type *)
            MU.applyToFunction s
              (fun vi -> 
                let rt, args, isva, al = splitFunctionType vi.vtype in
                H.add allocFunctions vi.vname ();
                vi.vtype <- TFun(!upointType, args, isva, al));
            (* Allocators are polymorphic *)
            Poly.processPragma a

        | Attr("ccurednounroll", [AStr s]) ->
            H.add dontUnrollTypes s true

        | Attr("ccuredleavealone", funcs) ->
            List.iter 
              (function (AStr s) -> 
                (* Make nocure functions polymorphic *)
                Poly.processPragma a;
                if MU.alreadyDefinedFunction s then
                  ignore 
                    (warn "#pragma ccuredleavealone appears after definition of %s\n" s)
                else begin
                  MU.applyToFunction s
                    (fun vi -> 
                      vi.vattr <- addAttribute (Attr("nocure",[])) vi.vattr);
                end
                | _ -> ignore (warn "Invalid #pragma ccuredleavealone"))
              funcs

        | _ -> Vararg.processPragma a;
               Poly.processPragma a);
	()
    end

    | g -> ()
  in
  iterGlobals fl processOtherPragmas;

  Wrappers.replaceWrappers fl;

  (* This is where we process all the functions. *)
  ignore (E.log "before markptr\n");
  MU.theFile := [];
  List.iter (fun g -> let g' = doGlobal g in 
                      MU.theFile := g' :: !MU.theFile) fl.globals;

  (* Now we have to scan the nodes again. There might be some nodes whose 
   * type is pointer to TComp and which do not have any EPointsTo edges 
   * because the TComp was a forward reference. Now that should have been 
   * fixed, so try to regenerate the EPoints to edges *)
  H.iter 
    (fun _ n -> 
      (* ignore (E.log "Recomputing PointsTo for node %d\n" n.N.id); *)
      N.setNodePointsTo n)
    mustRecomputePointsTo;

  (* Now do the globinit *)
  let newglobinit = 
    match fl.globinit with
      None -> None
    | Some g -> begin
        match doGlobal (GFun(g, locUnknown)) with
          GFun (g', _) -> Some g'
        | _ -> E.s (bug "markptr: globinit")
    end
  in
  ignore (E.log "after markptr\n");

  (* Now we must create the copies for the polymorphic functions *)
  Poly.finishInstantiations 
    (fun f -> 
(*    ignore (E.log "Marking body of %s after instantiation\n" f.svar.vname);*)
      let g = doGlobal (GFun(f, locUnknown)) in
      (* Let's drop the cilnoremove things, so that the rmtmps can remove 
       * more things  *)
      (match g with 
        GPragma(Attr("cilnoremove", _), _) -> ()
      | _ -> 
          MU.theFile :=  g :: !MU.theFile));
  ignore (E.log "after creating the polymorphic instantiations\n");


  (* Now we add to the globals the automatically generated descriptors *)
  Vararg.addToFileAutoDescr ();

  let newglobals = List.rev !MU.theFile in

  (* Now, after we have added the nodes we fix the overrides *)
  if !Cilutil.doCxxPP then 
    Markcxx.fixOverrides ();

     
  (* Now we must go through the extends hierachy and add ECast edges as 
   * appropriate *)
  if !E.verboseFlag then 
    MU.dumpExtensionHierarchy();
  List.iter 
    (fun (child, parent, loc) -> 
      (* Manufacture two pointers *)
      let p_child, _ = doType (TPtr(child, [])) (N.anonPlace ()) 1 in
      let p_parent, _ = doType (TPtr(parent, [])) (N.anonPlace ()) 1 in
      (* Add the ECast edge *)
      match nodeOfType p_child, nodeOfType p_parent with 
        n_child, n_parent 
          when n_child != N.dummyNode && n_parent != N.dummyNode -> 
            ignore (N.addEdge n_child n_parent 
                      (N.ECast N.EEK_extends) (Some loc))
      | _, _ -> E.s (bug "markptr: extends relationship"))
    (MU.allExtendsRelationships ());
      

  let newfile = {fl with globals = newglobals; globinit = newglobinit} in

  (* Add a few more edges: *)
  Taggedunion.processTaggedUnionsAfterMarking newfile;

  if !Cilutil.doCheck then
    ignore (Check.checkFile [] newfile);

  if !E.verboseFlag || !E.hadErrors then (* But do not stop, we want to print 
                                          * the browser and the infer files *)
    ignore (E.log "Markptr: %s\n"
              (if !E.hadErrors then "Error" else "Success"));

  H.clear dontUnrollTypes;
  H.clear allocFunctions;
  H.clear mustRecomputePointsTo;
  H.clear markedCompInfos;
  (* MU.init (); Do not initialize, since we need this info in box.ml *)
  Vararg.initFile ();
  Poly.initFile ();
  currentFile := dummyFile;

  newfile



