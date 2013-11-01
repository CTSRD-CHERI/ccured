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
module IH = Inthash
module A = Alpha
module E = Errormsg
module N = Ptrnode
module MU = Markutil
module CC = Curechecks

let showGlobals = false
let debugInstr = false

let debugVI: (string, varinfo) H.t = H.create 7

let log (fmt : ('a,unit,doc,unit) format4) : 'a =
  E.log ("%a: Cure.ml: " ^^ fmt) d_loc !currentLoc

let noUnrefPointerChecks = ref false

let compactBlocks = true

let suppressWrapperWarnings = ref false

let showMangleReasons = ref false

(* Remember names that we have already mangled. Use also for "struct foo" and
 * such. Store the old name and the suffix. *)
let mangledNames : (string, (string * string)) H.t = H.create 123
let demangle name : string * string = (* Returns the old name, and suffix *)
  try H.find mangledNames name
  with Not_found -> name, ""


let lu = locUnknown
let isSome = function Some _ -> true | _ -> false

(* Have a loop constructor that yields nothing if the body is empty *)
let mkForIncrOptim ~iter:(iter:varinfo) ~first:(first: exp)
                   ~past:(past: exp) ~incr:(incr: exp)
                   ~body:(body: stmt list) : stmt list =
  if body = [] then []
  else mkForIncr iter first past incr body

(* How are we using an lval? *)
type forAccess =
    ForWrite  (* As an lvalue *)
  | ForRead   (* As an rvalue *)
  | NoAccess  (* In an AddrOf or Sizeof *)

(**** Stuff that we use while converting to new CIL *)
let mkSet (lv:lval) (e: exp) : stmt
    = mkStmtOneInstr (Set(lv, e, !currentLoc))
let call lvo f args : stmt = mkStmtOneInstr (Call(lvo,f,args, !currentLoc))
let mkAsm attrs tmpls outputs inputs clobs =
  mkStmtOneInstr (Asm(attrs, tmpls, outputs, inputs, clobs, !currentLoc))

let rec dropCasts (e: exp) : exp =
  match e with
    CastE (_, e) -> dropCasts e
  | _ -> e

(*** End stuff for old CIL *)


(**** Pointer representation ****)

(* Kinds of metadata *)
type mkind =
  | MKBase (* the base *)
  | MKEnd  (* The end *)
  | MKRtti
  | MKMetaPointer

let d_mkind () = function
  | MKBase -> text "Base"
  | MKEnd -> text "End"
  | MKRtti -> text "Rtti"
  | MKMetaPointer -> text "Meta"

(** Each metadata kind is stored in a field with a certain name. Keep the
 * two-way mapping between these *)

(* For each metadata kinds we store the name of the field and its type *)
let fieldOfMK = function
  | MKBase -> "_b", voidPtrType
  | MKEnd -> "_e", voidPtrType
  | MKRtti -> "_t", MU.rttiType
  | MKMetaPointer -> "_mp", voidPtrType (* Will fix this type when we make
                                         * the field *)

let mkOfField = function
  | "_b" -> MKBase
  | "_e" -> MKEnd
  | "_t" -> MKRtti
  | "_mp" -> MKMetaPointer
  | fn -> E.s (bug "mkOfField: not a metadata field: %s\n" fn)


(* Check if a certain kind has certain metadata *)
let pkHas (mk: mkind) (k: N.opointerkind) : bool =
  match mk, k with
  | MKBase, (N.Seq | N.SeqR | N.SeqC | N.SeqRC | N.SeqN | N.SeqNC
             | N.Wild | N.Index) -> true
  | MKEnd, (N.FSeq | N.FSeqC | N.FSeqR | N.FSeqRC | N.FSeqN | N.FSeqNC
            | N.Seq | N.SeqC | N.SeqR | N.SeqRC | N.SeqN | N.SeqNC) -> true
  | MKRtti, (N.Rtti | N.SeqR | N.FSeqR
             | N.RttiC | N.SeqRC | N.FSeqRC) -> true
  | MKMetaPointer, (N.SafeC | N.FSeqC | N.SeqC
                    | N.RttiC| N.FSeqRC | N.SeqRC) -> true
  | _, _ -> false

        (* The order of the fields is very important, because it must match
         * the code in the library. *)
let mkOrder = [MKBase; MKEnd; MKRtti; MKMetaPointer]

(* For each pointer kind, store a list of the metadata that it needs, in the
 * right order. *)
let pkFields: (N.opointerkind, mkind list) H.t =
  let pkFields = H.create 15 in
  (* Initialize the pkFields with all empty *)
  List.iter (fun k -> H.add pkFields k []) N.allKinds;
  (* Now fill in the pkFields hash table, in the specified order *)
  List.iter
    (fun mk ->
      (* For each metadata kind add it to the pointers that need it *)
      List.iter
        (fun k ->
          if pkHas mk k then begin
            H.replace pkFields k (H.find pkFields k @ [mk])
          end) N.allKinds)
    mkOrder;
  pkFields

let pkHasMeta (k: N.opointerkind) : bool = [] != H.find pkFields k

let pkIsWild  (k: N.opointerkind) : bool =
  k = N.Wild || k = N.WildT || k = N.WildC

(* We cure an expression and we store it in the following form *)
type cureexp =
    { et: typ; (* The type of the whole cureexp *)
      ep: exp; (* This is the main expression. For a non-pointer it is THE
                * expression. For a pointer it is the _p component *)
      ek: N.opointerkind; (* The kind of this pointer. This is always the
                           * result of kindOfType et  *)
      em: expmeta; (* The meta data for the value, corresponding to the ek *)
    }

(* Metadata for a cureexp. *)
and expmeta = { _b: exp option; (* A base *)
                _e: exp option; (* An end *)
                _t: exp option; (* A RTTI *)
                _mp: exp option (* A pointer to metadata for pointed-to obj *)
              }

let emNone : expmeta = { _b = None; _e = None; _t = None; _mp = None}
let emMeta (m: exp) : expmeta = { emNone with _mp = Some m}
let emEnd (e: exp) : expmeta = { emNone with _e = Some e}
let emBaseEnd (b: exp) (e: exp) : expmeta =
  {emNone with _b = Some b; _e = Some e}
let emBase (b: exp) : expmeta =
  {emNone with _b = Some b}
let emRtti (t: exp) : expmeta =
  {emNone with _t = Some t}
let emRttiMeta (t: exp) (m: exp) : expmeta =
  {emNone with _t = Some t; _mp = Some m}
let emEndMeta (e: exp) (m: exp) : expmeta =
  {emNone with _e = Some e; _mp = Some m}
let emBaseEndMeta (b: exp) (e: exp) (m: exp): expmeta =
  {emNone with _b = Some b; _e = Some e; _mp = Some m}
let emBaseMeta (b: exp) (m: exp): expmeta =
  {emNone with _b = Some b; _mp = Some m}

let d_expmeta () (em: expmeta) =
  let fields: doc list =
    List.fold_left
      (fun acc (fld, whato) ->
        match whato with
          None -> acc
        | Some e -> (dprintf "%s=%a" fld d_exp e) :: acc)
      []
      [("_b", em._b); ("_e", em._e); ("_t", em._t); ("_mp", em._mp)]
  in
  if fields = [] then
    nil
  else
    (docList ~sep:(chr ',' ++ break) (fun x -> x)) () fields

let emHas (mk: mkind) (em: expmeta) : bool =
  match mk, em with
  | MKBase, { _b = Some _} -> true
  | MKEnd, { _e = Some _} -> true
  | MKRtti, { _t = Some _} -> true
  | MKMetaPointer, { _mp = Some _} -> true
  | _, _ -> false

let emGet (mk: mkind) (where: string) (em: expmeta) : exp =
  match mk, em with
  | MKBase, { _b = Some b} -> b
  | MKEnd, { _e = Some e} -> e
  | MKRtti, { _t = Some t} -> t
  | MKMetaPointer, { _mp = Some mp} -> mp
  | _, _ -> E.s (bug "emGet(%a): %s em=%a" d_mkind mk where d_expmeta em)

let emSet (mk: mkind) (em: expmeta) (what: exp) : expmeta =
  match mk with
  | MKBase -> {em with _b = Some what}
  | MKEnd -> {em with _e = Some what}
  | MKRtti -> {em with _t = Some what}
  | MKMetaPointer -> {em with _mp = Some what}

let emClear (mk: mkind) (em: expmeta) : expmeta =
  match mk with
  | MKBase -> {em with _b = None}
  | MKEnd -> {em with _e = None}
  | MKRtti -> {em with _t = None}
  | MKMetaPointer -> {em with _mp = None}

let emCopy (mk: mkind) (emto: expmeta) (emfrom: expmeta) : expmeta =
  if emHas mk emfrom then
    emSet mk emto (emGet mk "emCopy" emfrom)
  else
    emClear mk emto

let checkExpMeta (em: expmeta) (k: N.opointerkind) : bool =
  (* For each of the metadata that the pointer kind demands, make sure that
   * we have it *)
  List.iter
    (fun mk ->
      if pkHas mk k && not (emHas mk em) then
        E.s (bug "missing metadata %a from %a"
               d_mkind mk d_expmeta em))
    mkOrder;
  true

let d_cureexp () (ce: cureexp) =
  dprintf "CE(@[P=%a,@?M=%a%a@])\n"
    d_exp ce.ep N.d_opointerkind ce.ek d_expmeta ce.em


let emHasMetaPtr (em: expmeta) : bool = em._mp != None

let emGetMetaPtr (em: expmeta) : exp =
  match em._mp with
    None -> E.s (bug "emGetMetaPtr: no metadata pointer available")
  | Some e -> e

let emStripMetaPtr (em: expmeta) : expmeta = {em with _mp = None }

let emSetMetaPtr (em: expmeta) (m: exp) : expmeta = {em with _mp = Some m}


(* We cure lvals in preparation for taking their address. We keep the lval
 * itself and its type (not the type of its address), the metadata of pointer
 * TO THE lval, and the kind of the pointer TO THE lval (if we
 * actually take the address of the lval). The base and end fields might not
 * be used for certain pointer kinds  *)
type curelval =
    { lv: lval;
      lvt: typ; (* typeOfLval(lv) *)
      lvm: expmeta; (* The metadata for the address of lval. This would be
                     * for example the begining and the end of the home area
                     * containing lval *)
      plvk: N.opointerkind; (* The kind of pointer to this lval that we
                             * should create *)
}

let d_curelval () (lv: curelval) : doc =
  dprintf "(LV=%a,LVT=%a,M=%a%a)"
    d_lval lv.lv
    d_type lv.lvt
    N.d_opointerkind lv.plvk
    d_expmeta lv.lvm

let nodeOfType (t: typ) (what: exp) =
  match N.nodeOfAttrlist (typeAttrs t) with
    Some n -> n
  | None ->
      ignore (warn "Cannot find the node of written %a\n" d_exp what);
      N.dummyNode

let isUnrefPointer (t: typ) =
  let a = typeAttrs t in
  (match N.nodeOfAttrlist a with
    None -> (*ignore (warn "Checking isUnref on pointer without a node\n");
            ignore (E.log " T=%a\n" d_plaintype t);
            ignore (E.log " A=%a\n" d_attrlist a); *)
            false
  | Some n ->
      (* ignore (E.log "Reading pointer %d\n" n.N.id); *)
      not (N.hasFlag n N.pkReferenced))

(* This test determines whether a function should be called as a compat
 * function--that is, when calling this function, we'll take advantage
 * of the compatible representation and call it directly, sans wrapper. *)
let isCompatFunction (e: exp) : bool =
  match e with
    Lval (Var v, NoOffset) -> hasAttribute "compat" v.vattr
  | _ -> false

let extraGlobInit : stmt clist ref = ref empty

(* For each local that is moved to the heap we keep the field of the heap
 * structure where it lives *)
let heapifiedLocals: (string, lval) H.t = H.create 7

(* Expresssions denoting the things to free at the end of the function *)
let heapifiedFree: stmt list ref = ref []

(* After processing an expression, we create its type, a list of
 * instructions that should be executed before this exp is used,
 * and a replacement exp *)
type expRes =
    typ * stmt clist * exp

type allocInfo = {
  mutable aiZeros: bool;              (* Whether the allocator initializes the
                                       * memory it allocates *)
  mutable aiGetSize: exp list -> exp; (* Extract the size argument out of a
                                       * list of arguments *)
  mutable aiNewSize: exp -> exp list -> exp list;
                                      (* Rewrite the argument list with a new
                                       * size *)
}

let allocFunctions : (string, allocInfo) H.t = H.create 13

(* Now a constructor of allocation information from ccuredalloc pragmas *)
let ccuredallocPragma (name: string) (args: attrparam list) : unit =
  let getArg n args =
    try List.nth args n
    with _ -> E.s (bug "no size arguments in call to allocator %s\n" name)
  in
  let replaceArg n what args =
    let rec loop n = function
        _ :: rest when n = 0 -> what :: rest
      | a :: rest when n > 0 -> a :: loop (n - 1) rest
      | _ -> E.s (bug "cannot replace size argument for allocator %s\n" name)
    in
    loop n args
  in
  (* Initialize like for malloc *)
  let ai =
    { aiZeros = false;
      aiGetSize = getArg 0;
      aiNewSize = replaceArg 0;
    }
  in
  let rec loop = function
      [] -> ()
    | ACons("nozero", _) :: rest -> ai.aiZeros <- false; loop rest
    | ACons("zero", _) :: rest -> ai.aiZeros <- true; loop rest
    | ACons("sizein", [AInt n]) :: rest ->
        ai.aiGetSize <- getArg (n - 1); ai.aiNewSize <- replaceArg (n - 1);
        loop rest
    | ACons("sizemul", [AInt n1; AInt n2]) :: rest ->
        ai.aiGetSize <-
           (fun args -> BinOp(Mult, getArg (n1 - 1) args, getArg (n2 - 1) args,
                              intType));
        ai.aiNewSize <-
           (fun what args ->
             (replaceArg (n1 - 1) one
                (replaceArg (n2 - 1) what args)));
        loop rest
    | ACons("sizenone", _) :: rest ->
        ai.aiGetSize <- (fun _ -> zero);
        ai.aiNewSize <- (fun _ args -> args);
        loop rest
    | a :: rest ->
        (ignore (warn "Don't understand ccuredalloc atrtibute: %a@!"
                   d_attrparam a));
        loop rest
  in
  loop args;
  (* Add to the hash *)
  H.add allocFunctions name ai

let getAllocInfo fname =
  try
    (* strip the pointer-kind suffix
     * (in case the user has an allocation function like realloc that takes
     *  a pointer as a formal argument.)
     *)
    let fname', _ = demangle fname in
    let fname'' = Poly.stripPoly fname' in
    (* Strip the alpha suffix as well *)
    let lookup = Alpha.getAlphaPrefix fname'' in
    (* ignore (E.log "Getting alloc info for %s\n" lookup); *)
    Some (H.find allocFunctions lookup)
  with _ -> None

let isAllocFunction name =
  isSome (getAllocInfo name)

(********************************************************************)

            (* Same for offsets *)
type offsetRes =
    typ * stmt clist * offset * exp * N.opointerkind

(*** Helpers *)
let castVoidStar e = mkCast e voidPtrType

let voidStarZero = castVoidStar zero

let prefix p s =
  let lp = String.length p in
  let ls = String.length s in
  lp <= ls && String.sub s 0 lp = p


  (* We collect here the new file *)
let theFile : global list ref = ref []
let consGlobal (x : global) l = x :: l

(**** Make new types ****)

(* For each new type name, keep track of various versions, usually due
 * to varying attributes *)
let typeNames : (string, location A.alphaTableData ref) H.t = H.create 17

let newTypeName (prefix: string) =
  fst (A.newAlphaName typeNames None prefix !currentLoc)

let rec newTypeNameFromType prefix t =
  let polyprefix, name = baseTypeName t in
  let n = polyprefix ^ prefix ^ name in
  newTypeName n

 (* Make a type name, for use in type defs *)
and baseTypeName = function
  | TNamed (t, _) -> "", t.tname
  | TBuiltin_va_list _ -> "", "__builtin_va_list"
  | TVoid(_) -> "", "void"
  | TInt(IInt,_) -> "", "int"
  | TInt(IUInt,_) -> "", "uint"
  | TInt(IShort,_) -> "", "short"
  | TInt(IUShort,_) -> "", "ushort"
  | TInt(IChar,_) -> "", "char"
  | TInt(IBool,_) -> "", "bool"
  | TInt(IUChar,_) -> "", "uchar"
  | TInt(ISChar,_) -> "", "schar"
  | TInt(ILong,_) -> "", "long"
  | TInt(IULong,_) -> "", "ulong"
  | TInt(ILongLong,_) -> "", "llong"
  | TInt(IULongLong,_) -> "", "ullong"
  | TFloat(FFloat,_) -> "", "float"
  | TFloat(FDouble,_) -> "", "double"
  | TFloat(FLongDouble,_) -> "", "ldouble"
  | TEnum (enum, _) -> "", "enum_" ^ enum.ename
  | TComp (comp, _) ->
      let su = if comp.cstruct then "s_" else "u_" in
      let prefix, name = Poly.splitPolyName comp.cname in
      prefix, su ^ name
  | TFun _ -> "", "fun"
  | TPtr(t, _) ->
      let polypref, name = baseTypeName t in
      polypref, "p_" ^ name
  | TArray(t, _, _) ->
      let polypref, name = baseTypeName t in
      polypref, "a_" ^ name

(**** Inspect the curing style attribute *)
let extractPointerTypeAttribute al =
  let k, why = N.kindOfAttrlist al in
  k

let extractArrayTypeAttribute al =
  filterAttributes "sized" al <> []

(**** Make new string names *)
let stringId = ref 0
let newStringName () =
  incr stringId;
  "__string" ^ (string_of_int !stringId)

let isNullTerm = function
    N.SeqN | N.FSeqN | N.SeqNT | N.FSeqNT | N.String | N.ROString -> true
  | _ -> false

(* sm: scan a list of strings for one element
 * (never know where to put this kind of stuff in ML) *)
let stringListContains (str:string) (sl:string list) : bool =
  List.exists (fun s -> s = str) sl

(***** Convert some pointers in types to fat pointers ************)
let sizedArrayTypes : (typsig, typ) H.t = H.create 123
(* We need to avoid generating multiple copies of the same tagged type
 * because we run into trouble if a variable is defined twice (once with
 * extern). *)
let taggedTypes: (typsig, typ) H.t = H.create 123
(**** FIXUP TYPE ***)
let fixedTypes : (typsig, typ) H.t = H.create 17

(* Search in the type attributes for the node and get from the node the type
 * qualifier. *)
(* matth: this used to drop "const" attributes as well, but the file and
   function arguments of ccured_fail have to be "char const *", since that's
   how __FILE__ and __FUNCTION__ are defined in newer versions of gcc. *)
let getNodeAttributes t =
  let dropit where a =
    N.replacePtrNodeAttrList where a
(*       (dropAttribute "const" a) *)
  in
  let rec loop t =
    match t with
      TVoid a -> TVoid (dropit N.AtOther a)
    | TInt (i, a) -> TInt (i, dropit N.AtOther a)
    | TFloat (f, a) -> TFloat (f, dropit N.AtOther a)
    | TNamed (t, a) ->
        let isptr =
          match unrollType t.ttype with TPtr _ -> N.AtPtr | _ -> N.AtOther
        in
        TNamed(t, dropit isptr a)
    | TPtr (t', a) -> TPtr(loop t', dropit N.AtPtr a)
    | TArray (t', (Some l as lo), a) ->
        let at = if isZero l && not (hasAttribute "size" a) &&
                                not (hasAttribute "count" a) then begin
          ignore (warn "Found open array");
          N.AtOpenArray
        end else N.AtArray in
        TArray(loop t', lo, dropit at a)

    | TArray (t', None, a) ->
        let at =
          if not (hasAttribute "size" a) &&
            not (hasAttribute "count" a) then begin
              ignore (warn "Found open array");
              N.AtOpenArray
            end else
             N.AtArray
        in
        TArray(loop t', None, dropit at a)

    | TComp (comp, a) -> TComp (comp, dropit N.AtOther a)
    | TEnum (enum, a) -> TEnum (enum, dropit N.AtOther a)
    | TFun (r, args, v, a) ->
        let args' =
          match args with
            None -> None
          | Some argl ->
              Some (List.map (fun (an,at,aa) ->
                                  (an, loop at, dropit N.AtOther aa)) argl)
        in
        TFun(loop r, args', v, dropit N.AtOther a)
    | TBuiltin_va_list a -> TBuiltin_va_list (dropit N.AtOther a)
  in
  loop t

(************* Metadata functions ***************)
let isMetaComp (comp: compinfo) =
  (comp.cstruct &&
   hasAttribute "metacomp" comp.cattr)

let isMetaType (t: typ) =
  match unrollType t with
    TComp (comp, _) when isMetaComp comp -> true
  | _ -> false

(*
let getFieldsOfMeta (t: typ)
    : (offset option) * (offset option) * (offset option) =
  let mkOffset (f: fieldinfo) : offset option =
    Some (Field (f, NoOffset))
  in
  match unrollType t with
    TComp (comp, _) when isMetaComp comp -> begin
      match List.filter (fun f -> f.fname <> "_z") comp.cfields with
      | a :: b :: c :: [] ->
          if a.fname = "_b" && b.fname = "_e" && c.fname = "_mp" then
            mkOffset a, mkOffset b, mkOffset c
          else
            E.s (bug "getFieldsOfMeta: unrecognized comp %a\n" d_type t)
      | a :: b :: [] ->
          if a.fname = "_e" && b.fname = "_mp" then
            None, mkOffset a, mkOffset b
          else if a.fname = "_b" && b.fname = "_e" then
            mkOffset a, mkOffset b, None
          else
            E.s (bug "getFieldsOfMeta: unrecognized comp %a\n" d_type t)
      | a :: [] ->
          if a.fname = "_e" then
            None, mkOffset a, None
          else if a.fname = "_b" then
            mkOffset a, None, None
          else if a.fname = "_mp" then
            None, None, mkOffset a
          else
            E.s (bug "getFieldsOfMeta: unrecognized comp %a\n" d_type t)
      | _ -> E.s (bug "getFieldsOfMeta")
    end
  | _ -> E.s (bug "getFieldsOfMeta %a\n" d_type t)
*)

(* Give a META type, return a list of metadata kinds stored in there along
 * with their fields *)
let getFieldsOfMeta (t: typ) : (mkind * offset) list =
  match unrollType t with
    TComp (comp, _) when isMetaComp comp -> begin
      (* Filter out the _z and _p field *)
      let fields =
        List.filter
          (fun f -> f.fname <> "_p" (*&& f.fname <> "_z"*))
          comp.cfields
      in
      List.map
        (fun f ->
          (* Find which metadata is stored in this field *)
          let mk = mkOfField f.fname in
          (mk, Field(f, NoOffset)))
        fields
    end
  | _ ->  E.s (bug "getFieldsOfMeta %a\n" d_type t)

let readFieldsOfMeta (t: typ) (m: lval) : expmeta =
  if isMetaType t then
    let metaFields = getFieldsOfMeta t in
    List.fold_left
      (fun (acc: expmeta) (mk, o) ->
        emSet mk acc (Lval (addOffsetLval o m)))
      emNone
      metaFields
  else
    { emNone with _mp = Some (Lval m) }

let setMetaPointer (t: typ) (em: expmeta) : stmt clist * lval =
  let tmp = makeTempVar !CC.currentFunction t in
  let metaFields = getFieldsOfMeta t in
  let instrs =
    List.fold_left
      (fun (acc: instr list) (mk, o) ->
        Set((Var tmp, o), emGet mk "setMetaPointer" em, !currentLoc) :: acc)
      []
      metaFields
  in
  (single (mkStmt (Instr instrs)),
   (Var tmp, NoOffset))

(***************** Handling of pointer qualifiers *****************)
let isFatComp (comp: compinfo) =
  (comp.cstruct && hasAttribute "mergecomp" comp.cattr)

let isFatPtrComp (comp: compinfo) =
  isFatComp comp &&
  (match comp.cfields with
     p :: _ when p.fname = "_p" -> true
   | _ -> false)

    (* Test if a type is FAT *)
let isFatType t =
  match unrollType t with
    TComp (comp, _) when isFatComp comp -> true
  | _ -> false

let getTypeOfFat (where: string) (t: typ) : typ =
  match unrollType t with
    TComp (comp, _) when isFatComp comp -> begin
      match comp.cfields with
        p :: _ -> p.ftype (* The p field is always the first *)
      | [] -> E.s (bug "getTypeOfFat (no fields): %s" where)
    end
  | _ -> E.s (bug "Expecting a FAT pointer type (%s).@!\tGot: %a\n"
                where d_type t)

(* Given a fat type, return the three fieldinfo corresponding to the ptr,
 * (optional) base, (optional) end, (optional) meta *)
let getFieldsOfFat (where: string) (t: typ) : offset * (mkind * offset) list =
  match unrollType t with
    TComp (comp, _) when isFatComp comp -> begin
      match comp.cfields with
      | p :: ms :: [] when p.fname = "_p" && ms.fname = "_ms" ->
          (Field(p, NoOffset)),
          (* Invoke the getFieldsOfMeta and then add a new offset *)
          (List.map
             (fun (mk, o) -> (mk, addOffset o (Field(ms, NoOffset))))
             (getFieldsOfMeta ms.ftype))

      | d :: md :: [] when d.fname = "_d" && md.fname = "_md" ->
          (Field(d, NoOffset)), [MKMetaPointer, (Field(md, NoOffset))]

      | p :: rest when p.fname = "_p" ->
          (Field(p, NoOffset)),
          (List.map
             (fun f ->
               (* Find which metadata is stored in this field *)
               let mk = mkOfField f.fname in
               (mk, Field(f, NoOffset)))
             rest)
      | _ -> E.s (bug "getFieldsOfFat (unexpected fields): %s" where)
    end
  | _ -> E.s (bug "getFieldsOfFat: no FAT type (%s).@!\tGot: %a\n"
                where d_type t)


let getOneFieldOfFat (where: string) (mk: mkind) (t: typ) : offset =
  let o, metaKinds = getFieldsOfFat where t in
  match List.filter (fun (mk', _) -> mk' = mk) metaKinds with
    [(_, o)] -> o
  | _ -> E.s (bug "getOneFieldOfFat(%a)" d_mkind mk)


let getFieldsOfMerge (t: typ) : offset * offset =
  match unrollType t with
    TComp (comp, _) when isFatComp comp -> begin
      match comp.cfields with
      | a :: b :: [] -> Field (a, NoOffset), Field (b, NoOffset)
      | _ -> E.s (bug "getFieldsOfMerge")
    end
  | _ -> E.s (bug "getFieldsOfMerge %a\n" d_type t)

(* Given an expression of a fat type, return three expressions, encoding the
 * pointer, the base and the end. Also return the type of the first
 * expression *)
let rec readFieldsOfFat (e: exp) (et: typ) : typ * exp * expmeta =
  if isFatType et then
    let pOff, metaFields = getFieldsOfFat "read fields" et in
    match e with
      Lval lv ->
        let em =
          List.fold_left
            (fun (acc: expmeta) (mk, o) ->
              emSet mk acc (Lval (addOffsetLval o lv)))
            emNone
            metaFields
        in
        (getTypeOfFat "read fields" et,
         Lval (addOffsetLval pOff lv),
         em)

    | _ -> E.s (unimp "readFieldsOfFat: %a" d_plainexp e)
  else
    (et, e, emNone)

(* Create a new temporary of a fat type and set its pointer and base
 * fields *)

let setFatPointer (t: typ) (ce: cureexp) : stmt clist * lval =
  let tmp = makeTempVar !CC.currentFunction t in
  let poff, metaoffs = getFieldsOfFat "setFatPointer" t in
  let setMetaInstrs: instr list =
    List.fold_right
      (fun (mk, off) acc ->
        let data = emGet mk "setFatPointer" ce.em in
        Set ((Var tmp, off), data, !currentLoc) :: acc)
      metaoffs
      []
  in
  single (mkStmt (Instr (Set ((Var tmp, poff), ce.ep, !currentLoc) ::
                         setMetaInstrs))),
  (Var tmp, NoOffset)

let readPtrField (e: exp) (t: typ) : exp =
  let (tptr, ptr, _) = readFieldsOfFat e t in ptr

let rec kindOfType t =
  (* Since t was fixed up, it has a qualifier if it is a pointer *)
  (* If it is a named type, look at the real type *)
  match t with
    TPtr (_, a) -> begin
      match extractPointerTypeAttribute a with
        N.Unknown -> if !N.defaultIsWild then N.Wild else N.Safe
      | res -> res
    end
  | TNamed (nt, _) -> kindOfType nt.ttype (* Ignore the attributes of the
                                           * TNamed *)
  | TComp (comp, _) when comp.cstruct -> begin
      match comp.cfields with
        p :: _ when p.fname = "_p" -> kindOfType p.ftype  (* A fat type *)
      | _ -> N.Scalar
  end
  | _ -> N.Scalar

let rec maybeStackPointer (what: exp) : bool =
 (* matth: Any casts on 'what' are probably casts to the lhs type.  We're
    interested in a property of the rhs value, so just delete the casts here.*)
  let what' = stripCasts what in
  let t = typeOf what' in
  if pkIsWild (kindOfType t) then
    true (*the flag doesn't work for wilds, for some reason.
           Maybe it isn't being propagated across bad casts? *)
  else match what' with
  (** Const and AddrOf expressions don't seem to have nodes.  So figure out
   ** their storage location manually, instead of using N.pkStack. *)
      Const _ ->
        false (* writing a NULL value, or some other scalar cast to a ptr *)
    | AddrOf (Var v, off)
    | StartOf (Var v, off) ->
        if v.vglob then
          false (* global var, including function pointers *)
        else
          true (* local var *)
    | AddrOf (Mem e, off)          (* e.g. the address of a field *)
    | StartOf (Mem e, off) ->      (* e.g. array access *)
        maybeStackPointer e  (* check the pointer to the start of the object *)
    | Lval (Var vi, off) when String.length vi.vname >= 11
        && String.sub vi.vname 0 11 = "__heapified" ->
        false
    | _ -> begin
        let a = typeAttrs t in
        match N.nodeOfAttrlist a with
            None ->
              ignore (warn
                        "[%a] Checking maybeStackPointer on pointer without a node: %a\n\n"
                        d_loc !currentLoc d_exp what');
              true (* conservative *)
          | Some n ->
              let b = N.hasFlag n N.pkStack in
(*               if b then ignore (E.log "[%a] %a [node %d] may point to the stack.\n  Type is %a\n\n" *)
(*                                   d_loc !currentLoc d_exp what n.N.id *)
(*                                   d_type t) *)
(*               else ignore (E.log "# [%a]  %a [node %d] does NOT point to the stack.\n" *)
(*                              d_loc !currentLoc d_exp what n.N.id); *)
              b
      end

(* Is the LHS of an assignment a local variable?  If so, skip the
   CHECK_STOREPTR check. *)
let isLocalVar lv : bool = match lv with
    Var vi, _ -> not vi.vglob
  | Mem e, _ -> false

let checkFetchIndexEnd tmplen ptr base (noint: bool) =
  call (Some (var tmplen)) (Lval (var CC.checkFetchIndexEndFun.svar))
    [ castVoidStar ptr;
      castVoidStar base;
      if noint then one else zero ]


let pkMakeScalarMeta (k: N.opointerkind) : expmeta =
  match k with
    N.Wild -> emBase voidStarZero
  | N.Index -> emBase voidStarZero
  | (N.FSeq|N.FSeqN) -> emEnd voidStarZero
  | (N.FSeqC|N.FSeqNC) -> emEndMeta voidStarZero voidStarZero
  | (N.Seq|N.SeqN) -> emBaseEnd voidStarZero voidStarZero
  | (N.SeqC|N.SeqNC) -> emBaseEndMeta voidStarZero voidStarZero voidStarZero
  | N.Safe -> emNone
  | N.SafeC -> emMeta voidStarZero
  | N.Rtti -> emRtti (MU.getScalarRtti ())
  | _ -> E.s (unimp "pkMakeNullMeta: offsetof for field of kind %a"
                N.d_opointerkind k)

(** The constructor for cureexp. Extracts the kind and the packages the
  * cureexp.*)
let mkCureexp (t: typ) (ep: exp) (em: expmeta) =
  let k = kindOfType t in
  (* In bytecode mode do some sanity checking *)
  assert (checkExpMeta em k);
  { et = t; ek = k; ep = ep; em = em }


let isZeroCureexp (ce: cureexp) = isZero ce.ep

let pkTypePrefix (pk: N.opointerkind) =
  match pk with
    N.Wild -> "wildp_"
  | N.FSeq | N.FSeqN -> "fseqp_"
  | N.Index -> "indexp_"
  | N.Seq | N.SeqN -> "seq_"
  | N.SafeC -> "safecp_"
  | N.WildC -> "wildcp_"
  | N.SeqC | N.SeqNC -> "seqcp_"
  | N.FSeqC | N.FSeqNC -> "fseqcp_"
  | N.Rtti -> "rtti_"
  | N.SeqR -> "seqrp_"
  | N.FSeqR -> "fseqrp_"
  | N.RttiC -> "rttic_"
  | N.SeqRC -> "seqrcp_"
  | N.FSeqRC -> "fseqrcp_"
  | _ -> E.s (bug "pkTypeName")

let pkQualName (pk: N.opointerkind)
               (acc: string list)
               (dobasetype: string list -> string list) : string list =
  if not (pkHasMeta pk) then dobasetype ("s" :: acc) else
  match pk with
  | N.Wild -> "w" :: acc (* Don't care about what it points to *)
  | N.Index -> dobasetype ("i" :: acc)
  | N.Seq -> dobasetype ("q" :: acc)
  | N.SeqN -> dobasetype ("Q" :: acc)
  | N.FSeq -> dobasetype ("f" :: acc)
  | N.FSeqN -> dobasetype ("F" :: acc)
  | N.SafeC -> dobasetype ("ms" :: acc)
  | N.WildC -> "mw" :: acc
  | N.SeqC -> dobasetype ("mq" :: acc)
  | N.SeqNC -> dobasetype ("mQ" :: acc)
  | N.SeqRC -> dobasetype ("mrq" :: acc)
  | N.FSeqC -> dobasetype ("mf" :: acc)
  | N.FSeqNC -> dobasetype ("mF" :: acc)
  | N.FSeqRC -> dobasetype ("mrf" :: acc)
  | N.Rtti -> dobasetype ("rs" :: acc)
  | N.RttiC -> dobasetype ("rms" :: acc)
  | N.FSeqR -> dobasetype ("rf" :: acc)
  | N.SeqR -> dobasetype ("rq" :: acc)
  | N.Scalar -> acc
  | _ -> E.s (bug "pkQualName")

(****** the CHECKERS ****)

let checkFunctionPointer (whatp:exp) (whatm:expmeta) whatkind nrargs =
  begin
    match whatkind with
    | N.Wild ->
        let whatb = emGet MKBase "checkFunctionPointer" whatm in
        call None (Lval(var CC.checkFunctionPointerFun.svar))
          [ castVoidStar whatp;
            castVoidStar whatb; integer nrargs ]

    | N.Safe | N.SafeC ->
        CC.checkNull whatp

    | N.FSeq -> (* A function pointer cannot be incremented. But we can still
                 * have in integer disguised in there. So check for non-null
                 * metadata *)
        let whate = emGet MKEnd "checkFunctionPointer" whatm in
        CC.checkNull whate

    | _ ->
        E.s (error "Function pointer is of kind %a. Arithemtic or casting of integers into function pointers is not supported\n"
               N.d_opointerkind whatkind)
  end

(* When we compute attributes we ignore the ptrnode attribute, but keep the
   split and maybeStackPtr info *)
let ignorePtrNode al =
  let rec loop al = match al with
      [] -> []
    | Attr(aname, _) :: rest when aname = "mdsize" ->
        loop rest
    | Attr(aname, _) :: rest when aname = "_ptrnode" -> begin
        (* drop ptrnode, add back the maybestack info *)
        let rest' = loop rest in
        match  N.nodeOfAttrlist al with
            None -> E.s (bug "missing node id")
          | Some n ->
              if N.hasFlag n N.pkStack then
                Attr("maybeStack",[]) :: rest'
              else
                Attr("noStack", []) :: rest'
        end
    | (a :: rest) as al ->
        let rest' = loop rest in
        if rest' == rest then al else a :: rest'
  in
  let newAttrs = loop al in
  let no = N.nodeOfAttrlist al in
  match no with
      Some n when N.hasFlag n N.pkSplit -> Attr("split", []) :: newAttrs
    | _ -> Attr("nosplit", []) :: newAttrs
let typeSigCure t = typeSigWithAttrs ignorePtrNode t

(* Keep track of the fixed composite types. Index by full name *)
let fixedComps : (int, unit) H.t = H.create 113
let metaDataTable : (typsig, typ option) H.t = H.create 113
let metaDataComps : (int, compinfo) H.t = H.create 13
let checkMetaDataComps : (int, unit) H.t = H.create 13

(* This function indicates whether a type is a split type. Note that
 * in cases like void and int, where split and nosplit are equivalent,
 * we return false in cases where we probably should return true. *)
let rec isSplitType (t: typ) : bool =
  match unrollType t with
    TPtr (_, a) | TArray (_, _, a) -> begin
      match N.nodeOfAttrlist a with
        Some n -> N.hasFlag n N.pkSplit
      | None -> false (* TODO E.s (bug "expected node") *)
    end
  | TComp (comp, _) -> hasAttribute "split" comp.cattr
  | TFun (rt, args, _, _) ->
      (isSplitType rt) ||
      (List.exists (fun (_, t, _) -> isSplitType t)
                   (argsToList args))
  | TNamed _ -> E.s (bug "impossible")
  | TVoid _ | TInt _ | TFloat _ | TEnum _ | TBuiltin_va_list _ ->
      false (* TODO: correct? irrelevant? *)

(* We need to remember the original function types (pre-fixupType) in
 * order to properly set the type of a compatible function in
 * varStartInput. *)
let originalFunctionTypes : (typsig, typ) H.t = H.create 113

let recordOriginalFunctionType (oldt: typ) (newt: typ) : unit =
  let tsig = typeSigCure newt in
  if not (H.mem originalFunctionTypes tsig) then
    H.add originalFunctionTypes tsig oldt

let getOriginalFunctionType (t: typ) : typ =
  try
    H.find originalFunctionTypes (typeSigCure t)
  with Not_found -> t (*E.s (bug "Original function type not stored!")*)

let rec fixupType t =
  match t with
    (* Replace the uses of the compatible types *)
  | TComp (ci, a) when ci != Poly.getPolyCompRepresentative ci ->
      TComp (Poly.getPolyCompRepresentative ci, a)

    (* Nosplit comps are fixed up in place--that is, their fields are
     * altered destructively.  Split comps must be processed here. *)
  | TComp (_, _) ->
      if isSplitType t then fixit t else t

    (* Nosplit typedefs are fixed up in place (i.e., destructively).
     * For split types, we need to unroll and fix up the base type. *)
  | TNamed (_, _) ->
      if isSplitType t then fixupType (unrollType t) else t

  (* Do not hash function types because they contain arguments with names *)
  | TFun (rt, args, isva, a) -> begin
      let args' = match args with
        None -> None
      | Some argl ->
          Some (List.map
                  (fun (an,at,aa) -> (an, fixupType at, aa))
                  argl)
      in
      let res = TFun(fixupType rt, args', isva, a) in
      res
  end
  | _ -> fixit t

and fixit t =
  (* First replace the _ptrnode attribute *)
(*  ignore (E.log "fixit T=%a\n" d_plaintype t); *)
  let t = getNodeAttributes t in
  let nd = N.nodeOfAttrlist (typeAttrs t) in (* Get the node so that we can
                                              * add it to the fixed type *)
  let ts = typeSigCure t in
  let res =
    try begin
      let found = H.find fixedTypes ts in
      (* We would like to preserve the use of the typedefs from the orignal
       * type. This could happen because when we compute the signatures we do
       * not take typedef into account. *)
      let rec preserveTypedef (orig: typ) (result: typ) =
        match orig, result with
        | TNamed(origti, _), result -> (* Use the original since we have
                                        * taken care of the origti *) orig
        | _, TNamed(tires, _) -> (* We do not want to introduce a typedef
                                  * where there was none *)
            preserveTypedef orig tires.ttype
          (* And preserve under pointers as well *)
        | TPtr(origt, _), TPtr(rest, resa) ->
            TPtr(preserveTypedef origt rest, resa)
          (* We could have other cases, but for now leave it alone *)
        | _, _ -> result
      in
      preserveTypedef t found

    end with Not_found -> begin
      let makeComp (tname: string) (tcomp: compinfo) : typ =
        let tstruct = TComp (tcomp, []) in
        (* Register the struct *)
        theFile :=
           consGlobal (GCompTag (tcomp, !currentLoc)) !theFile;
        (* Now define a type name *)
        let ti = { ttype = tstruct; tname = tname;
                   treferenced = false } in
        theFile :=
           consGlobal (GType(ti, !currentLoc)) !theFile;
        let tres = TNamed(ti, []) in
        (* Add this to ensure that we do not try to cure it twice *)
        H.add fixedTypes (typeSigCure tres) tres;
        tres
      in
      let makeMerge (prefix: string) (t: typ) (meta: typ) : typ =
        let tname = newTypeNameFromType prefix t in
        let tcomp =
          mkCompInfo true tname
          (fun _ ->
            [ ("_d", t, None, [], !currentLoc);
              ("_md", meta, None, [], !currentLoc) ])
          [Attr("mergecomp", [])]
        in
        makeComp tname tcomp
      in
      let fixed =
        match t with
          (TInt _|TEnum _|TFloat _|TVoid _) -> t

        | TBuiltin_va_list a ->
            E.s (E.bug "__builtin_va_list should not get to cure.ml. Your patching of stdarg.h does not work!")
        | TPtr (t', a) -> begin
            (* Get info about the type *)
            let pkind = kindOfType t in
            let isSplit = isSplitType t' in
            (* Figure out the new base type and new ptr type *)
            let fixedBaseType, fixedPtrType =
              if isSplit then
                t', t
              else
                let fixed = fixupType t' in
                fixed, TPtr (fixed, a)
            in
            (* Now create the new type according to its metadata type *)
            match metaDataType t with
              Some metaType ->
                (* If we have metadata, we need to create a fat ptr type *)
                let tname = newTypeNameFromType (pkTypePrefix pkind)
                                                fixedBaseType in
                let tcomp =
                  mkCompInfo true tname
                  (fun _ ->
                    [ ("_p", fixedPtrType, None, [], !currentLoc);
                      ("_ms", metaType, None, [], !currentLoc) ])
                  [Attr("mergecomp", [])]
                in
                let tres = makeComp tname tcomp in
                (* And to make sure that for all identical pointer types we
                 * create identical structure (for split types, this is
                 * done automatically below) *)
                if not isSplit then
                  H.add fixedTypes (typeSigCure fixedPtrType) tres;
                tres
            | None ->
                (* There's no metadata, so we're done *)
                fixedPtrType
          end

        | TNamed _ ->
            E.s (E.bug "Cure:fixupType: TNamed")

        | TComp (ci, _) ->
            if isSplitType t then
              match metaDataType t with
                Some ((TComp _) as meta) -> makeMerge "mc_" t meta
              | None -> t
              | _ -> E.s (E.bug "Composite metadata is not a composite.")
            else
              t

        | TArray(t', l, a) ->
            if isSplitType t then
              match metaDataType t with
                Some ((TArray _) as meta) -> makeMerge "ma_" t meta
              | None -> t
              | _ -> E.s (E.bug "Array metadata is not an array.")
            else
              let sized = extractArrayTypeAttribute a in
              let newarray = TArray(fixupType t', l, a) in
              let res =
                if sized then begin
                  addArraySize newarray
                end else begin
                  (match l with Some z when isZero z &&
                                            not (hasAttribute "size" a) &&
                                            not (hasAttribute "count" a) ->
                    ignore (warn "Unsized array of length 0\n");
                  | _ -> ());
                  newarray
                end
              in
              (* Save the fixed comp so we don't redo it later. Important since
               * redoing it means that we change the fields in place. *)
              H.add fixedTypes (typeSigCure res) res;
              res

        | TFun _ ->
            E.s (E.bug "Cure:fixupType: TFun")

      in
      H.add fixedTypes ts fixed;
(*      H.add fixedTypes (typeSigCure fixed) fixed; *)
(*    ignore (E.log "Id of %a\n is %s\n" d_plaintype t (N.typeIdentifier t));*)
      fixed
    end
  in
  (* Now add the node attribute to the resulting type *)
  let resnode =
    match nd with
      None -> res
    | Some nd ->
        typeAddAttributes [Attr("_ptrnode", [AInt nd.N.id])]
          (typeRemoveAttributes ["_ptrnode"] res)
  in
(*  ignore (E.log " :%a\n" d_plaintype resnode); *)
  resnode

(* This function computes the type of the metadata for a given function,
 * if any. *)
and metaDataType (t: typ) : typ option =
  let a = getNodeAttributes t in
  let ts = typeSigCure a in
  try
    H.find metaDataTable ts
  with Not_found ->
    let meta =
      match t with
        TVoid _ ->
          Some (voidType)

      | TFun (rt, args, _, _)
            when (metaDataType rt <> None) ||
                 (List.exists (fun (_, t, _) -> metaDataType t <> None)
                              (argsToList args)) ->
          (* TODO: do i want to avoid caching these like fixupType? *)
          Some (fixupType t)

      | TPtr (t', a) when pkHasMeta (kindOfType t) -> begin
          let pkind = kindOfType t in
          let tname = newTypeNameFromType
                  ("meta_" ^ (pkTypePrefix pkind)) t' in
          let metaFields = H.find pkFields pkind in
          let mcomp =
            mkCompInfo true tname
              (fun _ ->
                List.map
                  (fun mk ->
                    let fn, ft = fieldOfMK mk in
                    (fn, ft, None, [], !currentLoc))
                  metaFields)
              [Attr("metacomp", [])]
          in
          (* Now we must patch the type of the _mp field *)
          if pkHas MKMetaPointer pkind && isSplitType t' then begin
            let fn, _ = fieldOfMK MKMetaPointer in
            match metaDataType t' with
              Some t'' ->
                List.iter
                  (fun f ->
                    if f.fname = fn then
                      f.ftype <- TPtr(t'', [])) mcomp.cfields
            | _ -> () (*E.s (bug "metaDataType: Pointer's base type has no metadata, but the solver disagrees. %a" d_type t')*)
          end;
          theFile := consGlobal (GCompTag (mcomp, !currentLoc)) !theFile;
          Some (TComp (mcomp, []))
        end

      | TArray (t', eo, _) -> begin
          match metaDataType t' with
            Some t'' -> Some (TArray (t'', eo, []))
          | None -> None
        end

      | TComp (ci, _) when isSplitType t -> begin
          let newci =
            mkCompInfo ci.cstruct ("meta_" ^ ci.cname) (fun _ -> []) []
          in
          Some (TComp (newci, []))
(*
          try
            Some (TComp (H.find metaDataComps ci.ckey, []))
          with Not_found ->
            let createFields (newci: compinfo) =
              H.add metaDataComps ci.ckey newci;
              theFile := consGlobal (GCompTagDecl (newci, !currentLoc))
                         !theFile;
              let foldField f fs =
                match metaDataType f.ftype with
                  Some t'' -> (f.fname, t'', None, [], !currentLoc) :: fs
                | None -> fs
              in
              let result = List.fold_right foldField ci.cfields [] in
              H.remove metaDataComps ci.ckey;
              result
            in
            let newci =
              mkCompInfo ci.cstruct ("meta_" ^ ci.cname) createFields []
            in
            begin
            match newci.cfields with
              [] -> E.s (bug "metaDataType: Composite type has no metadata, but the solver disagrees.")
            | _ ->
                theFile := consGlobal (GCompTag (newci, !currentLoc))
                           !theFile;
                Some (TComp (newci, []))
            end
*)
        end

      | TNamed (ti, _) ->
          metaDataType ti.ttype

      | _ ->
          None
    in
    H.add metaDataTable ts meta;
    meta

and moveAttrsFromDataToType attrs typ : attributes * typ =
  let mustCopyMove = function
      Attr("sized", []) -> true, true
    | Attr("size", _) | Attr("count", _) -> true, false
    | Attr("nullterm", []) -> true, true
    | _ -> false, false
  in
  let a_copy, a_move =
    List.fold_left (fun (a_copy, a_move) a ->
      let mustCopy, mustMove = mustCopyMove a in
      let a_copy' = if mustCopy then a :: a_copy else a_copy in
      let a_move' = if mustMove then a :: a_move else a_move in
      (a_copy', a_move'))
      ([], [])
      attrs
  in
  List.filter (fun a -> not (List.mem a a_move)) attrs,
  typeAddAttributes a_copy typ

(****** Generate sized arrays *)
and addArraySize t =
  let tsig = typeSigCure t in
  try
    H.find sizedArrayTypes tsig
  with Not_found -> begin
	(* GCC does not like fields to have incomplete types *)
    let complt =
      if isCompleteType t then typeAddAttributes [Attr("sized", [])] t
      else begin
        match unrollType t with
	  TArray(bt, None, a) -> TArray(bt, Some zero,
                                        addAttribute (Attr("sized", [])) a)
        | TArray(bt, Some z, a) when isZero z ->
            TArray(bt, Some z, addAttribute (Attr("sized", [])) a)
        | TComp (ci, a) when ci.cfields = [] -> TArray(charType, Some zero,
                                                       [Attr("sized", [])])
        | _ ->
            E.s (unimp "Don't know how to tag incomplete type %a"
                   d_plaintype t)
      end
    in
    let packAttr = if !msvcMode then [] else [Attr("packed", [])] in
    let tname = newTypeNameFromType "_sized_" t in
    let newtypecomp =
         mkCompInfo true tname
           (fun _ ->
             [ ("_size", uintType, None, [], !currentLoc);
                                              (* Don't pack the first field
                                               * or else the whole variable
                                               * will be packed against the
                                               * preceeding one  *)
               ("_array", complt, None, packAttr, !currentLoc); ]) []
    in
    (* Register the new tag *)
    theFile := consGlobal (GCompTag (newtypecomp, !currentLoc)) !theFile;
    let newtype = TComp (newtypecomp, []) in
    let namedti = { tname = tname; ttype = newtype; treferenced = false } in
    let named = TNamed (namedti, [Attr("sized", [])]) in
    theFile := consGlobal (GType (namedti, !currentLoc)) !theFile;
    H.add sizedArrayTypes tsig named;
    (* Since maybe we added a zero length when there was no length, we should
     * compute the new signature
    (match tsig with
      TSArray(t,None,al) ->
        H.add sizedArrayTypes (TSArray(t,Some zero,al)) named
    | _ -> ());  *)
    (* Maybe we are adding too many types here *)
    H.add sizedArrayTypes (typeSigCure named) named;
    H.add sizedArrayTypes (typeSigCure newtype) named;
    H.add sizedArrayTypes (typeSigCure complt) named;
    named
  end

and tagType (t: typ) : typ =
  let tsig = typeSigCure t in
  try
    H.find taggedTypes tsig
  with Not_found -> begin
    let tname = newTypeNameFromType "_tagged_" t in
    let newtype =
      if isCompleteType t then begin
        (* ignore (E.log "Type %a -> bytes=%d, words=%d, tagwords=%d\n"
                  d_type t bytes words tagwords); *)
        let _, tagWords = tagLength (SizeOf(t)) in
        let tagAttr = if !msvcMode then [] else [Attr("packed", [])] in
        let tagComp =
           mkCompInfo true tname
             (fun _ ->
               [ ("_len", uintType, None, [], !currentLoc);
                                               (* Don't pack the first
                                                * field,or else the entire
                                                * thing will be packed
                                                * against the preceeding one  *)
                 ("_data", t, None, tagAttr, !currentLoc);
                 ("_tags", TArray(intType,
                                  Some tagWords, []), None, tagAttr, !currentLoc);
               ])
             []
        in
        (* Register the type *)
        theFile := consGlobal (GCompTag (tagComp, !currentLoc)) !theFile;
        TComp (tagComp, [])

      end else begin (* An incomplete type *)
	(* GCC does not like fields to have incomplete types *)
	let complt =
	  match unrollType t with
	    TArray(bt, None, a) -> TArray(bt, Some zero, a)
	  | TArray(bt, Some z, a) when isZero z -> t
	  | TComp (ci, _) when ci.cfields = [] ->
              TArray(charType, Some zero, [])
	  | _ -> t (* E.s (unimp "Don't know how to tag incomplete type %a"
                        d_plaintype t) *)
	in
        let tagComp =
           mkCompInfo true tname
             (fun _ ->
               [ ("_len", uintType, None, [], !currentLoc);
                 ("_data", complt, None, [], !currentLoc); ]) [] in
        (* Register the type *)
        theFile := consGlobal (GCompTag (tagComp, !currentLoc)) !theFile;
        TComp (tagComp, [])
      end
    in
    let namedti = { tname = tname; ttype = newtype; treferenced = false } in
    let named = TNamed (namedti, []) in
    theFile := consGlobal (GType (namedti, !currentLoc)) !theFile;
    H.add taggedTypes tsig named;
    H.add taggedTypes (typeSigCure named) named;
    named
   end

(* Compute the number of data words and the number of tag words, given a raw
 * area size (in bytes) *)
and tagLength (sz: exp) : (exp * exp) =
  (* TODO: WildC: number of tag words = number of words *)
  (* First the number of words *)
   BinOp(Shiftrt,
        BinOp(PlusA, mkCast sz uintType, kinteger IUInt 3, uintType),
        integer 2, uintType),
  (* Now the number of tag words. At 1 tag bit/ word we can fit the tags for
   * 128 bytes into one tag word. *)
  BinOp(Shiftrt,
        BinOp(PlusA,
              mkCast sz uintType, kinteger IUInt 127, uintType),
        integer 7, uintType)

let finalizeMetaDataComp (ci: compinfo) : unit =
  match metaDataType (TComp (ci, [])) with
    Some (TComp (mci, _)) when mci.cfields = [] ->
      let foldField f fs =
        match metaDataType f.ftype with
          Some t'' -> (f.fname, t'', None, [], !currentLoc) :: fs
        | None -> fs
      in
      let fieldSpec = List.fold_right foldField ci.cfields [] in
      let fields =
        List.map (fun (fn, ft, fb, fa, fl) ->
                    { fcomp = mci; ftype = ft; fname = fn;
                      fbitfield = fb; fattr = fa; floc = fl})
                 fieldSpec
      in
      mci.cfields <- fields
  | _ -> E.s (bug "finalizeMetaDataComp: comp metadata is not a stub comp")


(* Create the preamble (in reverse order). Must create it every time because
 * we must consider the effect of "defaultIsWild" *)
let preamble () =
  (* Define WILD away *)

  (* First add the preamble *)
  (* We define the macros. We will also put them in the body of main *)
  theFile :=
     (GText ((if !MU.alwaysStopOnError then "" else "// ") ^
             "#define CCURED_ALWAYS_STOP_ON_ERROR")) ::
     (GText ((if !MU.failIsTerse then "" else "// ") ^
             "#define CCURED_FAIL_IS_TERSE")) ::
     (GText ((if !N.useStrings then "" else "// ") ^
             "#define CCURED_USE_STRINGS")) ::
     (GText ((if !MU.logNonPointers then "" else "// ") ^
             "#define CCURED_LOG_NON_POINTERS")) ::
     (GText ((if !N.allowPartialElementsInSequence then "" else "// ") ^
             "#define CCURED_ALLOW_PARTIAL_ELEMENTS_IN_SEQUENCE")) ::
     !theFile;
  theFile :=
     GText ("// Include the definition of the checkers") :: !theFile;
  theFile :=
     GText ("#define CCURED\n#define CCURED_POST\n#include \"ccuredcheck.h\"")
       :: !theFile;

  (** Create some more fat types *)
  (* ignore (fixupType (TPtr(TInt(IChar, []), [Attr("wild",[])]))); *)
(*  ignore (fixupType (TPtr(TInt(IChar, [AId("const")]), [AId("wild")]))); *)
(*  wildpVoidType := fixupType (TPtr(TVoid([]), [Attr("wild",[])])); *)
(*  ignore (fixupType (TPtr(TVoid([AId("const")]), [AId("wild")]))); *)

  (* Now add the RTTI information.  *)
  theFile := consGlobal MU.rttiArrayDefn !theFile;

  ()

(**** Make a pointer type of a certain kind *)
let mkPointerTypeKind (bt: typ) (k: N.opointerkind) =
  let t = TPtr(bt, [N.k2attr k]) in
  if N.isC k then t else fixupType t

(***** Conversion functions *******)

(***** Address of ******)
let pkAddrOf (lv: curelval) : (cureexp * stmt clist) =
  (* The type of the addrOf *)
  let ptrtype =
    if lv.plvk = N.Wild && isFunctionType lv.lvt then
      (* It is not Ok to call mkPointerKind on a WILD function pointer
       * because we might be before the function type is settled. It will
       * change when we replace some formals. So we use an approximate type
       * in that case. This is an unfortunate hack. *)
      mkPointerTypeKind
        (TFun(voidType, Some [], false, typeAttrs lv.lvt)) lv.plvk
    else
      mkPointerTypeKind lv.lvt lv.plvk
  in
  (* For pointers to functions we only allow SAFE and WILD pointers *)
  if isFunctionType lv.lvt && lv.plvk <> N.Safe &&
     lv.plvk <> N.SafeC && lv.plvk <> N.Wild then
    E.s (bug "pkAddrOf function: %a" N.d_opointerkind lv.plvk);
  (* If we're taking an incompatible pointer to a compatible type,
   * then we need to unsplit it. *)
  let lv', lvm' =
(*
    (* JC: This should never happen! What was I thinking? *)
    if isSplitType lv.lvt && not (N.isC lv.plvk) && emHasMetaPtr lv.lvm then
      (* We're making an incompatible pointer, so we strip off the _p or _d
       * offset on the main lval and throw away the metadata.  It must
       * have one of these offsets because otherwise the inferencer
       * wouldn't have let us take an incompatible pointer to it. *)
      let rec stripP o =
        match o with
          NoOffset -> o
        | Field (f, NoOffset) when f.fname = "_p" || f.fname = "_d" -> NoOffset
        | Field (_, NoOffset) | Index (_, NoOffset) ->
            E.s (bug "pkAddrOf: couldn't find _p to remove")
        | Field (f, o) -> Field (f, stripP o)
        | Index (i, o) -> Index (i, stripP o)
      in
      (fst lv.lv, stripP (snd lv.lv)), emStripMetaPtr lv.lvm
    else if N.isC lv.plvk && not (emHasMetaPtr lv.lvm) then
      (* The address of this field needs a metadata pointer, but the current
       * type has no metadata.  This case can occur when the result flows
       * into a type requiring a metadata pointer.  So, add a zero ptr. *)
      lv.lv, emSetMetaPtr lv.lvm zero
    else
*)
      (* We're making a compatible pointer, so we're all good. *)
      lv.lv, lv.lvm
  in
  let plv =
    if isFunctionType lv.lvt && N.isC lv.plvk then
      (* TODO: Temporary hack for fptrs: Since we use a variable with a
       * fixed-up type for data and metadata, we need to cast the data
       * to the non-fixed-up type. *)
      mkCast (mkAddrOf lv') ptrtype
    else
      mkAddrOf lv'
  in
  match lv.plvk with
    N.Safe | N.SafeC | N.Index | N.Wild | N.WildC |
    N.FSeq | N.FSeqN | N.FSeqC | N.Seq | N.SeqN | N.SeqC ->
      mkCureexp ptrtype plv lvm', empty
  | _ -> E.s (bug "pkAddrOf(%a)" N.d_opointerkind lv.plvk)

(* sm: return whether given type is {unsigned,signed,} char *)
let isCharType (t : typ) : bool =
  match unrollType t with
  | TInt((IChar|ISChar|IUChar), _) -> true
  | _ -> false

let isIntOrPtrType (t : typ) : bool =
  match unrollType t with
  | TInt _ -> true
  | TPtr _ -> true
  | _ -> false

(* sm: localize the -1 that goes on in calculating array ends, to *)
(* facilitate experimenting with policy *)
let nulltermArrayEndIndex
  (arrayLen: exp) (* in elements *)
  : exp =
  if !N.useStrings && not !N.extendStringBuffers then
    (* let the end be length-1, cutting off access to last element *)
    (BinOp(MinusA, arrayLen, one, intType))
  else
    (* new policy: allow access to complete array; we add one more byte *)
    (* during a post-process after curing proper *)
    arrayLen

(* Same as above, but do the -1 on a pointer instead of an integer.
   (So subtract a full element size, instead of one byte) *)
let nulltermPointerEnd
  (arrayLen: exp) (* in bytes *)
  (ptrType: typ)
  : exp =
  if !N.useStrings && not !N.extendStringBuffers then
    (* let the end be length-1, cutting off access to last element *)
    (BinOp(MinusPI, arrayLen, one, ptrType))
  else
    (* new policy: allow access to complete array; we add one more byte *)
    (* during a post-process after curing proper *)
    arrayLen

(* Given an array lval obtain an lval corresponding to the first element *)
let arrayPointerToIndex (lv: curelval) : curelval =
  match unrollType lv.lvt with
    TArray(elemt, leno, a) ->
      let lv' = addOffsetLval (Index(zero, NoOffset)) lv.lv in
      if  lv.plvk = N.Wild || lv.plvk = N.WildC (* || lv.plvk = N.WildT *) then
        { lv = lv'; lvt = elemt; plvk = lv.plvk; lvm = lv.lvm; }
      else if (filterAttributes "sized" a <> []) then begin
        if isSplitType lv.lvt then
          E.s (unimp "arrayPointerToIndex: can't handle compat sized arrays");
        { lv = lv'; lvt = elemt; plvk = N.Index;
          lvm = emBase (StartOf lv.lv); }
      end else begin
        match leno with
          Some alen -> (* If it is not sized then better have a length *)
            let knd, alen' =
              if filterAttributes "nullterm" a <> [] then begin
                (* Leave null for the null character *)
                N.SeqN, (nulltermArrayEndIndex alen)
              end else N.Seq, alen
            in
            let em =
              emBaseEnd (StartOf lv.lv)
                        (BinOp(IndexPI, StartOf lv.lv, alen',
                               TPtr(elemt, [])))
            in
            (* If necessary, apply the parallel change to the metadata ptr *)
            let knd, em =
              if emHasMetaPtr lv.lvm then
                let deref = mkMem (emGetMetaPtr lv.lvm) NoOffset in
                N.addC knd,
                emSetMetaPtr em (mkAddrOf (addOffsetLval
                                             (Index (zero, NoOffset)) deref))
              else
                knd, em
            in
            (* A flavor of SEQ *)
            { lv = lv'; lvt = elemt; plvk = knd; lvm = em; }
        | None -> (* Not WILD and not SIZED *)
            E.s (bug "arrayPointIndex on a unsized array: %a\n" d_lval lv.lv)
      end

  | _ -> E.s (bug "arrayPointerToIndex on a non-array (%a)"
                d_plaintype lv.lvt)

(************* END of pointer qualifiers *************)


let cureExp2exp (ce: cureexp) : expRes =
  let t = if isSplitType ce.et then fixupType ce.et else ce.et in
  if not (isFatType t) then
    (ce.et, empty, ce.ep)
  else
    let (doset, lv) = setFatPointer t ce in
    (t, doset, Lval(lv))



   (* Test if we have changed the type *)
let rec typeContainsFats t =
   existsType
   (function TComp (comp, _) ->
      begin
        match comp.cfields with
          [p;b] when comp.cstruct && p.fname = "_p" && b.fname = "_b" ->
            ExistsTrue
        | _ -> ExistsMaybe
      end
      | _ -> ExistsMaybe)
    t

(* See if a type contains arrays *)
let containsArray t =
  existsType
    (function
        TArray _ -> ExistsTrue
      | TPtr _ -> ExistsFalse
      | TFun _ -> ExistsFalse
      | _ -> ExistsMaybe) t

let containsSizedArray t =
  existsType
    (function
        TComp (ci, _) when ci.cstruct -> begin
          match ci.cfields with
            [s; a] when s.fname = "_size" && a.fname = "_array" -> ExistsTrue
          | _ -> ExistsMaybe
        end
      | TPtr _ -> ExistsFalse
      | TFun _ -> ExistsFalse
      | _ -> ExistsMaybe) t

(* Create tags for types along with the newly created fields and initializers
 * for tags and for the length  *)
(* Check whether the type contains an embedded array *)
let mustBeTagged v =
  let isFunction =
    match v.vglob, v.vtype with
      true, TFun _ -> true
    |  _ -> false
  in
  if isFunction then false
                       (* Do not tag functions!! We handle them separately *)
  else
    (* See if it make sense to tag this one. We look at the address-of flag
     * and whether it contains arrays. *)
    let taggable =
       v.vaddrof (* Has its addres taken *)
    || containsArray v.vtype (* Or contains arrays *)

        (* Or the user said so *)
    || (match N.nodeOfAttrlist v.vattr with
        Some n when n.N.kind = N.Wild && n.N.why_kind = N.UserSpec -> true
        | _ -> false)
    (* !!! Do not tag the other globals. If you want them tagged then put a
     * __TAGGED attribute. That will force the node to be WILD  *)
    in
(*
    if v.vname = "tnow" then begin
      ignore (E.log "For %s: taggable=%b. vaddrof=%b, hasAttr=%b\n"
                v.vname taggable v.vaddrof
                (hasAttribute "tagged" v.vattr));
    end;
*)
    (* But do not tag certain variables *)
    let taggable' = taggable && (v.vname <> "__ccured_va_tags") in
    taggable' &&
    (!N.defaultIsWild || hasAttribute "tagged" v.vattr)

(* Everytime you register a local variable, remember here *)
let hasRegisteredAreas = ref true

(* Produce a statement to register an area and saves the code to unregister
 * the area *)
let registerArea (args: exp list)
                 (acc: stmt clist) : stmt clist =
  if !N.useLeanFats then begin
    hasRegisteredAreas := true;
    let reg = call None (Lval(var CC.registerAreaFun.svar)) args in
    CConsL (reg, acc)
  end else
    acc

let unregisterStmt () =
  if !hasRegisteredAreas then
    call None (Lval(var CC.unregisterFrameFun.svar)) []
  else
    mkEmptyStmt ()

(* Create a compound initializer for a tagged type *)
let splitTagType (tagged: typ)
    : fieldinfo * fieldinfo * fieldinfo * exp * exp  =
  (* Get the data field, the length field, and a tag field *)
  let dfld, lfld, tfld =
    match unrollType tagged with
      TComp (comp, _) -> begin
        match comp.cfields with
          [lfld; dfld; tfld] -> dfld, lfld, tfld
        | _ -> E.s (bug "splitTagType. No tags: %a\n" d_plaintype tagged)
      end
    | _ -> E.s (bug "splitTagType. No tags: %a\n" d_plaintype tagged)
  in
  let words, tagwords = tagLength (SizeOf(dfld.ftype)) in
            (* Now create the tag initializer *)
  dfld, lfld, tfld, words, tagwords

let makeTagCompoundInit (tagged: typ)
                        (datainit: init option) : init * fieldinfo =
  let dfld, lfld, tfld, words, _ = splitTagType tagged in
  CompoundInit (tagged,
                  (* Now the length *)
                (Field(lfld, NoOffset), SingleInit words) ::
                (match datainit with
                  None -> []
                | Some e -> [(Field(dfld, NoOffset), e)]))
    (* Leave the rest alone since it will be initialized with 0 *)
    ,
  dfld

let debugBitfields = false
(* Since we cannot take the address of a bitfield we treat accesses to a
 * bitfield like an access to the entire sequence of adjacent bitfields in
 * the host structure. Return a starting address and a length of the range *)
let getRangeOfBitfields (lv: lval) (t: typ) : exp * exp =
  let lvbase, lvoff = lv in
  try (* Will throw Not_found if not a bitfield *)
    let rec getHostOffset = function
        Field (fi, NoOffset) ->
          if fi.fbitfield <> None then fi, NoOffset else raise Not_found
      | Field (fi, o) ->
          let fibitfield, o' = getHostOffset o in
          fibitfield, Field (fi, o')
      | Index (e, o) ->
          let fibitfield, o' = getHostOffset o in
          fibitfield, Index (e, o')
      | NoOffset -> raise Not_found
    in
    let fibitfield, hostoff = getHostOffset lvoff in
    if debugBitfields then
      ignore (E.log "Found bitfield %s with host %s\n" fibitfield.fname
                fibitfield.fcomp.cname );
    (* Now find the last non-bitfield field before fi *)
    let rec findRange (before: fieldinfo option) (pastus: bool) =
      function
        | [] -> before, None  (* Bitfields all the way to the end *)
        | f :: rest ->
            if f.fname = fibitfield.fname then
              findRange before true rest (* We past our bitfield *)
            else
              if pastus then
                if f.fbitfield == None then
                  before, Some f (* We found the end of the range *)
                else
                  findRange before true rest
              else
                if f.fbitfield == None then
                  findRange (Some f) false rest
                else
                  findRange before false rest
    in
    let before, after = findRange None false  fibitfield.fcomp.cfields in
    let start =
      match before with
        None -> (* We are the first in the host.Take the address of the host *)
          if debugBitfields then
            ignore (E.log "  first in host\n");
          mkAddrOf (lvbase, hostoff)
      | Some beforefi ->
          if debugBitfields then
            ignore (E.log "  bitfields start after %s\n" beforefi.fname);
          let beforelval =
            lvbase, (addOffset (Field(beforefi, NoOffset))
                       hostoff)
          in
          BinOp(IndexPI,
                mkCast (mkAddrOf beforelval) charPtrType,
                SizeOfE (Lval(beforelval)),
                charPtrType)
    in
    let after =
      match after with
        Some afterfi ->
          if debugBitfields then
            ignore (E.log "  bitfields end before %s\n" afterfi.fname);
          mkAddrOf (lvbase, addOffset (Field(afterfi, NoOffset)) hostoff)
      | None -> (* No more bitfields after us *)
          if debugBitfields then
            ignore (E.log "  last in host\n");
          BinOp(PlusPI,
                mkCast (mkAddrOf (lvbase, hostoff)) charPtrType,
                SizeOfE (Lval(lvbase, hostoff)),
                charPtrType)
    in

    (castVoidStar start,
     BinOp(MinusPP,
           mkCast after charPtrType,
           mkCast start charPtrType, intType))
  with Not_found ->
    (mkAddrOf lv, SizeOf t)

(* Compute the offset of first scalar field in a thing to be written. Raises
 * Not_found if there is no scalar *)

(* This function is not used anymore *)
let offsetOfFirstScalar (t: typ) : exp =
  let rec theOffset (sofar: offset) t : offset option =
    match unrollType t with
      (TInt _ | TFloat _ | TEnum _) -> Some sofar
    | TPtr _ -> None
    | TComp (comp, _) when isFatComp comp -> None
    | TComp (comp, _) when comp.cstruct -> begin
        let doOneField acc fi =
          match acc, fi.ftype with
            None, TInt _ when fi.fbitfield <> None -> None
          | None, _ ->
              theOffset (addOffset (Field(fi, NoOffset)) sofar) fi.ftype
          | Some _, _ -> acc
        in
        List.fold_left doOneField None comp.cfields
    end
    | TComp (comp, _) -> begin (* UNION *)
        (* Do it for the first field only *)
        match comp.cfields with
          [] -> None
        | fi :: _ -> theOffset (addOffset (Field(fi, NoOffset)) sofar) fi.ftype
    end

    | TArray (bt, _, _) ->
        theOffset (addOffset (Index(zero, NoOffset)) sofar) bt
    | _ -> E.s (unimp "offsetOfFirstScalar")
  in
  match theOffset NoOffset t with
    None -> raise Not_found
  | Some NoOffset -> kinteger IUInt 0
  | Some off ->
      let scalar = mkMem (mkCastT zero intType (TPtr (t, []))) off in
      let addrof = mkAddrOf scalar in
      mkCast addrof uintType


let checkZeroTags base lenExp lv t =
  let start, size = getRangeOfBitfields lv t in
  try
    let _ = offsetOfFirstScalar t in (* Just find out if there are scalars *)
    call None (Lval (var CC.checkZeroTagsFun.svar))
      [ castVoidStar base; lenExp ;
        castVoidStar start;
        size; (* ofcureexp *) ]
  with Not_found ->
    mkEmptyStmt ()

let cureLocal (l: varinfo) =
  let newa, newt = moveAttrsFromDataToType l.vattr l.vtype in
  l.vattr <- N.replacePtrNodeAttrList N.AtVar newa;
(*                ignore (E.log "Fixing the type of local %s\n" l.vname);*)
  l.vtype <- fixupType newt;
  if mustBeTagged l then begin
    l.vtype <- tagType l.vtype;
  end
(*
                ignore (E.log "Local %s: %a. A=%a\n" l.vname
                          d_plaintype l.vtype
                          d_attrlist l.vattr);
*)

(****** CONVERSION FUNCTIONS *******)

(* Check the alignment in a cast from an expression to a given type *)
let checkAlignment (p: exp) (pm: expmeta)
                   (desttyp: typ) : stmt clist =
  empty

let seqToFSeq (p: exp) (pm: expmeta) : exp * expmeta * stmt clist =
  let b = emGet MKBase "seqToFSeq" pm in
  let bend = emGet MKEnd "seqToFSeq" pm in
  p, emEnd bend,
  single (call None (Lval (var CC.checkSeq2FSeqFun.svar))
            [ castVoidStar b; castVoidStar bend; castVoidStar p; ])

let indexToSeq (p: exp) (pm: expmeta) (noint: bool)
    : exp * expmeta * stmt clist =
  let b  = emGet MKBase "indexToSeq" pm in
  let tmp = makeTempVar !CC.currentFunction voidPtrType in
  p, emBaseEnd b (Lval(var tmp)),
  single (checkFetchIndexEnd tmp p b noint)

let indexToFSeq (p: exp) (pm: expmeta) (noint: bool)
    : exp * expmeta * stmt clist =
  let p', p'meta, acc' = indexToSeq p pm noint in
  (* At this point we know it is not an integer *)
  let p'', p''meta, acc'' = seqToFSeq p' p'meta in
  p'', p''meta, append acc' acc''

let fseqToSafe (p: exp)
               (pm: expmeta)
               (desttyp: typ)
               (foraccess: bool)
               (noint: bool) : exp * stmt clist =
  (*   (trace "sm" (dprintf "fseqToSafe: p=%a desttyp=%a b=%a bend=%a\n"*)
  (*                        d_exp p*)
  (*                        d_type desttyp*)
  (*                        d_exp b*)
  (*                        d_exp bend));*)
  let dest_baset =
    match unrollType desttyp with
      TPtr(x, _) -> x
    | _ -> E.s (bug "fseqToSafe: expected pointer type in dest")
  in
  let src_baset =
    match unrollType (typeOf p) with
      TPtr(x, _) -> x
    | _ -> E.s (bug "fseqToSafe: expected pointer type in source")
  in
  let bend = emGet MKEnd "fseqToSafe" pm in
  (* See if we must check the bounds *)
  let omitCheck = !noUnrefPointerChecks && isUnrefPointer desttyp in
  let theCheck =
    if not omitCheck then
      let sizeOfNoVoid (t: typ): exp =
        (* On MSVC sizeof void is 0, so we should use 1 instead *)
        match !msvcMode, unrollType t with
          true, TVoid _ -> one
        | _ -> SizeOf t
      in
      (* sm: changed to the OrNull variant so we allow casts of *)
      (* NULL FSEQs to NULL SAFEs *)
      single (call None (Lval (var CC.checkFSeq2SafeFun.svar))
                [ castVoidStar bend;
                  castVoidStar p;
                  sizeOfNoVoid src_baset;
                  sizeOfNoVoid dest_baset;
                  if foraccess then one else zero;
                  if noint then one else zero ])
    else begin
      empty
    end
  in
  p, theCheck

let seqToSafe (p: exp) (pm: expmeta)
              (desttyp: typ)
              (foraccess: bool)
              (noint: bool) : exp * stmt clist =
  (* An alternative way that collapses the two bounds checks *)
  let dest_baset =
      match unrollType desttyp with
        TPtr(x, _) -> x
      | _ -> E.s (bug "seqToSafe: expected pointer type")
  in
  let b = emGet MKBase "seqToSafe" pm in
  let bend = emGet MKEnd "seqToSafe" pm in
  (* See if we must check the bounds *)
  let omitCheck = !noUnrefPointerChecks && isUnrefPointer desttyp in

  let theCheck =
    if not omitCheck then
      CC.checkSeq2Safe b bend p dest_baset foraccess noint

    else begin
      (* sm: silence this too (it appears above as well) *)
      (*ignore (warn "Omitting bounds check on unref pointer");*)
      empty
    end
  in
  p, theCheck

let elementSize (srctype: typ) (desttyp: typ) : exp =
  let dest_baset =
    match unrollType desttyp with
      TPtr(x, _) -> x
    | _ -> E.s (bug "elementSize: expected pointer type in dest")
  in
  let src_baset =
    match unrollType srctype with
      TPtr(x, _) -> x
    | _ -> E.s (bug "elementSize: expected pointer type in source")
  in
  if not(Util.equals dest_baset src_baset) then  (* make sure the sizes match *)
    E.s (bug " Cast not allowed in (f)seqnWrite");
  (* On MSVC sizeof void is 0, so we should use 1 instead *)
  match !msvcMode, unrollType src_baset with
    true, TVoid _ -> one
  | _ -> SizeOf src_baset

(* fseqnWrite does checks similar to fseq2safe, but it calls CHECK_FSEQN_WRITE
   instead, which allows writing nul to the character past the end pointer. *)
let fseqnWrite (p: exp)
               (pm: expmeta)
               (desttyp: typ)
               (noint: bool)
               (isnul: exp)  : exp * stmt clist =
  let bend = emGet MKEnd "fseqnWrite" pm in
  (* See if we must check the bounds *)
  let omitCheck = !noUnrefPointerChecks && isUnrefPointer desttyp in
  let theCheck =
    if not omitCheck then
      let size: exp = elementSize (typeOf p) desttyp in
      single (call None (Lval (var CC.checkFSeqnWrite.svar))
                [ castVoidStar bend;
                  castVoidStar p;
                  size;
                  if noint then one else zero;
                  isnul
                ])
    else begin
      empty
    end
  in
  p, theCheck

let seqnWrite  (p: exp)
               (pm: expmeta)
               (desttyp: typ)
               (noint: bool)
               (isnul: exp)  : exp * stmt clist =
  let b = emGet MKBase "seqnWrite" pm in
  let bend = emGet MKEnd "seqnWrite" pm in
  (* See if we must check the bounds *)
  let omitCheck = !noUnrefPointerChecks && isUnrefPointer desttyp in
  let theCheck =
    if not omitCheck then
      let size: exp = elementSize (typeOf p) desttyp in
      single (call None (Lval (var CC.checkSeqnWrite.svar))
                [ castVoidStar b;
                  castVoidStar bend;
                  castVoidStar p;
                  size;
                  if noint then one else zero;
                  isnul
                ])
    else begin
      empty
    end
  in
  p, theCheck

let indexToSafe (p: exp) (desttyp: typ)
                (em: expmeta)
                (foraccess: bool) (noint: bool) : exp * stmt clist =
  let p', p'meta, acc' = indexToSeq p em noint in
  (* We know that this is not an integer at this point. *)
  let p'', acc'' = seqToSafe p' p'meta desttyp foraccess true in
  p'', append acc' acc''

let nulltermToSeq (p: exp) : exp * expmeta * stmt clist =
  (* Make a new temporary variable *)
  let sz = bitsSizeOf (typeOfLval (mkMem p NoOffset)) / 8 in
  let tmpend = makeTempVar !CC.currentFunction voidPtrType in
  let func, args = CC.checkFetchNulltermEnd sz in
  p, emBaseEnd p (Lval (var tmpend)),
  single (call (Some (var tmpend))
            (Lval (var func.svar))
            (p :: args))

let nulltermToFseq (p: exp) : exp * exp * exp * stmt clist =
  (* Make a new temporary variable *)
  let sz = (bitsSizeOf (typeOfLval (mkMem p NoOffset)) / 8) in
  let tmpend = makeTempVar !CC.currentFunction voidPtrType in
  let func, args = CC.checkFetchNulltermEnd sz in
  p, p, (Lval (var tmpend)),
  single (call (Some (var tmpend))
            (Lval (var func.svar))
            (p :: args))

(* Conversion to a string is with a bounds check.
 * But make the check pass if p == e.  e points to the terminating nul,
 * and an empty string is a valid string.  *)
let seqNToString (p: exp) (pm: expmeta) (desttyp: typ) : exp * stmt clist =
  if not !N.useStrings then
    E.s (bug "seqN when not using strings.");
  let b = emGet MKBase "seqNToString" pm in
  let e = emGet MKEnd "seqNToString" pm in
  (* Do a bounds check using end="e+1" *)
  let endptr =
      castVoidStar (BinOp(PlusPI, e, one, desttyp))
  in
(*  log "seqNToString %a\n" d_exp p; *)
  seqToSafe p (emBaseEnd b endptr) desttyp
    false (* allow NULL values *)
    false

(* Conversion to a string is with a bounds check.
 * But make the check pass if p == e.  e points to the terminating nul,
 * and an empty string is a valid string.  *)
let fseqNToString (p: exp) (pm: expmeta) (desttyp: typ) : exp * stmt clist =
  if not !N.useStrings then
    E.s (bug "fseqN when not using strings.");
  let e = emGet MKEnd "fseqNToString" pm in
  (* Do a bounds check using end="e+1" *)
  let endptr =
      castVoidStar (BinOp(PlusPI, e, one, desttyp))
  in
  fseqToSafe p (emEnd endptr) desttyp
    false (* allow NULL values *)
    false

let wildToROString (p: exp) (pm: expmeta) : exp * stmt clist =
  let b = emGet MKBase "wildToROString" pm  in
  p,
  single (call None (Lval (var CC.checkStringMax.svar))
            [ castVoidStar p; b ])

(* weimer: is this right?! *)
let indexToROString (p: exp) (pm: expmeta) : exp * stmt clist =
  let b = emGet MKBase "indexToROString" pm  in
  p,
  single (call None (Lval (var CC.checkStringMax.svar))
            [ castVoidStar p; b ])

(* Convert an RTTI to SAFE.  *)
(* if p is null and the test type is a pointer type,
   then the check automatically succeeds.*)
type downcastReason = DC_rtti | DC_union
let rttiDowncast (p: exp) (pm: expmeta) (dest_rtti: exp)
 (dest_is_ptr: bool) (reason: downcastReason) : stmt clist =
  let src_rtti = emGet MKRtti "rttiToSafe" pm in
  let checkfun = match reason with
      (* Two functions that have the same behavior, but different error msgs.*)
      DC_rtti -> CC.checkRttiCast
    | DC_union -> CC.checkRttiUnionTag
  in
  let check = call None (Lval (var checkfun.svar))
                [ src_rtti; dest_rtti ] in
  if dest_is_ptr then
    (* if (p != NULL) { CHECK_RTTICAST(src_rtti, dest_rtti) }   *)
    single (mkStmt(If(mkCast p !upointType,
                      mkBlock [check],
                      mkBlock [],
                      !currentLoc)))
  else
    single check

let fromTable (oldk: N.opointerkind)
              (p: exp)
  (* Returns some metadata *)
  : expmeta * stmt clist =
  let _checkAreas () =
    if not !N.useLeanFats then
      E.s (bug "I thought that we weren't using lean fats\n")
  in
  let fetchHomeEnd (kind: int) (p: exp) : varinfo * varinfo * stmt =
    let tmpb = makeTempVar !CC.currentFunction voidPtrType in
    let tmpe = makeTempVar !CC.currentFunction voidPtrType in
    tmpb, tmpe,
    call (Some (var tmpb)) (Lval (var CC.checkFindHomeEndFun.svar))
      [ integer kind ; castVoidStar p; mkAddrOf (var tmpe) ]
  in
  let fetchHome (kind: int) (p: exp) : varinfo * stmt =
    let tmpb = makeTempVar !CC.currentFunction voidPtrType in
    tmpb,
    call (Some (var tmpb)) (Lval (var CC.checkFindHomeFun.svar))
      [ integer kind; castVoidStar p ]
  in
  match oldk with
    N.WildT ->
      let b, s = fetchHome CC.registerAreaTaggedInt p in
      emBase (Lval(var b)), single s
  | N.IndexT ->
      let b, s = fetchHome CC.registerAreaSizedInt p in
      emBase (Lval(var b)), single s

  | N.SeqT | N.SeqNT ->
      let b, e, s = fetchHomeEnd CC.registerAreaSeqInt p in
      emBaseEnd (Lval(var b)) (Lval(var e)), single s

  | N.FSeqT | N.FSeqNT ->
      let _, e, s = fetchHomeEnd CC.registerAreaSeqInt p in
      emEnd (Lval(var e)), single s

  | _ -> E.s (bug "Called fromTable on a non-table")


(* from table *)
let fromTableCureexp (ce: cureexp) : stmt clist * cureexp =
  let newk = N.stripT ce.ek in
  if newk = ce.ek then
    empty, ce
  else
    let bt =
      match unrollType ce.et with
        TPtr(bt, _) -> bt
      | _ -> voidType
    in
    let newt = mkPointerTypeKind bt newk in
    let em, s = fromTable ce.ek ce.ep in
    s, mkCureexp newt ce.ep em

(* Whether we must do a null check (after we have done bounds checking) *)
let nullCheckAfterBoundsCheck (k: N.opointerkind) =
  match k with
    (* For these we don't because we did one when we fetched the length *)
    N.Wild | N.WildT | N.Index | N.IndexT -> false
  (* Do not add a null check after boundscheck for SEQ and FSEQ because those
   * bounds checks will also do the null check if this is preparation for a
   * memory access *)
  | N.Seq | N.SeqC | N.SeqN | N.SeqNC -> false
  | N.FSeq | N.FSeqC | N.FSeqN | N.FSeqNC -> false
  | N.String | N.ROString -> false
  | _ -> true

(* Convert an address into an curelval *)
let addressToLval (ae: cureexp) (off: offset) (foraccess: bool)
    : curelval * stmt clist =
  (* Get rid of the table types first *)
  let (addrt1, doaddr1, addr1meta, addrkind) =
    let addrt = typeOf ae.ep in
    match unrollType addrt with
      TPtr(t, a) ->
        let ptrk1 = kindOfType addrt in
        let ptrk = ae.ek in
        if ptrk1 <> ptrk then
          ignore (warn "addressToLval: ptrk1=%a and ptrk=%a\n"
                    N.d_opointerkind ptrk1 N.d_opointerkind ptrk);
        let newk = N.stripT ptrk in
        if newk <> ptrk then
          (* It was a table type *)
          let addr'meta, doaddr2 = fromTable ptrk ae.ep in
          t, doaddr2, addr'meta, newk
        else
          (* It was not a table type *)
          t, empty, ae.em, newk
    | _ -> E.s (unimp "Mem but no pointer type: %a@!addr= %a@!"
                  d_plaintype addrt d_plainexp ae.ep)
  in
  let addr1meta =
    if metaDataType addrt1 = None then
      emStripMetaPtr addr1meta
    else
      addr1meta
  in
  (* If the kind of the address is not WILD or INDEX we must do a null
   * check. For WILD and INDEX the bounds check will also take care of
   * the null *)
  let doaddr2 =
    (* Catch the case &v->f when v is Safe and f is the first field. In that
     * case we do not need to do a null check *)
    if addrkind = N.Safe && not foraccess &&
       (match off with
         Field(f, NoOffset) -> begin
           match f.fcomp.cfields with
             f' :: _ -> f == f'
           | _ -> false
         end
       | _ -> false) then
      doaddr1
    else
      if nullCheckAfterBoundsCheck addrkind then
        CConsR (doaddr1, CC.checkNull ae.ep)
      else
        doaddr1
  in
  let res =
    { lv = mkMem ae.ep NoOffset; lvt = addrt1; plvk = addrkind;
      lvm = addr1meta; } in
  res, doaddr2

let checkWild (p: exp) (size: exp) (b: exp) (blen: exp) : stmt =
  let src_baset =
    match unrollType (typeOf p) with
      TPtr (x, _) -> x
    | _ -> E.s (bug "checkWild: source is not a pointer")
  in
  (* This is almost like indexToSafe, except that we have the length already
   * fetched *)
  call None (Lval (var CC.checkBoundsLenFun.svar))
    [ castVoidStar b; blen;
      castVoidStar p; SizeOf (src_baset); size]

(* Check index when we switch from a sequence type to Safe, in preparation
 * for accessing a field.  *)
let beforeField (inlv: curelval)
                (foraccess: bool)
                (noint: bool) : curelval * stmt clist =
  let updateLval (lv: curelval) =
    (* Change the kind to SafeC or Safe depending on whether the original
     * kind had a metadata ptr. *)
    let k, m =
      if N.isC lv.plvk then
        N.SafeC,
        (if emHasMetaPtr lv.lvm then emMeta (emGetMetaPtr lv.lvm) else emNone)
      else
        N.Safe, emNone
    in
    { lv with plvk = k; lvm = m; }
  in
  (* Drop the RTTI here. *)
  let inlv = { inlv with plvk = N.stripRTTI inlv.plvk;
                         lvm = emClear MKRtti inlv.lvm } in
  match inlv.plvk with
    (* The kind is never a table type *)
    (N.Wild|N.WildC) -> inlv, empty (* No change if we are in a tagged area *)
  | (N.Safe|N.SafeC) -> inlv, empty (* No change *)

  | N.Index ->
      let _, docheck =
        indexToSafe (mkAddrOf inlv.lv)
          (TPtr(inlv.lvt, [])) inlv.lvm foraccess noint
      in
      updateLval inlv, docheck

  | (N.Seq|N.SeqN|N.SeqC) ->
      (* log "beforeField %a\n" d_lval inlv.lv; *)
      let _, docheck =
        seqToSafe (mkAddrOf inlv.lv) inlv.lvm
          (TPtr(inlv.lvt,[])) foraccess noint
      in
      updateLval inlv, docheck

  | (N.FSeq|N.FSeqN|N.FSeqC) ->
      let _, docheck =
        fseqToSafe (mkAddrOf inlv.lv) inlv.lvm
          (TPtr(inlv.lvt,[])) foraccess noint
      in
      updateLval inlv, docheck

  | N.String -> (* this happens when we have a NULLTERM pointer to an
                 * array of structures. Treat it as SAFE *)
      inlv, empty

  | _ -> E.s (unimp "beforeField on unexpected pointer kind %a"
                N.d_opointerkind inlv.plvk)

(* Prepare for indexing an lval. Obtain an lval that corresponds to the first
 * element of the array, but with a Safe or Wild pointer *)
let rec beforeIndex (inlv: curelval)
                    (foraccess: bool)
                    (noint: bool) : curelval * stmt clist =
  match inlv.plvk with
  | (N.Safe|N.SafeC|N.Wild|N.WildC) -> arrayPointerToIndex inlv, empty

  | (N.FSeq|N.FSeqN|N.FSeqC|N.Seq|N.SeqN|N.SeqC|N.Index) ->
      (* Convert to SAFE or WILD first *)
      let res1, acc1 = beforeField inlv foraccess noint in
      begin
      match res1.plvk with
        N.Safe | N.SafeC ->
          (* Now try again once it is SAFE *)
          let res2, acc2 = beforeIndex res1 foraccess noint in
          res2, append acc1 acc2
      | _ ->
          E.s (bug "beforeIndex: should be Safe\n")
      end

  | _ -> E.s (unimp "beforeIndex on unexpected pointer kind %a"
                N.d_opointerkind inlv.plvk)

(***** Create function descriptors ******)
let functionDescriptors : (int, varinfo) H.t = H.create 13
let definedFunctionIds : (int, bool) H.t = H.create 13
let functionDescriptorInit : global list ref = ref []

let funDescrInfo =
  mkCompInfo true "__functionDescriptor"
    (fun _ ->
      [ ("_len", uintType, None, [], !currentLoc);
        ("_pfun", TPtr(TFun(voidType, None,false, []), []),  None, [], !currentLoc);
        ("_nrargs", uintType, None, [], !currentLoc) ])
    []

let getFunctionDescriptor (vi: varinfo) : exp =
  let pfunfld = List.nth funDescrInfo.cfields 1 in
  let descr =
    try
      let descr = H.find functionDescriptors vi.vid in
      descr
    with Not_found -> begin
      let basename, _ = demangle vi.vname in
      let descr = makeGlobalVar (basename ^ "__descriptor")
          (TComp (funDescrInfo, [])) in
      (* Make the descriptor static if the function is static *)
      descr.vstorage <- vi.vstorage;
      (* Register a declaration or a definition for it *)
      if H.mem definedFunctionIds vi.vid then begin
        (* Need to know the number of arguments *)
        let nrformals =
          match vi.vtype with
            TFun (_, formals, _, _) -> List.length (argsToList formals)
          | _ -> E.s (bug "getFunctionDescriptor: %s not a function type"
                        vi.vname)
        in
        let lenfld, pfunfld, nrargsfld =
          match funDescrInfo.cfields with
            [l; f; a] -> l, f, a
          | _ -> E.s (bug "getFunctionDescriptor")
        in
        (* Store a declaration for now *)
        theFile := GVarDecl (descr, !currentLoc) :: !theFile;
        (* Store the initializer for later *)
        functionDescriptorInit :=
           (GVar (descr,
                  {init=Some (CompoundInit (TComp (funDescrInfo, []),
                                      [ (Field(lenfld, NoOffset),
                                         SingleInit zero);
                                        (Field(pfunfld, NoOffset),
                                         SingleInit
                                           (mkCast
                                              (AddrOf (Var vi,
                                                       NoOffset))
                                              (TPtr(TFun(voidType,None,
                                                         false, []),[]))));
                                        (Field(nrargsfld, NoOffset),
                                         SingleInit (integer nrformals))]))},
                  !currentLoc)) :: !functionDescriptorInit;

      end else begin
        descr.vstorage <- Extern;
        theFile := consGlobal (GVarDecl (descr, !currentLoc)) !theFile;
      end;
      H.add functionDescriptors vi.vid descr;
      descr
    end
  in
  mkAddrOf (Var descr, Field(pfunfld, NoOffset))

(******* Start of *******)
let rec pkStartOf (lv: curelval) : (cureexp * stmt clist) =
  match unrollType lv.lvt with
    TArray(t, _, _) -> begin
      match lv.plvk with
        N.Safe | N.SafeC | N.Wild | N.WildC | N.WildT ->
          let lv' = arrayPointerToIndex lv in
          let pres = mkPointerTypeKind t lv'.plvk in
          mkCureexp pres (mkAddrOf lv'.lv) lv'.lvm, empty

      | N.Seq|N.FSeq|N.Index|N.SeqC|N.FSeqC
      | N.SeqN|N.FSeqN|N.SeqNC|N.FSeqNC ->
          (* multi-dim arrays. Convert to SAFE first.  *)
          let safe, dolv = beforeField lv false false in
          begin
          match safe.plvk with
            N.Safe | N.SafeC ->
              let (res, stmts'') = pkStartOf safe in
              (res, append dolv stmts'')
          | _ ->
              E.s (bug "pkStartOf: I expected a safe here\n");
          end

      | _ -> E.s (unimp "pkStartOf: %a" N.d_opointerkind lv.plvk)
    end
  | _ -> E.s (unimp "pkStartOf on a non-array: %a"
                d_plaintype lv.lvt)

let isWildOrTaggedAttribute (va: attributes) : bool =
  (match N.nodeOfAttrlist va with
    Some n when n.N.kind = N.Wild -> true | _ -> false)
  || hasAttribute "tagged" va

let varStartInput (vi: varinfo) : curelval =
  (* Look out for wild function pointers *)
  match unrollType vi.vtype with
    TFun _ when isWildOrTaggedAttribute vi.vattr ->
      let descr = getFunctionDescriptor vi in
      { lv = (Var vi, NoOffset); lvm = emBase descr;
        lvt = vi.vtype; plvk = N.Wild; }
  | TFun _ when isSplitType
                  (getOriginalFunctionType vi.vtype) ->
      { lv = (Var vi, NoOffset);
        lvm = emMeta (mkAddrOf (Var vi, NoOffset));
        lvt = getOriginalFunctionType vi.vtype; plvk = N.SafeC; }
  | _ ->
      let res =
        { lv = (Var vi, NoOffset); lvm = emNone;
          lvt = vi.vtype; plvk = N.Safe; }
      in
(*      ignore (E.log "varStartInput for %s = %a\n"
                vi.vname d_curelval res);
*)
      res

(** Extract a pointer kind and true pointer type from a potentially fat
  * pointer type *)
let extractTruePointerType (t: typ) =
  let k = kindOfType t in
  let t' =
    match k with
      N.Safe | N.String | N.ROString
    | N.WildT | N.SeqT | N.FSeqT | N.SeqNT | N.FSeqNT | N.IndexT -> t
    | N.Scalar -> begin
        match unrollType t with
          TComp (ci, _) when isFatComp ci ->
            getTypeOfFat "extractTruePointerKind" t
        | _ -> t
      end
    | N.FSeq | N.FSeqN | N.Seq | N.SeqN | N.Wild | N.Index
    | N.SafeC | N.WildC | N.SeqC | N.FSeqC | N.SeqNC | N.FSeqNC
    | N.Rtti | N.FSeqR | N.SeqR
    | N.RttiC | N.FSeqRC | N.SeqRC
      -> begin
        match unrollType t with
          TPtr _ -> t
        | TComp _ -> getTypeOfFat "extractTruePointerKind" t
        | _ -> E.s (bug "castTo: unexpected pointer representation")
      end

    | k -> E.s (bug "extractTruePointerType: %a pointer kind"
                  N.d_opointerkind k)
  in
  k, t'

(* Do we need an alignment check for p + x?  Well, that depends on the size of
 *  *p.  If the size is a power of two, p + x will be aligned even if it
 *  overflows, so we can skip the check. *)
let needsSeqAlignCheck baset: bool =
  let size = (bitsSizeOf baset / 8) in
  let needed = match size with
    1|2|4|8|16|32|64|128|256|512|1024|2048|4096 -> false
  | _ -> true
  in
(*   if !E.verboseFlag then begin *)
(*     if needed then *)
(*       ignore (E.log "  Adding alignment check due to arith of size %d bytes.\n" *)
(*                 size) *)
(*     else *)
(*       ignore (E.log "  Not adding alignment check due to arithmetic.\n") *)
(*   end; *)
  needed

let pkArithmetic (e1: cureexp)
                 (bop: binop)  (* Either PlusPI or MinusPI or IndexPI *)
                 (e2: exp) : (cureexp * stmt clist) =
  let updateMeta (e1: cureexp) (e2: exp) =
    if emHasMetaPtr e1.em then
      let meta = emGetMetaPtr e1.em in
      emSetMetaPtr e1.em (BinOp (bop, meta, e2, typeOf meta))
    else
      e1.em
  in
  let e1ptype = typeOf e1.ep in
  match e1.ek with
  | N.Wild|N.WildC ->
      mkCureexp e1.et (BinOp(bop, e1.ep, e2, e1ptype)) (updateMeta e1 e2),
      empty

  | N.Index ->
      (* We should really do a check like SEQALIGN below. *)
      ignore (warn "alignment checks for Index pointers unimplemented.\n");
      mkCureexp e1.et (BinOp(bop, e1.ep, e2, e1ptype)) (updateMeta e1 e2),
      empty

  | N.Seq|N.SeqN|N.SeqC|N.SeqNC ->
      let baset =
        match unrollType e1ptype with
          TPtr(x, _) -> x
        | _ -> E.s (bug "pkArithmetic: expected pointer type")
      in
      let newp = BinOp(bop, e1.ep, e2, e1ptype) in
      let newp' = mkCureexp e1.et newp (updateMeta e1 e2) in
      let alignCheck = if needsSeqAlignCheck baset then
        single (call None (Lval (var CC.checkSeqArithFun.svar))
                  [ SizeOf(baset);
                    castVoidStar newp'.ep;
                    emGet MKBase "pkArithmetic" newp'.em;
                    emGet MKEnd "pkArithmetic" newp'.em ])
      else
        empty
      in
      newp',
      alignCheck

  | (N.FSeq|N.FSeqN|N.FSeqC|N.FSeqNC) ->
      let baset =
        match unrollType e1ptype with
          TPtr(x, _) -> x
        | _ -> E.s (bug "pkArithmetic: expected pointer type")
      in
      let newp = BinOp(bop, e1.ep, e2, e1ptype) in
      let newp' = mkCureexp e1.et newp (updateMeta e1 e2) in
      newp',
      single (call None (Lval (var CC.checkFSeqArithFun.svar))
                [ castVoidStar e1.ep;
                  SizeOf (baset);
                  castVoidStar newp;
                  emGet MKEnd "pkArithmetic" newp'.em;
                  if needsSeqAlignCheck baset then one else zero ])

  | N.Safe|N.SafeC ->
      if isZero e2 then e1, empty else
      E.s (bug "pkArithmetic: pointer arithmetic on safe pointer: %a@!"
             d_exp e1.ep)

  | N.String|N.ROString ->
      (* Arithmetic on strings is tricky. We must first convert to a Seq and
       * then do arithmetic. We leave it a SeqN to be converted back to
       * string later if necessary *)
      let p', p'meta, acc' = nulltermToSeq e1.ep in
      (* Change the type from String into a SeqN pointer *)
      let ptype' =
        match e1ptype with
          TPtr(bt, _) ->
            TPtr(bt, [N.k2attr N.SeqN])
        | _ -> E.s (bug "String pointer kind but not a pointer type")
      in
      (* And recompute the right type for the result *)
      let et' = fixupType ptype' in
      let p'' = BinOp(bop, p', e2, ptype') in
(*
      ignore (E.log "pkArithString: %a. @?pMETA=%a, K=%a,@?T=%a\n"
                d_plaintype ptype' d_expmeta p'meta
                N.d_opointerkind (kindOfType et')
                d_plaintype et');
*)
      mkCureexp et' p'' p'meta, acc'

  (* If we are doing arithmetic on tables we just do it directly. This is
   * UNSAFE since we might skip into the next table *)
  | N.FSeqT | N.FSeqNT | N.SeqT | N.SeqNT | N.WildT | N.IndexT ->
      mkCureexp e1.et (BinOp(bop, e1.ep, e2, e1ptype)) e1.em, empty

  | N.FSeqR|N.SeqR ->
      E.s (error "Pointer arithmetic is not allowed on %a pointers"
             N.d_opointerkind e1.ek)

  | _ -> E.s (bug "pkArithmetic(%a)" N.d_opointerkind e1.ek)

(* Various reasons why we might want to check an LV *)
type checkLvWhy =
    ToWrite of exp * expmeta
  | ToRead

(* Return just the code to do bounds checking, not also
 * the code for making the lvalue *)
let checkBounds (why: checkLvWhy)
                (mkBaseEnd: unit -> exp * exp)
                (lv: curelval) : stmt clist =
  begin
    (*     (trace "sm" (dprintf "checkBounds(%s): %a\n"        *)
    (*                          (if iswrite then "w" else "r") *)
    (*                          d_curelval lv));               *)

    (* Do not check the bounds when we access variables without array
     * indexing  *)
    match lv.plvk with
    | (N.Wild|N.WildC) ->
        (* We'll need to read the length anyway since we need it for
         * working with the tags *)
        let start, size = getRangeOfBitfields lv.lv lv.lvt in
        let b, e = mkBaseEnd () in
        let docheck = checkWild start size b e in
        single docheck

    | N.Index ->
        let _, docheck =
          indexToSafe (mkAddrOf lv.lv) (TPtr(lv.lvt, []))
                      lv.lvm true false in
        docheck

    | (N.FSeq|N.FSeqC) -> begin
        let _, docheck =
          fseqToSafe (mkAddrOf lv.lv)
            lv.lvm (TPtr(lv.lvt, [])) true false
        in
        docheck
      end
    | (N.Seq|N.SeqC) -> begin
        let _, docheck =
          seqToSafe (mkAddrOf lv.lv) lv.lvm
            (TPtr(lv.lvt, [])) true false
        in
        docheck
      end

    | (N.FSeqN|N.FSeqNC) -> begin
        (* compute the end pointer (end is first inaccessible byte); *)
        (* if we're reading, then we allow reading one more byte, *)
        (* so that string-manipulation code can read the final 0 *)
        (* GN: But only when reading a char *)
        let e = emGet MKEnd "checkBounds" lv.lvm in
        match why with
          ToRead ->
            let endptr =
              if !N.useStrings then (
                (* Allow reading of the trailing 0 *)
                (* (trace "sm" (dprintf "allowing read of trailing 0\n")); *)
                castVoidStar (BinOp(PlusPI,
                                    mkCast e charPtrType, one, charPtrType))
              )
              else
                e
            in
            let _, docheck =
              fseqToSafe (mkAddrOf lv.lv)
                (emEnd endptr) (TPtr(lv.lvt, [])) true false
            in
            docheck
        | ToWrite (what, whatm) ->
            let isnul = BinOp(Eq, what, zero, uintType) in
            let _, docheck =
              fseqnWrite (mkAddrOf lv.lv)
                (emEnd e) (TPtr(lv.lvt, [])) false isnul
            in
            docheck
      end
    | (N.SeqN|N.SeqNC) -> begin
        (* compute the end pointer (end is first inaccessible byte); *)
        (* if we're reading, then we allow reading one more byte, *)
        (* so that string-manipulation code can read the final 0 *)
        (* GN: But only when reading a char *)
        let b = emGet MKBase "checkBounds" lv.lvm in
        let e = emGet MKEnd "checkBounds" lv.lvm in
        match why with
          ToRead ->
            let endptr =
              if !N.useStrings then (
                (* Allow reading of the trailing 0 *)
                (* (trace "sm" (dprintf "allowing read of trailing 0\n")); *)
                castVoidStar (BinOp(PlusPI, e, one, typeOf e))
              )
              else
                e
            in
            let _, docheck =
              seqToSafe (mkAddrOf lv.lv) (emBaseEnd b endptr)
                (TPtr(lv.lvt, [])) true false
            in
            docheck
        | ToWrite (what, whatm) ->
            let isnul = BinOp(Eq, what, zero, uintType) in
            let _, docheck =
              seqnWrite (mkAddrOf lv.lv) (emBaseEnd b e)
                (TPtr(lv.lvt, [])) false isnul
            in
            docheck
      end
    | N.Safe | N.SafeC -> empty

    | N.String | N.ROString -> begin
        match why with
          ToRead ->
            (* Reading the 0th byte is always safe, but we must do the
               null check since we promised in nullCheckAfterBoundsCheck
               that we'd handle the null-check for these kinds. *)
            single (CC.checkNull (mkAddrOf lv.lv))
        | ToWrite (what, whatm) ->
            (* we can safely write the 0th byte if
                 - the current value is non-zero (so the length is >= 1), or
                 - the new value is 0.
              This also does a null check.*)
            let iszero = BinOp(Eq, what, zero, uintType) in
            single (call None (Lval (var CC.checkStringWrite.svar))
                      [ castVoidStar (mkAddrOf lv.lv);
                        iszero
                      ])
      end
    | _ -> E.s (bug "Unexpected pointer kind in checkBounds(%a)"
                  N.d_opointerkind lv.plvk)
  end

(****************************************************)

(*******************************************************
 **
 **   CASTS
 **
 **
 *******************************************************)
(* To debug rename the next function !!! *)
let rec castTo (fe: cureexp) (newt: typ) : stmt clist * cureexp =
  let newkind, newPointerType = extractTruePointerType newt in

  (* Convert the tables to normal *)
  let doe, fe = fromTableCureexp fe in

  let oldkind, oldPointerType = extractTruePointerType fe.et in
  if oldkind <> fe.ek then
    E.s (bug "castTo: mismatch pointer kinds");

  (* Cast the pointer expression to the new pointer type *)
  let castP (p: exp) =
   (* castP was dropping previous casts. But this is not right because the
    * cast might mean a conversion. So we keep them *)
    match unrollType newPointerType with
      TArray _ ->
        ignore (E.log "Making cast to %a\n" d_type newPointerType);
        p
    | _ -> mkCast p newPointerType
  in
  (* Perform the corresponding cast on the metadata pointer. *)
  let castMP (em: expmeta) : expmeta =
    (* If we have a metadata pointer, find its type (a pointer to the
     * metadata of its base type) and insert the appropriate cast. *)
    if emHasMetaPtr em then
      let bt =
        match newPointerType with
          TPtr (bt, _) -> bt
        | _ -> E.s (bug "castTo: castMP expected pointer, got %a"
                        d_type newPointerType)
      in
      let mt =
        match metaDataType bt with
          Some mt -> mt
        | None -> TVoid []
      in
      emSetMetaPtr em (mkCast (emGetMetaPtr em) (TPtr (mt, [])))
    else
      em
  in
  let oldt, p = fe.et, fe.ep in

  (* Finish off the cast *)
  let finishCast (acc: stmt clist) (res: cureexp) =
    (* Check that when we are casting into FSEQ and SEQ pointers we are
     * casting from SAFE, FSEQ and SEQ pointer to types whose size is a
     * multiple of the destination type *)
    let final_checks : stmt clist =
      match newkind with
        N.FSeq|N.FSeqN|N.Seq|N.SeqN|N.Index -> begin
          try
            (* Compute the new element size in bits *)
            let new_bt, new_elem_size =
              (* Get the base type first *)
              match unrollTypeDeep newPointerType with
              | TPtr(TVoid _, _) -> voidType, 0 (* Cast into void* is Ok *)
              | TPtr(TFun _, _) -> voidType, 0 (* Cast into funptr * is Ok *)
              | TPtr(new_bt, _) -> new_bt, bitsSizeOf new_bt
              | _ -> E.s (bug "castTo: new_elem_size")
            in
            (* Compute the old element size in bits, or -1 if it is Scalar *)
            let old_bt, old_elem_size =
              (* Get the base type first *)
              match unrollTypeDeep oldPointerType with
                TPtr(TVoid _, _) -> voidType, 0 (* Casting out of void-ptr *)
              | TPtr(TFun _, _) -> oldPointerType, -1
              | TPtr(old_bt, _) -> old_bt, bitsSizeOf old_bt
              | _ when oldkind = N.Scalar -> oldPointerType, -1
              | _ -> E.s (bug "castTo: old_elem_size")
            in
            (* We need to add a check when the old element size is not a
             * multiple of the new element size. We do not add a check if the
             * new element size is 0 (void) or 8 (char), since in those cases
             * we cannot damage alignment. This is true even if on gcc the
             * sizeof(void) is 1.  *)
            if not !N.allowPartialElementsInSequence &&
               new_elem_size > 8 &&
               old_elem_size <> -1 &&
               (old_elem_size = 0 ||
                old_elem_size <> (old_elem_size / new_elem_size)
                                                * new_elem_size) then
              (* We must check alignment *)
              match newkind with
                (N.FSeq|N.FSeqN) ->
                  single (call None (Lval (var CC.checkFSeqAlignFun.svar))
                            [ SizeOf(new_bt);
                              castVoidStar res.ep;
                              emGet MKEnd "castTo" res.em ])
              | (N.Seq|N.SeqN) ->
                  single (call None (Lval (var CC.checkSeqAlignFun.svar))
                            [ SizeOf(new_bt);
                              castVoidStar res.ep;
                              emGet MKBase "castTo" res.em;
                              emGet MKEnd "castTo" res.em ])
              | N.Index ->
                  single (call None (Lval (var CC.checkIndexAlignFun.svar))
                            [ SizeOf(new_bt);
                              castVoidStar res.ep;
                              emGet MKBase "castTo" res.em; ])
              | _ -> E.s (bug "castTo: failed to add alignment check")
            else
              empty
          with SizeOfError (whystr, why) ->
            E.s (bug "castTo: cannot compute bitsSizeOf (%s:%a) to perform alignment check: new=%a"
                   whystr d_type why d_type newPointerType)
        end

      | _ -> empty
    in
    append doe (append acc final_checks), res
  in

  match oldkind, newkind with
    (* We allow casts from types without a metadata pointer to types
     * with a metadata pointer, in which case we set the metadata pointer
     * to zero.  This case can occur when trusted casts and downcasts are
     * used; in particular, it's important when casting to a void* that
     * must also accomodate types with metadata pointers. *)
  | _, _ when N.isC newkind && not (N.isC oldkind) && oldkind <> N.Scalar ->
      (* A brief sanity check: the old type should be compatible, and
       * it should have no metadata of its own. *)
(*
      begin
        match unrollType oldPointerType with
          TPtr (bt, _) when isSplitType oldPointerType &&
                            (isVoidType bt || metaDataType bt = None) -> ()
        | _ -> E.s (bug "castTo: can't add metadata ptr when casting from %a"
                        d_type oldt)
      end;
*)
      (* Recursively do the cast with no metadata ptrs; then add the
       * metadata ptr (set to zero) at the very end. *)
      let newk' = N.stripC newkind in
      let newt' =
        match unrollType newPointerType with
          TPtr(bt, _) (*when metaDataType bt <> None*) ->
            mkPointerTypeKind bt newk'
        | t -> E.s (bug "castTo: can't add metadata ptr to %a" d_type t)
      in
      let doe', fe' = castTo fe newt' in
      finishCast doe' (mkCureexp newt fe'.ep (emSetMetaPtr fe'.em zero))

    (* We allow removal of a metadata pointer.  This case can occur when
     * doing an upcast or when doing a trusted cast from, say, void* to
     * char*, when the void* must accomodate types with metadata ptrs. *)
  | _, _ when N.isC oldkind && not (N.isC newkind) && newkind <> N.Scalar ->
      (* Recursively do the cast with metadata ptrs in place; then strip
       * the metadata ptr off at the very end. *)
      let newk' = N.addC newkind in
      let newt' =
        match unrollType newPointerType with
          TPtr(bt, _) (*when isVoidType bt || metaDataType bt = None*) ->
            mkPointerTypeKind bt newk'
        | t -> E.s (bug "castTo: can't remove metadata ptr from %a" d_type t)
      in
      let doe', fe' = castTo fe newt' in
      finishCast doe' (mkCureexp newt fe'.ep (emStripMetaPtr fe'.em))

    (* Catch the cases when the destination is a table *)
  | _, (N.WildT|N.SeqT|N.FSeqT|N.SeqNT|N.FSeqNT|N.IndexT) ->
      let newk' = N.stripT newkind in
      let newt' =
        match unrollType newt with
          TPtr(bt, _) -> mkPointerTypeKind bt newk'
        | _ -> E.s (bug "castTo: strip table")
      in
      let doe', fe' = castTo fe newt' in
      finishCast doe' (mkCureexp newt fe'.ep emNone)

        (* SCALAR, SAFE -> SCALAR, SAFE *)
  | (N.Scalar|N.Safe|N.String|N.ROString),
    (N.Scalar|N.Safe|N.String|N.ROString) ->
      finishCast empty (mkCureexp newt (castP p) fe.em)

  | N.SafeC, N.SafeC ->
      finishCast empty (mkCureexp newt (castP p) (castMP fe.em))

        (* SAFE -> FSEQ | FSEQN | SEQ | SEQN *)
  | N.Safe,  (N.FSeq|N.FSeqN|N.Seq|N.SeqN) |
    N.SafeC, (N.FSeqC|N.FSeqNC|N.SeqC|N.SeqNC) ->
      (* If the pointer is non-zero then convert it to FSEQ by adding one to
       * find the end  *)
      (* If the pointer type is a void ptr then do not add one to get the end
       * since that is illegal C  *)
      let p' = castP p in
      let isN =
        match newkind with
          N.FSeqN | N.SeqN | N.FSeqNC | N.SeqNC -> true
        | _ -> false
      in
      if isN then
        ignore
          (warn "Casting SAFE to %a is unsafe. Change referent of %a to be an array of characters\n"
             N.d_opointerkind newkind d_exp (dropCasts p'));
      let tentative_end =
        let tp = typeOf p in
        match unrollTypeDeep tp with
          TPtr(TVoid _, _) ->
            ignore (warn "Casting SAFE void* to %a. The area is 1 word."
                      N.d_opointerkind newkind);
            (* Leave space for a word *)
            castVoidStar (BinOp(PlusPI, mkCast p intPtrType, one,
                                intPtrType))

        | TPtr(TInt((IChar|IUChar|ISChar), _), _) ->
            BinOp(PlusPI, p, one, tp)

        | _ -> (* The type is not pointer to character *)
            if isN then
              ignore (warn "Casting SAFE to %a of base type %a"
                        N.d_opointerkind newkind d_type tp);
            BinOp(PlusPI, p, one, tp)
      in
      (* Now find the true end *)
      let (theend:exp), (getit: stmt clist) =
        CC.checkSafeEnd p tentative_end
      in
      if not (isZero theend) then
        ignore (warnOpt "Casting SAFE pointer to %a. Length will be one."
                  N.d_opointerkind newkind );
      let meta =
        match newkind with
          N.FSeq | N.FSeqN | N.FSeqC | N.FSeqNC -> emEnd (castVoidStar theend)
        | _ -> emBaseEnd p' theend
      in
      finishCast getit (mkCureexp newt p'
                                  (castMP (emCopy MKMetaPointer meta fe.em)))

        (* SCALAR -> INDEX, WILD, SEQ, FSEQ *)
  | N.Scalar, (N.Index|N.Wild|N.WildC|N.Seq|N.FSeq|N.SeqC|N.FSeqC|
               N.FSeqN|N.SeqN|N.SeqNC|N.FSeqNC|N.SafeC) ->
      let record : stmt clist =
        if not (isZero p) && newkind <> N.Wild then begin
          ignore (warn "Casting scalar (%a) to non-WILD pointer in %s!"
                    d_exp p !CC.currentFunction.svar.vname);
          CC.logScalar p
        end else
          empty
      in
      let em = pkMakeScalarMeta newkind in
      finishCast record (mkCureexp newt (castP p) (castMP em))


        (* WILD, INDEX, SEQ, FSEQ, RTTI -> SCALAR *)
  | (N.Index|N.Wild|N.FSeq|N.Seq|N.FSeqN|N.SeqN|
     N.WildC|N.FSeqC|N.SeqC|N.FSeqNC|N.SeqNC|N.SafeC|
     N.Rtti|N.FSeqR|N.SeqR|N.RttiC|N.FSeqRC|N.SeqRC), N.Scalar ->
      finishCast empty (mkCureexp newt (castP p) emNone)

        (* WILD, INDEX, SEQ, FSEQ  -> same_kind *)
  | (N.Index|N.Wild|N.FSeq|N.Seq|N.FSeqN|N.SeqN|
     N.WildC|N.FSeqC|N.SeqC|N.FSeqNC|N.SeqNC), _ when newkind = oldkind ->
          (* Keep the metadata *)
       finishCast empty (mkCureexp newt (castP p) (castMP fe.em))

            (* INDEX -> SAFE. Must do bounds checking *)
  | N.Index, N.Safe ->
      let p', acc' = indexToSafe p newPointerType fe.em false false in
      finishCast acc' (mkCureexp newt (castP p') emNone)

        (* INDEX -> SEQ *)
  | N.Index, N.Seq ->
      let p', p'meta, acc' = indexToSeq p fe.em false in
      finishCast acc' (mkCureexp newt (castP p') p'meta)

        (* INDEX -> FSEQ *)
  | N.Index, N.FSeq ->
      let p', p'meta, acc' = indexToFSeq p fe.em false in
      finishCast acc' (mkCureexp newt (castP p') p'meta)

        (* SEQ -> SAFE. Must do bounds checking *)
  | (N.Seq|N.SeqN),   N.Safe |
    (N.SeqC|N.SeqNC), N.SafeC ->
      let p', acc' = seqToSafe p fe.em newPointerType false false in
      finishCast acc' (mkCureexp newt (castP p')
                                 (castMP (emCopy MKMetaPointer emNone fe.em)))

        (* SEQ -> FSEQ *)
  | (N.Seq|N.SeqN),   N.FSeq |
    (N.SeqC|N.SeqNC), N.FSeqC ->
      let p', p'meta, acc' = seqToFSeq p fe.em in
      finishCast acc' (mkCureexp newt (castP p')
                                 (castMP (emCopy MKMetaPointer p'meta fe.em)))

  | N.SeqN, N.FSeqN ->
      let p', p'meta, acc' = seqToFSeq p fe.em in
      finishCast acc' (mkCureexp newt (castP p') p'meta)

        (* FSEQ -> SAFE. Must do bounds checking *)
  | (N.FSeq|N.FSeqN),   N.Safe |
    (N.FSeqC|N.FSeqNC), N.SafeC ->
      let p', acc' = fseqToSafe p fe.em newPointerType false false in
      finishCast acc' (mkCureexp newt (castP p')
                                 (castMP (emCopy MKMetaPointer emNone fe.em)))

        (* FSEQ -> SEQ. *)
  | (N.FSeq|N.FSeqN), N.Seq ->
      ignore (warnOpt "Casting FSEQ pointer to SEQ.");
      let bend = emGet MKEnd "castTo FSEQ -> SEQ" fe.em in
      finishCast empty
        (mkCureexp newt (castP p) (emBaseEnd (castVoidStar p) bend))

  | N.FSeqN, N.SeqN ->
      ignore (warnOpt "Casting FSEQ pointer to SEQ.");
      let bend = emGet MKEnd "castTo FSEQN -> SEQ" fe.em in
      finishCast empty
        (mkCureexp newt (castP p) (emBaseEnd (castVoidStar p) bend))

  | N.FSeqN, N.FSeq |
    N.FSeqNC, N.FSeqC ->
      finishCast empty (mkCureexp newt (castP p) (castMP fe.em))

        (* SEQN -> SEQ *)
  | N.SeqN, N.Seq ->
      finishCast empty (mkCureexp newt (castP p) fe.em)

        (* SEQN -> STRING *)
  | (N.SeqN|N.SeqNC), (N.String|N.ROString) ->
      let p', acc' = seqNToString p fe.em newPointerType in
      finishCast acc' (mkCureexp newt (castP p') emNone)

        (* STRING -> SEQ. Allow the ROSTRING also. *)
  | (N.String | N.ROString), (N.SeqN|N.Seq) ->
      let p', p'meta, acc' = nulltermToSeq p in
      finishCast acc' (mkCureexp newt (castP p') p'meta)

        (* FSEQ -> STRING *)
  | (N.FSeqN|N.FSeqNC), (N.String|N.ROString) ->
      let p', acc' = fseqNToString p fe.em newPointerType in
      finishCast acc' (mkCureexp newt (castP p') emNone)

        (* STRING -> FSEQ *)
  | (N.String | N.ROString), (N.FSeqN|N.FSeq) ->
      let p', b', bend', acc' = nulltermToFseq p in
      finishCast acc' (mkCureexp newt (castP p') (emEnd bend'))

        (* WILD -> ROSTRING *)
  | N.Wild, N.ROString ->
      let p', acc' = wildToROString p fe.em in
      finishCast acc' (mkCureexp newt (castP p') emNone)

        (* INDEX -> ROSTRING *)
  | N.Index, N.ROString ->
      let p', acc' = indexToROString p fe.em in
      finishCast acc' (mkCureexp newt (castP p') emNone)

        (* RTTI -> anything *)
  | (N.Rtti|N.FSeqR|N.SeqR|N.RttiC|N.FSeqRC|N.SeqRC), newkind ->
      let newkind' = N.stripRTTI newkind in
      let destIsRtti = newkind' <> newkind in
      (* See if this is a downcast *)
      let rtti1, rtti2, downcast =
        MU.checkRttiCast ~newedges:None
             oldPointerType true newPointerType destIsRtti !currentLoc
      in
      (* See if we need to check the downcast *)
      let checkDowncast =
        if downcast then
          rttiDowncast p fe.em rtti2 true DC_rtti
        else empty
      in
      (* Now strip the RTTI from the source  *)
      let strippedFE: cureexp =
        let oldk' = N.stripRTTI oldkind in (* The new kind *)
        let t' =
          match unrollType oldPointerType with
            TPtr(bt, _) -> mkPointerTypeKind bt oldk'
        | _ -> E.s (bug "castTo: RTTI -> *")
        in
        { et = t';
          ep = p;
          ek = oldk';
          em = {fe.em with _t = None} }
      in
      (* Strip the RTTI from the destination *)
      let newt' =
        if destIsRtti then
          match unrollType newPointerType with
            TPtr(bt, _) -> mkPointerTypeKind bt newkind'
          | _ -> E.s (bug "castTo: RTTI -> *")
        else
          newt
      in
      (* Now do the cast as if we didn't have RTTI *)
      let doe', fe' = castTo strippedFE newt' in
      (* See if we must add back the RTTI metadata *)
      let em' =
        if destIsRtti then
          { fe'.em with _t = fe.em._t }
        else
          fe'.em
      in
      finishCast (append checkDowncast doe')
        (mkCureexp newt (castP fe'.ep) (castMP em'))

        (* SCALAR -> RTTI *)
  | N.Scalar, N.Rtti ->
      finishCast empty
        (mkCureexp newt (castP p) (castMP (emRtti (MU.getScalarRtti ()))))

        (* SCALAR -> RTTIC *)
  | N.Scalar, N.RttiC ->
      finishCast empty
        (mkCureexp newt (castP p)
                        (castMP (emRttiMeta (MU.getScalarRtti ()) zero)))

        (* SCALAR -> FSEQR | SEQR *)
  | N.Scalar, (N.FSeqR|N.SeqR|N.FSeqRC|N.SeqRC) ->
      (* Strip the RTTI from the destination *)
      let newkind' = N.stripRTTI newkind in
      let newt' =
        match unrollType newPointerType with
          TPtr(bt, _) -> mkPointerTypeKind bt newkind'
        | _ -> E.s (bug "castTo: SCALAR -> FSEQR|SEQR")
      in
      (* Now do the cast as if we didn't have RTTI *)
      let doe', fe' = castTo fe newt' in
      (* Now add to the metadata the RTTI for scalars *)
      finishCast doe'
        (mkCureexp newt (castP fe'.ep)
           (castMP {fe'.em with _t = Some (MU.getScalarRtti ())}))

    (* anything (except SCALAR) -> RTTI *)
  | _, (N.Rtti|N.FSeqR|N.SeqR|N.RttiC|N.FSeqRC|N.SeqRC) ->
      (* We know oldkind <> RTTI *)
      if N.isRTTI oldkind then
        E.s (bug "castTo: * -> RTTI");
      (* See if is a downcast amd make the RTTI *)
      let rtti1, rtti2, downcast =
        MU.checkRttiCast ~newedges:None
                         oldPointerType false newPointerType true !currentLoc
      in
      if downcast then
        E.s (bug "castTo: %a->RTTI did not expect downcast"
               N.d_opointerkind oldkind);
      (* Strip the RTTI from the destination type *)
      let newt' =
        match unrollType newPointerType with
          TPtr(bt, _) -> mkPointerTypeKind bt (N.stripRTTI newkind)
        | _ -> E.s (bug "castTo: * -> RTTI")
      in
      (* Now do the cast *)
      let doe', fe' = castTo fe newt' in (* Cast to non-RTTI type *)
      (* Now turn it into RTTI *)
      let rttiTag = if emHas MKRtti fe.em then
        (* oldkind is not RTTI, but if we are reading from a tagged union,
           it will have an RTTI tag anyways.  Use that tag instead of the
           static tag from before. *)
        emGet MKRtti "castTo(rtti for tagged unions)" fe.em
      else
        rtti1 in
      let newMeta = emSet MKRtti fe'.em rttiTag in
      finishCast doe'
        (mkCureexp newt (castP fe'.ep) (castMP newMeta))



        (* SAFE -> RTTI
  | N.Safe, N.Rtti ->
      let rtti1, rtti2, downcast =
        MU.checkRttiCast ~newedges:None
                         oldPointerType false newPointerType true !currentLoc
      in
      if downcast then
        E.s (bug "castTo: SAFE->RTTI did not expect downcast");
      finishCast empty (mkCureexp newt (castP p) (emRtti rtti1))

        (* FSEQ,SEQ,INDEX -> RTTI *)
  | (N.FSeq|N.FSeqN|N.Seq|N.SeqN|N.Index), N.Rtti ->
      (* Cast to SAFE first and then to RTTI *)
      let newt' =
        match unrollType oldPointerType with
          TPtr(bt, _) -> mkPointerTypeKind bt N.Safe
        | _ -> E.s (bug "castTo: FSEQ -> RTTI")
      in
      let doe', fe' = castTo fe newt' in (* Cast to SAFE *)
      let doe'', fe'' = castTo fe' newt in (* The actual cast *)
      finishCast (append doe' doe'') fe''
 *)
          (* RTTI -> SAFE
  | N.Rtti, N.Safe ->
      let rtti1, rtti2, downcast =
        MU.checkRttiCast ~newedges:None
            oldPointerType true newPointerType false !currentLoc
      in
      if downcast then
        let p', acc = rttiToSafe p fe.em rtti2 in
        finishCast acc (mkCureexp newt (castP p') emNone)
      else
        finishCast empty (mkCureexp newt (castP p) emNone)
   *)
          (******* UNIMPLEMENTED ********)
  | N.String, N.Wild
          when
        (match p with
          Const(CStr s) when prefix "ccurederror_exp: " s -> true
        | _ -> false) -> (* This occurs because such strings are generated
            * in case of error *)
            finishCast empty (mkCureexp newt (castP p) (emBase zero))

  | _, _ ->
      E.s (unimp "castTo(%a -> %a.@!%a@!:%a@!->%a)"
             N.d_opointerkind oldkind N.d_opointerkind newkind
             d_cureexp fe
             d_plaintype oldt d_plaintype newt)

(* Rename this as castTo *)
let castToDebug (fe: cureexp) (newt: typ) : stmt clist * cureexp =
  let (doe', fe') as res = castTo fe newt in
  ignore (E.log "castToDebug:\n  fe=%a\n  newt= %a\n fe'=%a\n\n"
            d_cureexp fe d_plaintype newt d_cureexp fe');
  res


(* Cache some iterator variables for the current function. *)
let iterVars: varinfo list ref = ref [] (* Clean this when you start a new
                                         * function *)
let globInitIterVars: varinfo list ref = ref [] (* A special list of iterator
                                                 * variables for the global
                                                 * initializer *)
let useGlobalIterVars: bool ref = ref false (* If this is set to true then
                                             * the withIterVar function will
                                             * use the global list of
                                             * iterators  *)
let withIterVar (doit: varinfo -> 'a) : 'a =
  let iterVarRef, hostFunction =
    if !useGlobalIterVars then
      globInitIterVars, getGlobInit !CC.currentFile
    else
      iterVars, !CC.currentFunction
  in
  let newv =
    match !iterVarRef with
      v :: resta ->
        iterVarRef := resta;
        v

    | [] -> makeTempVar hostFunction ~name:"iter" uintType
  in
  let res = doit newv in
  (* Make it available again *)
  iterVarRef := newv :: !iterVarRef;
  res

(* given that we're going to write a pointer to 'lval', return true *)
(* if it is allowed to point to the stack, and therefore the corresponding *)
(* check should be omitted *)
let rec lvalMayPointToStack (where: lval) : bool =
begin
  match where with
  (* simple variable access *)
  | (Var v, NoOffset)
  (* accessing field of fat pointer (needed for split types) *)
  | (Var v, Field({ fname = "_p" }, NoOffset))
  (* simple array access through named array *)
  | (Var v, Index(_, NoOffset)) -> (
      let mayPoint = (hasAttribute "mayPointToStack" v.vattr) in
      (trace "lvalMayPoint" (dprintf
        "lvalMayPointToStack: where = %s, attrs = %a, mayPoint = %b\n"
        v.vname d_attrlist v.vattr mayPoint));
      mayPoint
    )

  (* accessing a field of something *)
  | (_, Field(f, NoOffset)) -> (
      let mayPoint = (hasAttribute "mayPointToStack" f.fattr) in
      (trace "lvalMayPoint" (dprintf
        "lvalMayPointToStack: where field = %s, attrs = %a, mayPoint = %b\n"
        f.fname d_attrlist f.fattr mayPoint));
      mayPoint
    )

  (* accessing something within a field *)
  | (host, Field(f, ofs)) -> (
      (* all I really care about is digging down to find the attributes *)
      (* attached to the final offset; so synthesize something I can use *)
      (* to recurse, as a bit of a hack *)
      (lvalMayPointToStack (host, ofs))    (* ditch 'f', follow 'ofs' *)
    )

  (* pointer dereference, or accessing element of (non-simple-variable) array *)
  | _ -> (
      (* for now assume any non-variable isn't allowed to point at stack *)
      (trace "lvalMayPoint" (dprintf
        "lvalMayPointToStack: where = %a\n"
        d_lval where));
      false
    )
end

type gsResult =
    (** The custom scanner-generator declines to process this *)
  | GSDefault

    (** The custom scanner-generator completely processed this type *)
  | GSDone of stmt clist

    (** The custom scanner-generator computed a prefix and a suffix. Neither
     * of those must include the accumulator passed in to gsTryIt *)
  | GSPrefixSuffix of stmt clist * stmt clist

(** Generate code that scan all the components of a data structure. This
  * class is parameterized by the type of the information that is passed down
  * the tree. *)
class type ['a] scanner = object
  (** For each suboject we will invoke this function. If the function wishes
    * to override the default scanning, should return Some result *)
  method gsTryIt: typ -> 'a -> stmt clist -> gsResult


  (** While doing the default scanning for a field, we'll call this function
    * to find the parameter for processing each field *)
  method gsField: 'a -> fieldinfo -> 'a

  (** While doing the default scanning for an array element, we'll call this
   * function to find the parameter for processing one element. We pass the
   * type of the array element. *)
  method gsArrayElem: typ -> 'a -> exp -> 'a
end

(* A scanner for checking the reading, writing and return of pointers. All
 * structure fields are scanned. For unions we scan the longest field. For
 * arrays we scan all elements in a loop. *)
let rec genScanner (scanner: 'a scanner)
                   (t: typ)
                   (data: 'a)
                   (acc: stmt clist) : stmt clist =
  (* See if a special action must be performed *)
  match scanner#gsTryIt t data acc with
  | GSDone acc' -> acc' (* The specialized version did it for us *)
  | r -> begin (* The specialized version declines to do it *)
      let pref, suff =
        match r with
          GSDefault -> empty, empty
        | GSPrefixSuffix (p, s) -> p, s
        | GSDone _ -> E.s (bug "genScanner")
      in
      let acc' =
        match unrollType t with
          TInt _ | TFloat _ | TEnum _ | TPtr _ | TBuiltin_va_list _ -> acc

        | TComp (comp, _) -> begin
            (* Find the set of fields to do. For structures, this consists of
            * all fields. For unions this is the longest field *)
            let fields =
              if comp.cstruct then comp.cfields else
              let longest_len, longest_field =
                try
                  List.fold_left
                    (fun (longest_len, longest_field) f ->
                      let sz = bitsSizeOf f.ftype in
                      if sz > longest_len
                      then (sz, Some f) else (longest_len, longest_field))
                    (-1, None)
                    comp.cfields
                with SizeOfError _ ->
                  E.s (unimp "Cannot find the longest field in %s\n"
                         (compFullName comp))
              in
              match longest_field with
                None -> []
              | Some f -> [f]
            in
            List.fold_left
              (fun acc' f ->
                genScanner
                  scanner
                  f.ftype
                  (scanner#gsField data f)
                  acc')
              acc
              fields
        end

        | TArray (elt, leno, _) -> begin
            let len =
              match leno with
                Some len -> len
              | None ->
                  E.s (unimp
                         "Generating scanner for array of unspecified ength")
            in
            (* Loop over all elements *)
            (* Make an interator variable for this function *)
            withIterVar
              (fun it ->
                let itvar = Lval (var it) in
                let scanone =
                  genScanner
                    scanner
                    elt
                    (scanner#gsArrayElem elt data itvar)
                    empty
                in
                append
                  (fromList
                     (mkForIncrOptim
                        ~iter: it
                        ~first: zero
                        ~past: len
                        ~incr: one
                        ~body: (toList scanone)))
                  acc)
        end
        | _ -> E.s (unimp "genScanner: unexpected type %a\n" d_type t)
      in
      assert (checkBeforeAppend acc' suff);
      let acc'suff = append acc' suff in
      if not (checkBeforeAppend pref acc'suff) then begin
        ignore (warn "checkBeforeAppend failed\n");
      end;
      assert (checkBeforeAppend pref acc'suff);
      append pref acc'suff
  end

let addOffsetExp (off: offset) (e: exp) : exp =
  match e with
    Lval lv -> Lval (addOffsetLval off lv)
  | _ -> E.s (unimp "addOffsetExp: not an lvalue: %a\n" d_exp e)

let rec addOffsetExpMeta (off: offset) (em: expmeta) : expmeta =
  if emHasMetaPtr em then
    let mp =
      match emGetMetaPtr em with
        Lval lv -> lv
      | _ -> E.s (bug "addOffsetExpMeta: expected lval")
    in
    match unrollType (typeOfLval mp), off with
      TComp (comp, _) as t, NoOffset when isMetaComp comp ->
        readFieldsOfMeta t mp
    | TComp (comp, _), Field (f, off2) ->
        begin
        try
          let em2 = emSetMetaPtr em (Lval (addOffsetLval
                      (Field (getCompField comp f.fname, NoOffset)) mp))
          in
          addOffsetExpMeta off2 em2
        with Not_found ->
          emNone
        end
    | TArray _, Index (idx, off2) ->
        let em2 = emSetMetaPtr em (Lval (addOffsetLval off mp)) in
        addOffsetExpMeta off2 em2
    | _, NoOffset ->
        em
    | t, _ -> E.s (bug "addOffsetExpMeta: type=%a offset=%a"
                       d_type t (d_offset nil) off)
  else
    em

(*** Check a read. This is used only when we read a WILD pointer ***)
class checkReadClass (getbaselen: unit -> exp * exp) = object
  method gsTryIt (t: typ)
                 (where: lval)
                 (acc: stmt clist) : gsResult =
    match unrollType t with
    | TComp (comp, _) when isFatComp comp -> (* A fat pointer. We know it is
                                              * WILD  *)
        let omitCheckRead = !noUnrefPointerChecks && isUnrefPointer t in
        if not omitCheckRead then begin
          let base, e = getbaselen () in
          GSDone (CConsR (acc,
                          CC.checkWildPointerRead base (mkAddrOf where) e))
        end else
          GSDone acc

    | TBuiltin_va_list _ ->
        E.s (unimp "checking the read of a builtin_va_list")

    | _ -> GSDefault (* For the other types we use the default scanner *)

  (* Go into the field *)
  method gsField (where: lval) (f: fieldinfo) : lval =
    addOffsetLval (Field(f, NoOffset)) where

  (* Go to an array element *)
  method gsArrayElem (_: typ) (where: lval) (idx: exp) : lval =
    addOffsetLval (Index(idx, NoOffset)) where
end

(**** Check a write. For WILD areas we must set the tags. And whenever we
    * write a pointer we must check that it is not a stack pointer *)
class checkWriteClass (pkind: N.opointerkind)
                      (getbaselen: unit -> exp * exp) (* Use to get the base
                                                       * and the end for a
                                                       * Wild  *)
= object
  method gsTryIt (t: typ)
                 ((where: lval), (what: exp), (what_em: expmeta))
                 (acc: stmt clist) : gsResult =

    let checkPtr ptype whatp whatp_em =
        if pkind = N.Wild then
          let checkFn =
            if (lvalMayPointToStack where) then
              (* omit the stack pointer check *)
              CC.checkWildPointerWrite_noStackCheck
            else
              CC.checkWildPointerWrite
          in
          let base, e = getbaselen () in
          GSDone (CConsL
                  (checkFn base (mkAddrOf where)
                     (emGet MKBase "checkWriteClass" whatp_em)
                     whatp e,
                   acc))
        else
          (* We must always check the value that is either null for a
           * non-pointer or a pointer into the home area for a pointer *)
          let checkWhat =
            match kindOfType ptype with
              N.Wild|N.Index|N.Seq|N.SeqN|N.WildC|N.SeqC|N.SeqNC
            | N.SeqR|N.SeqRC ->
                emGet MKBase "checkWriteClass" whatp_em
            | N.FSeq|N.FSeqN|N.FSeqC|N.FSeqNC|N.FSeqR|N.FSeqRC ->
                emGet MKEnd "checkWriteClass" whatp_em
            | N.Safe|N.SafeC|N.String|N.Rtti|N.RttiC -> whatp
            | _ -> E.s (unimp "checkReturn: unexpected kind (%a) of fat type %a" N.d_opointerkind (kindOfType ptype) d_type ptype)
          in
          if not (maybeStackPointer whatp) then begin
            (* We're definitely a heap pointer.*)
            GSDone acc
          end
          (* this is the place we insert the stack-pointer check that is
           * causing EDG-generated exception code to fail; so here we check
           * for a special attribute which says to allow it  *)
          else if (lvalMayPointToStack where) then
            (* trust the user and omit the check *)
            GSDone acc
          else if (isLocalVar where) then
            (* it's always okay to store a pointer when the lhs is in the
               current frame. *)
            GSDone acc
          else
            (* do the check as usual *)
            GSDone (CConsL (CC.checkStorePtr (mkAddrOf where)
                              checkWhat, acc))
    in

    match unrollType t with
    | TComp (comp, _) when isFatComp comp -> begin (* A fat pointer. *)
        let ptype, whatp, whatp_em = readFieldsOfFat what t in
        checkPtr ptype whatp whatp_em
    end

    | TPtr(_, _) as t -> (* This can only happen if we are writing a SAFE or
                          * STRING pointer  *)
        checkPtr t what what_em

    | TBuiltin_va_list _ ->
        E.s (unimp "checking the write of a builtin_va_list")

    | _ -> GSDefault (* For the other types we use the default scanner *)

  (* Go into the field *)
  method gsField ((where: lval), (what: exp), (what_em: expmeta))
                 (f: fieldinfo) : lval * exp * expmeta =
    addOffsetLval (Field(f, NoOffset)) where,
    addOffsetExp (Field(f, NoOffset)) what,
    addOffsetExpMeta (Field(f, NoOffset)) what_em

  (* Go to an array element *)
  method gsArrayElem (_: typ) ((where: lval), (what: exp), (what_em: expmeta))
                     (idx: exp) : lval * exp * expmeta =
    addOffsetLval (Index(idx, NoOffset)) where,
    addOffsetExp  (Index(idx, NoOffset)) what,
    addOffsetExpMeta (Index(idx, NoOffset)) what_em

end

(* Return just the code to check the memory operation *)
let rec checkMem (why: checkLvWhy)
                 (inlv: curelval) (* The lval that we are reading or writing *)
 : stmt clist =
(*
  ignore (E.log "checkMem: lv=%a\n" d_curelval inlv);
*)
  (* Maybe it is a table. In that case, get the true base and end *)
  (* See if a table pointer *)
  let newk = N.stripT inlv.plvk in
  if newk <> inlv.plvk then begin (* A table pointer *)
    let addrmeta, stmts = fromTable inlv.plvk (mkAddrOf inlv.lv) in
    append stmts
          (checkMem why { inlv with lvm = addrmeta;
                                    plvk = newk; })
  end else begin
    (* Fetch the length field in a temp variable. But do not create the
     * variable until certain that it is needed  *)
    let baseEndExp : (exp * exp) option ref = ref None in
    let getWildBaseEndExp () =
      match !baseEndExp with
        Some (b, x) -> b, x
      | None -> begin
          let b = emGet MKBase "checkTags" inlv.lvm in
          let len = makeTempVar !CC.currentFunction ~name:"_tlen" uintType in
          let x = Lval(var len) in
          baseEndExp := Some (b, x);
          b, x
      end
    in
    let getVarOcureexp e =
      match e with
        Lval(Var vi, NoOffset) -> vi
      | _ -> E.s (bug "getLen");
    in
    (* See first what we need in order to check tags *)
    let checkTags =
      (* Take a look at the type involved. If it does not contain pointers
       * then we don't need to check anything *)
      if existsType (function TPtr _ -> ExistsTrue | _ -> ExistsMaybe)
                    inlv.lvt then
        begin
          match why with
            ToRead when inlv.plvk = N.Wild ->
              let _b = emGet MKBase "checkTags" inlv.lvm in
              let rdScanner = new checkReadClass getWildBaseEndExp in
              genScanner rdScanner inlv.lvt inlv.lv empty
          | ToRead -> empty
          | ToWrite (what, what_em) ->
              let wrScanner =
                new checkWriteClass inlv.plvk getWildBaseEndExp in
              genScanner wrScanner inlv.lvt (inlv.lv, what, what_em) empty
      end else
        empty
    in
    (* For a write through a WILD pointer also zero the tags *)
    let zeroAndCheckTags =
      match inlv.plvk, why with
        N.Wild, ToWrite _ ->
          let b, e = getWildBaseEndExp () in
          CConsL(checkZeroTags b e inlv.lv inlv.lvt, checkTags)
      | _ -> checkTags
    in
    (* Now see if we need to do bounds checking *)
    let checkb =
      append
        (checkBounds why getWildBaseEndExp inlv)
        zeroAndCheckTags
    in
    (* See if we need to generate the length *)
    (match !baseEndExp with
      None -> checkb
    | Some (b, e) ->
        let start, _ = getRangeOfBitfields inlv.lv inlv.lvt in
        CConsL(CC.checkFetchLength (getVarOcureexp e) start b false,
               checkb))
  end

(** Check a return value *)
class checkReturnValueClass = object
  method gsTryIt (t: typ)
                 (what: exp)
                 (acc: stmt clist) : gsResult =
    match unrollType t with
      TPtr(bt, _) when not (maybeStackPointer what) ->
          (* We're definitely a heap pointer, so there's no need for a check.*)
          GSDone acc
    | TComp (comp, _) when isFatPtrComp comp && not (maybeStackPointer what) ->
          GSDone acc

      (* We check pointers ourselves *)
    | TPtr(bt, _) ->
        begin
          match kindOfType t with
            N.Safe|N.SafeC|N.String -> ()
          | _ -> E.s (bug "checkReturnValue: expected SAFE or STRING pointer")
        end;
        GSDone (CConsR(acc, CC.checkReturnPtr what))

      (* Also, for fat pointers we must check the component that is either
       * null for a non-pointer or something within the home for a regular
       * pointer  *)
    | TComp (comp, _) when isFatPtrComp comp ->
        let ptype, ptr, ptr_em = readFieldsOfFat what t in
        let checkWhat =
          match kindOfType ptype with
            N.Wild|N.Index|N.WildC -> emGet MKBase "checkReturn" ptr_em
          | N.FSeq|N.FSeqN|N.FSeqC|N.FSeqNC|
            N.Seq|N.SeqN|N.SeqC|N.SeqNC |N.FSeqR|N.SeqR->
              emGet MKEnd "checkReturn" ptr_em
          | N.Safe|N.SafeC|N.String|N.Rtti -> ptr
          | _-> E.s(unimp "checkReturnVC: unexpected kind (%a) of fat type %a"
			N.d_opointerkind (kindOfType ptype) d_type ptype)
        in
        GSDone (CConsR(acc, CC.checkReturnPtr checkWhat))

    | TBuiltin_va_list _ ->
        E.s (unimp "checking the return of a builtin_va_list")

    | _ -> GSDefault (* For the other types we use the default scanner *)

  (* Go into the field *)
  method gsField (what: exp) (f: fieldinfo) : exp =
    addOffsetExp (Field(f, NoOffset)) what

  (* Go to an array element *)
  method gsArrayElem (_: typ) (what: exp) (idx: exp) : exp =
    addOffsetExp (Index(idx, NoOffset)) what

end

(* Now create the scanner for checking return types *)
let checkReturnScanner : exp scanner = new checkReturnValueClass

(* Now check a return value *)
let checkReturnValue
    (t: typ)
    (e: exp) : stmt clist =
  if existsType (function TPtr _ -> ExistsTrue | _ -> ExistsMaybe) t then
    genScanner checkReturnScanner t e empty
  else
    empty

(********** Initialize variables ***************)

(*** A scanner for initializing a type *)
class initializeTypeClass (mustZero: bool)
                          (endo: exp option) (* The end of the array for open
                                              * arrays *)
    = object (self)
  method gsTryIt (t: typ)
                 (where: lval)
                 (acc: stmt clist) : gsResult =
    match unrollType t with
    | TFun _ -> GSDone acc (* Probably a global function prototype *)
    | TVoid _ -> GSDone acc (* allocating and returning a void* *)
    | TPtr (bt, a) -> begin
        (* If a non-wild pointer then initialize to zero *)
        let mustinit =
          mustZero &&
          (match N.kindOfAttrlist a with
            N.Wild, _ -> false
          | N.Unknown, _ when !N.defaultIsWild -> false
          | _ -> true)
        in
        if mustinit then
          GSDone (CConsL (mkSet where (mkCastT zero intType t), acc))
        else
          GSDone acc
    end
    | TComp (comp, a) when comp.cstruct -> begin (* A struct *)
        match comp.cfields with
          [s; a] when s.fname = "_size" && a.fname = "_array" ->
            (* Sized arrays *)
            let bt, sizeo, aa =
              match unrollType a.ftype with
                TArray(bt, lo, aa) -> bt,lo,aa
              | _ -> E.s (bug "SIZED array is not an array\n")
            in
            (* Construct the array initializer *)
            (* ignore (E.log "Initializing sized for %s\n" v.vname); *)
            let thesizelv = addOffsetLval (Field(s, NoOffset)) where in
            let thearraylv = addOffsetLval (Field(a, NoOffset)) where in
            (* Compute the new array length (in elements for the array type)
             * and also compute the size in bytes of the array *)
            let l, thissize_bytes =
              match sizeo with
                Some l when not (isZero l) ->
                  l, (BinOp(Mult, mkCast l uintType, SizeOf(bt), uintType))

              | _ -> begin
                  match endo with
                    Some e ->
                      (* We know the end of the area *)
                      let sz =
                        BinOp(MinusA, e,
                              mkCast (mkAddrOf thearraylv) uintType,
                              uintType) in
                      (BinOp(Div, sz, SizeOf(bt), uintType)),
                      sz

                  | None ->
                      ignore
                        (E.warn "Initializing SIZED open array with len 0: %a"
                           d_exp (mkAddrOf thesizelv));
                      zero, zero
              end
            in
            (* Now compute the size in words *)
            let thissize =
                BinOp(Shiftrt,
                      BinOp(PlusA, thissize_bytes, kinteger IUInt 3,
                            uintType),
                      integer 2, uintType) in
            (* Register the sized array *)
            let acc1 =
              registerArea [ integer CC.registerAreaSizedInt;
                             castVoidStar (mkAddrOf thearraylv);
                             castVoidStar zero ] acc
            in
            (* Set the size *)
            let acc2 = CConsL (mkSet thesizelv thissize, acc1) in
            (* No go and initialize the array itself. But change the length
             * of the array *)
            GSDone (genScanner (self :> lval scanner)
                               (TArray(bt, Some l, aa)) thearraylv acc2)

        | _ -> (* A regular struct. Do all the fields in sequence *) GSDefault
    end
    | TArray(bt, Some l, a) ->
	let mustAddNul = filterAttributes "nullterm" a <> [] && mustZero in
        if mustAddNul && isCharType bt then begin
          (* Write a zero at the very end *)
          GSDone (CConsL
                  (mkSet (addOffsetLval
                            (Index((nulltermArrayEndIndex l), NoOffset)) where)
                     zero,
                   acc))
        end else begin
          if mustAddNul then begin
	    (* matth: (UNSOUND) Ignore mustAddNul if this is not a char[].  *)
            ignore (warn "NULLTERM array of base type %a" d_type bt)
	  end;
          (* Register the array *)
          let acc1 =
            registerArea
              [ integer CC.registerAreaSeqInt;
                castVoidStar (mkAddrOf where);
                castVoidStar (mkAddrOf (addOffsetLval
                                          (Index(l, NoOffset)) where)) ] empty
          in
          (* Initialize the array itself *)
          GSPrefixSuffix (acc1, empty)
      end

    | TBuiltin_va_list _ ->
        E.s (unimp "initializing a builtin_va_list")

    | _ -> GSDefault (* For the other types we use the default scanner *)


  (* Go into the field *)
  method gsField (where: lval) (f: fieldinfo) : lval =
    addOffsetLval (Field(f, NoOffset)) where

  (* Go to an array element *)
  method gsArrayElem (_: typ) (where: lval) (idx: exp) : lval =
    addOffsetLval (Index(idx, NoOffset)) where
end

let rec initializeType
    (t: typ)   (* The type of the lval to initialize *)
    (mustZero: bool)   (* The area is not zeroed already *)
    (endo: exp option) (* The end of the home area. To be used for
                        * initializing arrays of size 0  *)
    (lv: lval)
    (acc: stmt clist) : stmt clist =

  let initScanner = new initializeTypeClass mustZero endo in
  genScanner initScanner t lv acc

(* Create and accumulate the initializer for a variable *)
let initializeVar (acc: stmt clist)
                  (v: varinfo) : stmt clist =
  (* Maybe it must be tagged *)
  if mustBeTagged v then begin
   (* Generates code that initializes vi. Needs "iter", an integer variable
    * to be used as a for loop index  *)
    withIterVar
      (fun iter ->
        let dfld, lfld, tfld, words, tagwords = splitTagType v.vtype in
        (* Prepare the registration *)
        let acc' =
          registerArea
            [ integer CC.registerAreaTaggedInt;
              castVoidStar (mkAddrOf (Var v, Field(dfld, NoOffset)));
              castVoidStar zero ]
            acc
        in
        (* Write the length *)
        CConsL
          (mkSet (Var v, Field(lfld, NoOffset)) words,
           (* And the loop to initialize the tags with zero *)
           (if not v.vglob then
             append
               (fromList
                  (mkForIncr iter zero (mkCast tagwords intType) one
                     [mkSet (Var v, Field(tfld,
                                          Index (Lval(var iter),
                                                 NoOffset)))
                         zero]))
               acc'
           else
             acc')))
  end else begin
    let doinit = initializeType v.vtype (not v.vglob) None in
    doinit (Var v, NoOffset) acc
  end

(* ww: now that we have wide-character string literals, we need to make
 * globals arrays that have base types that are not just charType
 * (in particular, we might use wcharType). The 'thisCharType' argument
 * gives the element type of global array we should build. *)
let rec stringLiteral
        (s_get : int -> Cil.constant)
        (s_length : int) (strt: typ)
        (thisCharType : typ) : stmt clist * cureexp =
  let fixChrPtrType = fixupType strt in
  let k = kindOfType fixChrPtrType in
  let stringToInit (extra_nul : bool) : (offset * init) list =
    let chars =
      let rec allChars i acc =
        if i < 0 then acc
        else allChars (i - 1) ((s_get i) :: acc)
      in
      allChars (-1 + s_length)
        (if extra_nul then [(CChr (Char.chr 0)) ; (CChr (Char.chr 0))]
            else [(CChr (Char.chr 0))] )
    in
    let _, initl' =
      List.fold_left
        (fun (idx, acc) chr ->
          (idx + 1, (Index(integer idx, NoOffset),
                     SingleInit(Const(chr)))
           :: acc))
        (0, [])
        chars
    in
    List.rev initl'
  in
  if N.isT k then begin
    let kno_t = N.stripT k in
    let strtno_t =
      match strt with
        TPtr(chrt, a) -> TPtr(chrt, [N.k2attr kno_t])
      | _ -> E.s (bug "Making a string of a non char type\n")
    in
    let s1, fe = stringLiteral s_get s_length strtno_t thisCharType in
    (* Now cast it to the desired string type *)
    let s2, fe' = castTo fe fixChrPtrType in
    append s1 s2, fe'
  end else begin
    match  k with
      N.Wild ->
        (* Make a global variable that stores this one, so that we can
        * attach a tag to it  *)
        let l = 1 + s_length in
        let newt = tagType (TArray(thisCharType, Some (integer l), [])) in
        let gvar = makeGlobalVar (newStringName ()) newt in
        gvar.vstorage <- Static;
        let init = CompoundInit (newt, stringToInit false) in
        let varinit, dfield =  makeTagCompoundInit newt (Some init) in
        theFile :=
           consGlobal (GVar (gvar, {init=Some varinit}, !currentLoc)) !theFile;
        let result = StartOf (Var gvar, Field(dfield, NoOffset)) in
        let voidStarResult = castVoidStar result in
        (* Register the area *)
        let regarea =
          registerArea
            [ integer CC.registerAreaTaggedInt;
              voidStarResult; zero ] !extraGlobInit
        in
        (* Add the registration to the global initializer *)
        if regarea != !extraGlobInit then extraGlobInit := regarea;
        (empty,
         mkCureexp fixChrPtrType result (emBase (castVoidStar result)))

    | N.Seq | N.Safe | N.FSeq | N.String | N.ROString | N.SeqN | N.FSeqN |
      N.SeqC | N.SafeC | N.FSeqC | N.SeqNC | N.FSeqNC ->
        (* sm: to allow FSeq and ROStrings to coexist, always add another *)
        (* null byte, and let the user access everything up to, but *not* *)
        (* including, that last byte *)
        (* old: let l = (if isNullTerm k then 0 else 1) + String.length s in *)
        (*
        let fatString =
          if !N.useStrings then
            s ^ "\000"
          else
            s
        in
        *)
        (* Make a global array that stores this string. This way we can
        * register the area just once in the global initializer. *)
        let l = 1 + s_length +
            (if !N.useStrings && !N.extendStringBuffers then 1 else 0) in
        let newt = TArray(thisCharType, Some (integer l), []) in
        let gvar = makeGlobalVar (newStringName ()) newt in
        gvar.vstorage <- Static;
        let start = AddrOf (Var gvar, Index(zero, NoOffset)) in
        let addExtraNul = !N.useStrings && !N.extendStringBuffers in
        let inits = stringToInit addExtraNul in
        let init =  CompoundInit(newt, inits) in
        theFile := consGlobal (GVar (gvar, {init=Some init}, !currentLoc)) !theFile;
        (* Get the end so that we can make a SEQ *)
        let theend = BinOp(IndexPI, start, integer l, charPtrType) in
        (* Register the area *)
        let regarea =
          registerArea
            [ integer CC.registerAreaSeqInt;
              castVoidStar start;
              castVoidStar theend ] !extraGlobInit
        in
        (* Add the registration to the global initializer *)
        if regarea != !extraGlobInit then extraGlobInit := regarea;
        let em =
          match k with
            N.Safe | N.SafeC | N.String | N.ROString ->
              emNone
          | N.Seq | N.SeqN | N.SeqC | N.SeqNC ->
              emBaseEnd start theend
          | N.FSeq | N.FSeqN | N.FSeqC | N.FSeqNC ->
              emEnd theend
          | _ -> E.s (bug "stringLiteral")
        in
        let em' = if N.isC k then emSetMetaPtr em zero else em in
        let res = mkCureexp fixChrPtrType start em' in
        (empty, res)

    | _ -> E.s (unimp "String literal to %a" N.d_opointerkind k)
  end

(*************** Handle Allocation ***********)
let pkAllocate (ai:  allocInfo) (* Information about the allocation function *)
               (dest:  lval)   (* Where to put the result *)
               (f:  exp)        (* The allocation function *)
               (args: exp list) (* The arguments passed to the allocation *)
    : stmt clist =
  (*(trace "malloc" (dprintf "Al@[location call of %a.@?type(vi) = %a@!@] vtype = %a@!"*)
  (*                         d_exp f d_plaintype vi.vtype*)
  (*                         d_plaintype vtype));*)
  let destt = typeOfLval dest in
  let k = kindOfType destt in
  let kno_t = N.stripT k in
  (* Get the size *)
  let sz = ai.aiGetSize args in
  (* See if we must zero *)
  let mustZero = not ai.aiZeros in
  (* Round up the size to be allocated *)
  let nrdatawords, nrtagwords = tagLength sz in
  (* Words to bytes converter *)
  let wrdsToBytes wrds =
    BinOp(Shiftlt, mkCast wrds uintType, integer 2, uintType) in
  let nrdatabytes = wrdsToBytes nrdatawords in

  (* Find the pointer type and the offset where to save it *)
  let ptrtype, dest_ptr =
    match k with
    | N.Wild | N.Seq | N.FSeq | N.SeqN | N.FSeqN | N.Index
    | N.WildC | N.SeqC | N.FSeqC | N.SeqNC | N.FSeqNC | N.SafeC ->
        if isFatType destt then
          let t = getTypeOfFat "pkAllocate" destt in
          let fptr, _ = getFieldsOfFat "pkAllocate" destt in
          t, addOffsetLval fptr dest
        else
          destt, dest
    | N.Safe | N.String | N.ROString
    | N.WildT | N.SeqT | N.FSeqT | N.SeqNT | N.FSeqNT | N.IndexT
      -> destt, dest
    | N.Scalar ->
        E.s (error "You are casting the result of an allocation to a scalar type (%a). You will not be able to use this allocated memory!" d_type destt)

    | _ -> E.s (unimp "pkAllocate: ptrtype (%a)" N.d_opointerkind k)
  in
  (* Get the base type *)
  let basetype =
    match unrollType ptrtype with
      TPtr(bt, _) -> bt
    | _ -> E.s (bug "Result of allocation is not a pointer type")
  in

  (* Figure out how much extra space we need for metadata by scaling
   * according to the ratio of metadata size to data size *)
  let nrmetabytes =
    if N.isC k then
      match metaDataType (unrollType basetype) with
        Some metat ->
          BinOp (Div,
                 BinOp (PlusA,
                        BinOp (Mult, nrdatabytes, SizeOf metat, uintType),
                        BinOp (MinusA, SizeOf basetype, one, uintType),
                        uintType),
                 SizeOf basetype,
                 uintType)
      | None -> zero
    else
      zero
  in

  (* Compute the size argument to be passed to the allocator *)
  let allocsz =
    match kno_t with
      N.Wild ->
        wrdsToBytes (BinOp(PlusA, nrdatawords,
                           BinOp(PlusA, nrtagwords, kinteger IUInt 1,
                                 uintType), uintType))
    | N.Index ->
        wrdsToBytes (BinOp(PlusA, nrdatawords, kinteger IUInt 1, uintType))
    | _ ->
        if nrmetabytes = zero then
          nrdatabytes
        else
          BinOp (PlusA, nrdatabytes, nrmetabytes, uintType)
  in
      (* Call the allocation function and put the result in a temporary *)
  let tmpp = makeTempVar !CC.currentFunction ptrtype in
  let tmpvar = Lval(var tmpp) in
  let alloc = call (Some (var tmpp)) f (ai.aiNewSize allocsz args) in
  (* Adjust the allocation pointer past the size prefix (if any) *)
  let adjust_ptr =
    match kno_t with
      N.Index | N.Wild ->
        mkSet (var tmpp) (mkCast (BinOp(IndexPI,
                                        mkCast tmpvar charPtrType,
                                        integer 4, charPtrType))
                            ptrtype)
    | _ -> mkEmptyStmt ()
  in

  (* Save the pointer value into the final result *)
  let assign_p = mkSet dest_ptr tmpvar in


  (* And the base, if necessary. This one is equal to the pointer value *)
  let assign_base =
    if pkHas MKBase k then begin
      (* Get the metadata fields for the destination type *)
      let baseo = getOneFieldOfFat "pkAllocate::assign" MKBase destt in
      mkSet (addOffsetLval baseo dest)
             (mkCast tmpvar voidPtrType)
    end else
      mkEmptyStmt ()
(*
    match k with
      N.Wild | N.Seq | N.SeqN | N.SeqC | N.SeqNC | N.Index -> begin
        let _, fbaseo, _, _ = getFieldsOfFat  in
        match fbaseo with
          Some fbase -> (mkSet (addOffsetLval fbase dest)
                           (mkCast tmpvar voidPtrType))
        | _ -> mkEmptyStmt ()
      end
    | _ -> mkEmptyStmt ()
*)
  in

  (* Store the size in memory if necessary *)
  let setsz =
    match kno_t with
      N.Wild | N.Index ->
        mkSet (Mem(BinOp(PlusA,
                         mkCast tmpvar uintPtrType,
                         mone, uintPtrType)),
               NoOffset)
          nrdatawords
    | _ -> mkEmptyStmt ()
  in

  (* Now the remainder of the initialization *)
  let init =
    match kno_t with
      N.Wild ->
        (* Zero the tags *)
        if mustZero then
          single (call None
                    (Lval (var CC.checkZeroTagsFun.svar))
                    [ tmpvar;                      (* base *)
                      nrdatawords;                 (* basenrwords *)
                      tmpvar;                      (* where to start *)
                      nrdatabytes;                 (* size of area to zero *)
                      (* zero  *) ])
        else
          single (mkEmptyStmt ())
    | N.Safe | N.SafeC ->
        (* Check that we have allocated enough for at least 1 elem. *)
        let check_enough =
          call None (Lval (var CC.checkPositiveFun.svar))
            [ BinOp(MinusA, mkCast nrdatabytes intType,
                    mkCast (SizeOf(basetype)) intType, intType) ] in
        (* Compute the end *)
        let theend = BinOp(PlusPI, mkCast tmpvar uintType,
                           nrdatabytes, uintType) in
        (* Now initialize. *)
        let inits =
          initializeType basetype mustZero
            (Some theend) (mkMem tmpvar NoOffset) empty
        in
        (* We need to set tmpvar so that metadata is set correctly. *)
        (* TODO: only necessary when SafeC has metadata *)
        let settmp =
          match kno_t with
            N.Safe -> mkEmptyStmt ()
          | N.SafeC -> mkSet (var tmpp) (mkCast theend ptrtype)
          | _ -> E.s (bug "unexpected kind")
        in
        CConsL (check_enough, CConsR (inits, settmp))

    | N.Seq | N.FSeq | N.SeqN | N.FSeqN |
      N.SeqC | N.FSeqC | N.SeqNC | N.FSeqNC | N.Index ->
        (* Compute and save the end of the type *)
        let savetheend, theend =
          let tmpend = makeTempVar !CC.currentFunction uintType in
          mkSet (var tmpend)
            (BinOp(PlusPI, mkCast tmpvar uintType,
                   nrdatabytes, uintType)),
          Lval (var tmpend)
        in
        (* Now initialize. Use the tmp variable to iterate over a number of
         * copies.  *)
        let initone =
          initializeType basetype mustZero None
            (mkMem tmpvar NoOffset) empty

        in
        let initializeAll =
          if initone = empty then
            single (mkSet (var tmpp) (mkCast theend ptrtype))
          else
            (* Note that this loop will leave theend to point right past the
             * last initialized element. This might be before the end of the
             * allocated area if the size of the allocated area is not a
             * multiple of the element size *)
            fromList
              (mkFor
                 ~start:[mkEmptyStmt ()]
                 ~guard:(BinOp(Le, BinOp(PlusA,
                                         mkCast tmpvar !upointType,
                                         SizeOf(basetype), !upointType),
                               mkCast theend !upointType, intType))
                 ~next:[mkSet (var tmpp)
                           (BinOp(IndexPI, tmpvar, one, ptrtype))]
                 ~body:(toList initone))
        in
        let initNullterm : stmt clist =
          if isNullTerm k then begin (* FSeqN, etc *)
            (* This works only for setting to null a character only *)
            let plast = BinOp(MinusPI, tmpvar, one, ptrtype) in
            (* Make a zero initializer for the right type *)
            let zeroi = makeZeroInit basetype in
            let rec setLastToZero (off: offset)
                                  (i: init)
                                  (t: typ)
                                  (acc: stmt clist) : stmt clist =
              match i with
                SingleInit e ->
                  CConsR (acc, mkSet (Mem plast, off) (mkCast zero t))

              | CompoundInit (t, initl) ->
                  foldLeftCompound ~implicit:true
                                   ~doinit:setLastToZero
                                   ~ct:t
                                   ~initl:initl
                                   ~acc:acc
            in
            setLastToZero NoOffset zeroi basetype empty
          end else
            empty
        in
        CConsL(savetheend,
               append initializeAll initNullterm)


    | N.String | N.ROString -> (* Allocate this as SeqN, with a null term *)
        ignore (warn "Allocation of string. Use FSEQN instead. (%a)"
                  d_lval dest);
        single (mkSet (Mem(BinOp(PlusPI,
                                   mkCast tmpvar charPtrType,
                                   (nulltermArrayEndIndex nrdatabytes),
                                   charPtrType)), NoOffset)
                  (mkCast zero charType))

    | _ -> E.s (bug "pkAllocate: init")
  in
  (* Now assign the end if necessary. We do it this late because in the case
   * of sequences we now know the precise end of the allocated sequence. For
   * them the tmp variable has iterated over a number of instances of the
   * type and has stopped when there is not more room for one more instance. *)
  let assign_end =
    if pkHas MKEnd k then begin
      let endp =
        if isNullTerm k then(* FSeqN, etc. Subtract 1 element from the size. *)
          (nulltermPointerEnd tmpvar ptrtype)
        else
          tmpvar
      in
      let fendo = getOneFieldOfFat "pkAllocate::assign_end" MKEnd destt in
      mkSet (addOffsetLval fendo dest) endp
    end else
      mkEmptyStmt ()
  in

  (* Now assign the meta pointer and initialize its contents if necessary. *)
  let init_meta =
    if pkHas MKMetaPointer k then
      (* Get the type of the meta pointer from the destination variable.
       * Get the corresponding base type out of this pointer type. *)
      let fmetao =
        getOneFieldOfFat "pkAllocate::assign_meta" MKMetaPointer destt in
      let metalv = addOffsetLval fmetao dest in
      let metaptrtype = typeOfLval metalv in
      let metabasetype =
        match unrollType metaptrtype with
          TPtr (bt, _) -> bt
        | _ -> E.s (bug "Meta pointer doesn't have a pointer type")
      in
      (* Create a temporary variable to hold the meta pointer.  It should
       * be initialized to the end of the data part of the allocated
       * chunk; that is, it's at dest_ptr + nrdatabytes.  (Note that we
       * can't use tmpvar, since it was modified during initialization.)
       * Set the meta pointer of the result to this value. *)
      let tmpmp = makeTempVar !CC.currentFunction metaptrtype in
      let tmpmvar = Lval (var tmpmp) in
      let set_tmp =
        mkSet (var tmpmp)
              (mkCast (BinOp (PlusPI, mkCast (Lval dest_ptr) charPtrType,
                              nrdatabytes, charPtrType))
               metaptrtype)
      in
      let set_ptr = mkSet metalv tmpmvar in
      (* Now initialize the metadata according to the pointer kind. *)
      let init =
        match k with
        | N.SafeC ->
            (* Check that we have allocated enough for at least 1 elem. *)
            let check_enough =
              call None (Lval (var CC.checkPositiveFun.svar))
                [ BinOp(MinusA, mkCast nrmetabytes intType,
                        mkCast (SizeOf(metabasetype)) intType, intType) ] in
            (* Compute the end *)
            let theend = BinOp(PlusPI, mkCast tmpmvar uintType,
                               nrmetabytes, uintType) in
            (* Now initialize. *)
            let inits =
              initializeType metabasetype mustZero
                (Some theend) (mkMem tmpmvar NoOffset) empty
            in
            CConsL (check_enough, inits)

        | N.SeqC | N.FSeqC | N.SeqNC | N.FSeqNC ->
            (* Compute and save the end of the metadata array. *)
            let savetheend, theend =
              let tmpend = makeTempVar !CC.currentFunction uintType in
              mkSet (var tmpend)
                (BinOp(PlusPI, mkCast tmpmvar uintType,
                       nrmetabytes, uintType)),
              Lval (var tmpend)
            in
            (* Now initialize. Use the tmp variable to iterate over a number of
             * copies.  *)
            let initone =
              initializeType metabasetype mustZero None
                (mkMem tmpmvar NoOffset) empty
            in
            (* Now repeat the initialization for all elements in the metadata
             * array. *)
            let initializeAll =
              if initone = empty then
                single (mkSet (var tmpmp) (mkCast theend metaptrtype))
              else
                fromList
                  (mkFor
                     ~start:[mkEmptyStmt ()]
                     ~guard:(BinOp(Le, BinOp(PlusA,
                                             mkCast tmpmvar !upointType,
                                             SizeOf(metabasetype), !upointType),
                                   mkCast theend !upointType, intType))
                     ~next:[mkSet (var tmpmp)
                               (BinOp(IndexPI, tmpmvar, one, metaptrtype))]
                     ~body:(toList initone))
            in
            CConsL(savetheend, initializeAll)

        | _ -> empty
      in
      CConsL (set_tmp, CConsL (set_ptr, init))
    else
      empty
  in

  (* Now see if we must register the whole area *)
  let register_area =
    match kno_t with
    | N.Safe -> empty
    | N.Wild | N.Index ->
        let areaKind =
          if kno_t = N.Wild then
            CC.registerAreaTaggedInt else CC.registerAreaSizedInt
        in
        registerArea [ integer areaKind;
                       castVoidStar (Lval dest_ptr);
                       zero ] empty
    | N.Seq | N.SeqN | N.FSeq | N.FSeqN | N.String | N.ROString ->
        registerArea [ integer CC.registerAreaSeqInt;
                       castVoidStar (Lval dest_ptr);
                       castVoidStar tmpvar ] empty
    | N.SafeC | N.SeqC | N.SeqNC | N.FSeqC | N.FSeqNC ->
        (* TODO: safec may want to register its metadata; also, other
         * types can't reuse the code above because tmpvar != e *)
        if !N.useLeanFats then
          E.s (unimp "pkAllocate: we don't register compatible pointers");
        empty
    | _ -> E.s (bug "pkAllocate: register_area: %a" N.d_opointerkind k)
  in
  let initialize_whennotnull =
         CConsL(adjust_ptr,
                CConsL(assign_p,
                       CConsL(assign_base,
                              CConsL(setsz,
                                     append init
                                       (CConsL(assign_end,
                                               append init_meta
                                                      register_area))))))
  in
  let initialize_null =
    let setMetaInstrs =
      if isFatType destt then
        (* set each metadata field to the null value. *)
        let nullptrmeta = pkMakeScalarMeta k in
        let poff, metaoffs = getFieldsOfFat "pkAllocate::null" destt in
          List.fold_right
            (fun (mk, off) acc ->
               let meta = emGet mk "pkAllocate::null" nullptrmeta in
               (* meta will usually be 0, except perhaps for RTTI metadata *)
                 Set(addOffsetLval off dest, meta, !currentLoc)
                 ::acc)
            metaoffs
            []
      else
        []
    in
    (* and set the pointer itself to null *)
    single (mkStmt (Instr (Set(dest_ptr,
                               Cil.zero,
                               !currentLoc)
                           :: setMetaInstrs)))
  in
  let initialize =
    single (mkStmt(If(tmpvar,
                     mkBlock (toList initialize_whennotnull),
                     mkBlock (toList initialize_null),
                              !currentLoc)))
  in
  CConsL(alloc, initialize)

(* Given a sized array type, return the size and the array field *)
let getFieldsOfSized (t: typ) : fieldinfo * fieldinfo =
  match unrollType t with
   TComp (comp, _) when comp.cstruct -> begin
      match comp.cfields with
        s :: a :: [] when s.fname = "_size" && a.fname = "_array" -> s, a
      | _ -> E.s (bug "getFieldsOfSized")
    end
   | _ -> E.s (bug "getFieldsOfSized %a\n" d_type t)

(* Scan a list of types and compute a list of qualifiers that distinguish the
 * various possible combinations of qualifiers
 * If you call this with the optional hashtable, mangleTypes will populate
 * the table with all of the non-SAFE nodes that caused this mangling. *)
let mangleTypes (deep: bool) ?(mangledNodes: N.node IH.t option)
  (types: typ list) : string =
  (* Keep a hash table of composite types that we have descended into
   * already. This way we'll detect recursion. *)
  let doNotMangleComp: int list ref = ref [] in
  let recordMangledNode : typ -> unit =
    match mangledNodes with
      Some table ->
        (fun t -> match N.nodeOfAttrlist (typeAttrs t) with
           Some n -> IH.add table n.N.id n
         | None -> ())
    | None -> (fun t -> ())
  in
  let rec qualNames (acc: string list) = function
      TInt _ | TFloat _ | TVoid _ | TEnum _ -> acc
    | TPtr(t', _) as t ->
        let pk = kindOfType t in
        (* See if this is a modified va_list *)
        let acc' =
          match unrollType t' with
            TComp(ci, _) when ci.cstruct
              && prefix "__ccured_va_list" ci.cname ->
                "v" :: acc
          | _ -> acc
        in
        if pkHasMeta pk then
          recordMangledNode t;
        pkQualName pk acc' (fun acc'' -> qualNames acc'' t')
    | TArray(t', _, a) as t->
        let acc' =
          (* Choose the attributes so that "s" is always the C represent *)
          if filterAttributes "sized" a <> [] then begin
            recordMangledNode t;
            "l" :: acc
          end else "s" :: acc
        in
        qualNames acc' t'
    | TFun(tres, args, _, _) ->
        let acc' = qualNames acc tres in
        List.fold_left
          (fun acc (_, at, _) -> qualNames acc at) acc' (argsToList args)

    | TNamed (t, _) -> qualNames acc t.ttype

    (* We only go into struct that we created as part of "sized" or
     * "seq" or "fatp". Or if the struct is polymorphic itself, we get
     * and use its mangling. Or, we go into structs if we use
     * deepMangling. *)
    | (TComp (comp, _) as t) -> begin
        if isFatComp comp then
          (* If it is one of our fat type, we mangle the _p field. It carries
           * the pointer kind and the base type *)
          qualNames acc (getTypeOfFat "mangleTypes" t)
        else
          match comp.cfields with
          | [s;a] when s.fname = "_size" && a.fname = "_array" ->
              qualNames acc a.ftype
          | _ ->
              if deep || Poly.isPolyName comp.cname then begin
                (* It is polymorphic *)
                if List.exists (fun x -> x = comp.ckey) !doNotMangleComp then
                  acc
                else begin
                  doNotMangleComp := comp.ckey :: !doNotMangleComp;
                  (* For a union, use the longest field *)
                  let fields_todo =
                    if comp.cstruct then
                      comp.cfields
                    else begin
                      let longestField, _ =
                        List.fold_left
                          (fun ((_, accl) as acc) f ->
                            let thissz =
                              try bitsSizeOf f.ftype with SizeOfError _ -> 0 in
                            if thissz > accl then
                              (Some f, thissz)
                            else
                              acc)
                          (None, 0)
                          comp.cfields
                      in
                      match longestField with
                        Some f -> [ f ]
                      | _ -> []
                    end
                  in
                  let this =
                    List.fold_left qualNames
                      []
                      (List.map (fun f -> f.ftype) fields_todo)
                  in
                  (* If there are any non-safe pointers inside *)
                  if List.exists (fun m -> m <> "s") this then
                     "_" :: (this @ ("c" :: acc))
                  else
                     acc
                end
              end else
                acc
    end
    | _ -> E.s (E.bug "mangleTypes:builtin")
  in
  let quals = List.fold_left qualNames [] types in
  let rec allSafe = function (* Only default qualifiers *)
      [] -> true
    | ("s"|"c"|"_") :: rest -> allSafe rest
    | _ -> false
  in
  if allSafe quals then ""
  else (List.fold_left (fun acc x -> x ^ acc) "" quals)

let mangleSuffixForVar ~(showwhy:bool) (deep: bool) (name: string)(t: typ)
  : string =
  if showwhy then begin
    let nodes = IH.create 19 in
    let res = mangleTypes deep ~mangledNodes:nodes [t] in
    let nodes' = List.fast_sort (fun (id1,n1) (id2,n2) -> id2 - id1)
                   (IH.tolist nodes)
    in
    if res <> "" then begin
      E.log "Global %s mangled to %s_%s because of these nodes:\n"
        name name res;
      List.iter
        (fun (id, n) -> E.log "   NODE(%d) at %a\n" id d_loc n.N.loc)
        nodes';
      E.log "\n";
    end;
    res
  end
  else
    mangleTypes deep [t]

let mangleSuffixForComp (comp: compinfo) : string =
  mangleTypes false (List.map (fun f -> f.ftype) comp.cfields)

(* Find the structures whose mangling is non-empty and which are referenced
 * from the external globals *)
let printDeepManglingWarnings (f: file) =
  (* Keep here the compinfo that we have done *)
  let doneCompinfo: (string, unit) H.t = H.create 113 in
  let checkGlobalType (globname: string) (t: typ) =
    ignore (existsType
      (fun t ->
        match t with
          TComp (ci, _) when not (H.mem doneCompinfo ci.cname) ->
            if mangleSuffixForComp ci <> "" then begin
              let ci_decl_loc =
                try snd (H.find MU.allCompinfo ci.cname)
                with Not_found -> locUnknown
              in
              ignore (E.warn "Fields in external structure %s (%a) are incompatible (used in the type of %s (%a))"
                        ci.cname d_loc ci_decl_loc
                        globname d_loc !currentLoc)
            end;
            H.add doneCompinfo ci.cname ();
            ExistsMaybe
        | _ -> ExistsMaybe)
      t)
  in
  let isGlobal (name: string) = MU.isImported (Poly.stripPoly name) in
  let doOneGlobal = function
      GVar (v, _, l) | GVarDecl (v, l) when isGlobal v.vname ->
        currentLoc := l;
        checkGlobalType v.vname v.vtype

    | GFun (f, l) when isGlobal f.svar.vname ->
        currentLoc := l;
        checkGlobalType f.svar.vname f.svar.vtype

    | _ -> ()
  in
  List.iter doOneGlobal f.globals

let fixupGlobName vi =
  (* weimer: static things too! *)
  if vi.vglob && (* vi.vstorage <> Static &&  *)
    (* not (isAllocFunction vi.vname) && It is Ok to mangle the name of
     * allocators since the result is not a pointer *)
    not (H.mem mangledNames vi.vname) then
    begin
      (* For vararg functions we pretend that the type also contains the
       * union elements *)
      let vitype =
        match vi.vtype with
          TFun (rt, args, true, a) -> begin
            match filterAttributes "ccuredvararg" a with
              [Attr(_, [ASizeOf t])] ->
                let types =
                  match t with
                    TComp(ci, _) -> List.map (fun f -> f.ftype) ci.cfields
                  | _ -> [t]
                in
                let args' =
                  match args with
                    Some a ->
                      Some (a @ (List.map (fun t -> ("", t, [])) types))
                  | _ -> E.s (bug "vararg function without prototype")
                in
                TFun(rt, args', true, a)
            | _ -> vi.vtype
          end
        | _ -> vi.vtype
      in
      (* See if this global is imported *)
      let deepMangle =
        not !MU.shallowMangling
          && (MU.isImported (Poly.stripPoly vi.vname))
      in
      let suffix = mangleSuffixForVar ~showwhy:!showMangleReasons
                     deepMangle vi.vname vitype in
      let suffix =
        (* If we put the t suffix we don't really need the rest, because
         * those would be only WILD  *)
        if mustBeTagged vi then "t" (* ^ suffix *)
        else
          (* old: Tagged functions also get the t suffix *)
          (* weimer: Why do tagged functions get the t suffix? they already
           * have the "w" suffix. Suffices help us to resolve linking
           * problems, but all of the function descriptor stuff associated
           * with the tagged function is done at the call site. A tagged and
           * an untagged wild function link the same way.  *)
          (* gn: Tagging is meant to denote different calling conventions.
           * The t suffix means that the function takes only WILD pointers
           * and returns a WILD pointer. the w suffix means that it might
           * take some WILD pointers as arguments or results.  *)
          if isFunctionType vi.vtype && hasAttribute "tagged" vi.vattr then
            "t" (* ^ suffix *)
          else suffix
      in
      let newname =
        if suffix = "" then vi.vname else vi.vname ^ "_" ^ suffix in
      H.add mangledNames newname (vi.vname, suffix);
      vi.vname <- newname
    end

class unsafeVisitorClass = object
  inherit nopCilVisitor

  method vlval (lv: lval) : lval visitAction =
    (* Do everything after we handle the children *)
    (* Add offset to go into fat types *)
    let rec fixLastOffset (lv: lval) : lval =
      let t = typeOfLval lv in
      match unrollType t with
        TComp (comp, _) when comp.cstruct -> begin
          match comp.cfields with
            (* A sized array *)
            f1 :: f2 :: [] when (f1.fname = "_size" && f2.fname = "_array") ->
              fixLastOffset (addOffsetLval (Field(f2, NoOffset)) lv)
            (* A tagged struct *)
          | f1 :: f2 :: _ when (f1.fname = "_len" && f2.fname = "_data") ->
              fixLastOffset (addOffsetLval (Field(f2, NoOffset)) lv)
          | f1 :: _ when f1.fname = "_p" || f1.fname = "_d" ->
              fixLastOffset (addOffsetLval (Field(f1, NoOffset)) lv)
          | _ -> lv
        end
      | _ -> lv
    in
    let rec fixOffsets (lv: lval) (off: offset) =
      match off with
        NoOffset -> lv
      | Field (fi, off) ->
          fixOffsets
            (fixLastOffset (addOffsetLval (Field (fi, NoOffset)) lv))
            off
      | Index (e, off) ->
          fixOffsets
            (fixLastOffset (addOffsetLval (Index (e, NoOffset)) lv))
            off
    in
    let doafter (lv: lval) =
      match lv with
        Var v, off ->
          let lv0 = fixLastOffset (Var v, NoOffset) in
          fixOffsets lv0 off
      | Mem e, off ->
          let lv0 = fixLastOffset (mkMem e NoOffset) in
          fixOffsets lv0 off
    in
    ChangeDoChildrenPost (lv, doafter)
end

let unsafeVisitor = new unsafeVisitorClass

(* Make an cureexp out of a single expression. Either the type is fat and a
 * composite value is denoted by a single expression or the type is lean. *)
let curelval2cureexp (lv: curelval) : cureexp =
  let k = kindOfType lv.lvt in
  if isSplitType lv.lvt then
    let em =
      match metaDataType lv.lvt with
        Some t' -> readFieldsOfMeta t' (mkMem (emGetMetaPtr lv.lvm) NoOffset)
      | None -> emNone
    in
    { et = lv.lvt; ek = k; ep = Lval lv.lv; em = em }
  else
    let pt, _p, _em = readFieldsOfFat (Lval lv.lv) lv.lvt in
    let _em' = (* For tagged unions, we set the RTTI metadata of lv.lvm
                 explicitly.  Preserve this metadata here.
                 Not supported for split types. *)
      if not (emHas MKRtti _em) && emHas MKRtti lv.lvm then
        emSet MKRtti _em (emGet MKRtti "curelval2cureexp" lv.lvm)
      else
        _em
    in
    { et = lv.lvt; ek = k; ep = _p; em = _em' }

let optimizeFSeqArithChecks (blv: curelval)
                            (dolv: stmt clist)
                            (checkaccess: stmt clist) =
  (* Look here for the common case *(p + i) for a FSEQ pointer. Remove the
   * FSEQARITH check from dolv and strengthed the FSEQ2SAFE check from
   * "check" *)
  try
    match blv.lv with
      Mem (BinOp((PlusPI|IndexPI), p, i, TPtr(bt, a)) as ppi), off
        when blv.plvk = N.FSeq ->
          (* Now go and look for the FSEQARITH from dolv *)
          let foundFSeqArithCheck = ref None in
          Clist.iter
            (fun s ->
              match s.skind with
                Instr [ Call(None, Lval (Var fseqarith, NoOffset),
                             [ CastE(_, p'); _; CastE(_, ppi');
                               _; checkAlign],
                             _)
                      ]
                  when fseqarith.vname = "CHECK_FSEQARITH" ->
                    if p' == p && ppi' == ppi then
                      foundFSeqArithCheck := Some (s, checkAlign)

              | Instr [ Call(_, Lval (Var fseqarith, _), _, _) ]
                  when fseqarith.vname = "CHECK_FSEQARITH" ->
                  E.s (bug "bad call %a\n" d_stmt s);

              | _ -> ())
            dolv;
          (* Now look for the FSEQ2SAFE check in check *)
          let foundFseq2SafeCheck = ref false in
          Clist.iter
            (fun s ->
              match s.skind with
                Instr [ Call(None, Lval (Var fseq2safe, NoOffset),
                             [ bend; CastE(_, ppi'); origsz; sz; foracc;
                               noint ],
                             l)
                      ]
                  when fseq2safe.vname = "CHECK_FSEQ2SAFE" &&
                ppi' == ppi ->
                  begin
                    match !foundFSeqArithCheck with
                      None ->
                        ignore (warn "Found FSEQ2SAFE but no FSEQARITH check");
                        raise Not_found
                    | Some (arith_s, checkAlign) ->
                        (* Remove the Arith check *)
                        arith_s.skind <- Instr [];
                        (* And replace this check *)
                        s.skind <-
                           Instr [ Call(None,
                                        Lval (var CC.checkFSeqArith2SafeFun.svar),
                                        [ castVoidStar p;
                                          bend;
                                          castVoidStar ppi;
                                          origsz;
                                          sz; foracc;
                                          noint;
                                          checkAlign], l) ];
                        foundFseq2SafeCheck := true;
                        ()
                                 end

              | _ -> ())
            checkaccess;

          if !foundFseq2SafeCheck then
            raise Not_found;
          ()

    | _, _ -> ()
  with Not_found -> ()

(*
 * *** Metadata Generation ***
 *
 * The following functions are used to generate code that automatically
 * generates metadata.  The basic idea is that for each type, we will
 * create a function of the following form:
 *
 *   __metagen_t(meta(t) *md, t d, int len, void *ctx);
 *
 * Given data d of type t, this function allocates and initializes
 * metadata *md of type meta(t).  (If t is a struct, we pass by reference
 * instead of by value for efficiency.)
 *
 * The len field indicates the size of the area; for instance, if type t
 * is char * __FSEQ, then len indicates the size of the underlying
 * string.  Annotations are used to determine len.
 *
 * The ctx field is used to pass context from enclosing types.  This
 * feature can be used if the length of an area is stored at a higher
 * level than the pointer to the area itself.
 *)

(* Types corresponding to metadata annotations. *)
type mdsize =
  | MDSizeNullTerm
  | MDSizeFixed of int
  | MDSizeField of string
  | MDSizeContext

(* Given a type, return the corresponding size annotation. *)
let getMDSize (t: typ) : mdsize =
  let rec searchAttrs (attrs: attribute list) : mdsize =
    match attrs with
      (Attr (_, [ACons ("nullterm", [])]))      :: _ -> MDSizeNullTerm
    | (Attr (_, [ACons ("context", [])]))       :: _ -> MDSizeContext
    | (Attr (_, [ACons ("fixed", []); AInt n])) :: _ -> MDSizeFixed n
    | (Attr (_, [ACons ("field", []); AStr s])) :: _ -> MDSizeField s
    | _ :: rest -> searchAttrs rest
    | [] -> MDSizeFixed 1
  in
  match t with
    TPtr (_, tattr) -> searchAttrs (filterAttributes "mdsize" tattr)
  | _ -> MDSizeFixed 1

(* Given a type (plus some extra info), figure out the length argument
 * to use when calling that type's metadata generation function. *)
let getMDLengthArg (f: fundec) (t: typ) (p: exp) (cvar: varinfo)
                   (compo: (varinfo * compinfo) option)
    : exp * stmt list =
  match getMDSize t with
    MDSizeNullTerm ->
      (* For null-terminated types, search for the null value. *)
      let tmp = makeTempVar f t in
      BinOp (PlusA, BinOp (MinusPP, Lval (var tmp), p, uintType),
             integer 1, uintType),

      [mkStmtOneInstr (Set (var tmp, p, locUnknown));
       mkStmt
         (If (Lval (var tmp),
              { battrs = [];
                bstmts = mkWhile (Lval (mkMem (Lval (var tmp)) NoOffset))
                                 [mkStmtOneInstr
                                    (Set (var tmp, increm (Lval (var tmp)) 1,
                                          locUnknown))]; },
              { battrs = []; bstmts = []; },
              locUnknown))]
  | MDSizeContext ->
      (* Pass the context on as the size. *)
      mkCast (Lval (var cvar)) uintType, []
  | MDSizeFixed n ->
      (* Use the fixed size direclty. *)
      integer n, []
  | MDSizeField s ->
      (* Use a field of the current composite type to get the length. *)
      match compo with
        Some (d, comp) ->
          Lval (mkMem (Lval (var d)) (Field (getCompField comp s, NoOffset))),
          []
      | None -> E.s (bug "getMDLengthArg: need comp for field-based size")

(* Get the context for use when generating component types' metadata.
 * Either a field in the current comp is labelled as the new context
 * or we just use the old one. *)
let getMDContext (comp: compinfo) (tvar: varinfo) (cvar: varinfo) : exp =
  try
    let fld =
      let isContext (attr: attribute) : bool =
        match attr with
          Attr ("mdsize", [AStr "mkcontext"]) -> true
        | _ -> false
      in
      List.find (fun f -> List.exists isContext f.fattr) comp.cfields
    in
    Lval (mkMem (Lval (var tvar)) (Field (fld, NoOffset)))
  with Not_found ->
    Lval (var cvar)

(* Make a type signature that ignores ptrnode attributes. *)
let ignorePtrNode al =
  let rec loop = function
      [] -> []
    | Attr(aname, _) :: rest when aname = "_ptrnode" ->
        loop rest
    | (a :: rest) as al ->
        let rest' = loop rest in
        if rest' == rest then al else a :: rest'
  in
  loop al
let typeSigMetagen t = typeSigWithAttrs ignorePtrNode t

(* Memoize the metagen functions as they're created. *)
let metagenFundecs : (typsig, fundec) H.t = H.create 123

(* This function is the main interface for metadata generation.  It
 * looks up (and creates if necessary) the metadata generation function
 * for a given type and its corresponding metadata type. *)
let rec makeMetagenFun (t: typ) (mt: typ) : fundec =
  let ts = typeSigMetagen t in
  try
    H.find metagenFundecs ts
  with Not_found ->
    let addFundec (f: fundec) : unit =
      H.add metagenFundecs ts f;
      theFile := GVarDecl (f.svar, !currentLoc) :: !theFile
    in
    match t, mt with
      TComp (comp, _), TComp (mcomp, _) ->
        (* It's a composite type. *)
        let f = emptyFunction ("__metagen_c_" ^ comp.cname) in
        addFundec f;
        (* Create all the formal arguments. *)
        let md = makeFormalVar f "md" (TPtr (mt, [])) in
        let d = makeFormalVar f "d" (TPtr (t, [])) in
        let _len = makeFormalVar f "len" uintType in
        let ctx = makeFormalVar f "ctx" voidPtrType in
        (* Now make one function call for each field that has metadata. *)
        let makeMetagenFields (fi: fieldinfo) : stmt list =
          (* Make a function to handle the field. *)
          let dfi = getCompField comp fi.fname in
          let mf = makeMetagenFun dfi.ftype fi.ftype in
          (* Apply the appropriate offsets to both data and metadata.
           * Note that we pass the address of the metadata field. *)
          let arg1 = mkAddrOf (mkMem (Lval (var md)) (Field (fi, NoOffset))) in
          let arg2 =
            let lval = mkMem (Lval (var d)) (Field (dfi, NoOffset)) in
            if isPointerType dfi.ftype then Lval lval else mkAddrOf lval
            (* TODO: other types *)
          in
          let arg3, stmts =
            getMDLengthArg f dfi.ftype arg2 ctx (Some (d, comp))
          in
          let arg4 = getMDContext comp d ctx in
          stmts @
          [mkStmtOneInstr (Call (None, Lval (var mf.svar),
                                 [arg1; arg2; arg3; arg4], locUnknown))]
        in
        let stmts = List.flatten (List.map makeMetagenFields mcomp.cfields) in
        f.sbody.bstmts <- stmts;
        f
    | TPtr (bt, _), TComp (mcomp, _) ->
        (* It's a pointer type. *)
        let pkind = kindOfType t in
        let tname = (pkTypePrefix pkind) ^ (snd (baseTypeName bt)) in
        let f = emptyFunction ("__metagen_" ^ tname) in
        addFundec f;
        (* Create all the formal arguments. *)
        let ms = makeFormalVar f "ms" (TPtr (mt, [])) in
        let p = makeFormalVar f "p" t in
        let len = makeFormalVar f "len" uintType in
        let ctx = makeFormalVar f "ctx" voidPtrType in
        (* Create some locals: the base and end for this pointer. *)
        let b = makeLocalVar f "b" t in
        let e = makeLocalVar f "e" t in
        (* Initialize b and e locals, checking the pointer p for null. *)
        let setBaseEndReal =
          mkStmt (Instr [Set (var b, Lval (var p), locUnknown);
                         Set (var e, BinOp (PlusPI, Lval (var p),
                                            Lval (var len), t),
                              locUnknown)])
        in
        let setBaseEndZero =
          mkStmt (Instr [Set (var b, zero, locUnknown);
                         Set (var e, zero, locUnknown)])
        in
        let setBaseEnd =
          mkStmt (If (BinOp (Eq, Lval (var p), zero, uintType),
                      { battrs = []; bstmts = [setBaseEndZero]; },
                      { battrs = []; bstmts = [setBaseEndReal]; },
                      locUnknown))
        in
        (* Now intialize each field of the metadata. *)
        let copyLocalToField (vi: varinfo) (mk: mkind) : stmt =
          mkStmt (Instr [Set (mkMem (Lval (var ms))
                                    (Field (getCompField mcomp
                                              (fst (fieldOfMK mk)),
                                            NoOffset)),
                              Lval (var vi), locUnknown)])
        in
        let makeMetagenFields (mk: mkind) : stmt =
          match mk with
            MKBase -> copyLocalToField b mk
          | MKEnd -> copyLocalToField e mk
          | MKRtti -> E.s (unimp "makeMetagenFun: rtti")
          | MKMetaPointer ->
              (* THe recursive metadata pointer case. *)
              let mpfld = getCompField mcomp (fst (fieldOfMK mk)) in
              let mbt =
                match mpfld.ftype with
                  TPtr (bt', _) -> bt'
                | _ -> E.s (bug "makeMetagenFun: expected metadata ptr")
              in
              (* Allocate space for the metadata, and store in the local mp. *)
              let mp = makeLocalVar f "mp" (TPtr (mbt, [])) in
              let allocate =
                let malloc =
                  Wrappers.findOrCreateFunc false "malloc" voidPtrType
                                            ["size", uintType] theFile
                in
                Call (Some (var mp), Lval (var malloc),
                      [BinOp (Mult,
                              Lval (var len),
                              SizeOfE (Lval (mkMem (Lval (var mp)) NoOffset)),
                              uintType)],
                      locUnknown)
                      (* TODO: eliminate if zero *)
              in
              (* Copy this local's value into the metadata poitner field. *)
              let assign =
                Set (mkMem (Lval (var ms)) (Field (mpfld, NoOffset)),
                     Lval (var mp), locUnknown)
              in
              (* Initialize the metadata by calling the appropriate
               * generation function. *)
              let initialize =
                let mf = makeMetagenFun bt mbt in
                let arg2 =
                  let lval = mkMem (Lval (var p)) NoOffset in
                  if isPointerType bt then Lval lval else mkAddrOf lval
                  (* TODO: other types *)
                in
                let arg3, stmts = getMDLengthArg f bt arg2 ctx None in
                let arg4 = Lval (var ctx) in
                mkFor []
                      (BinOp (Lt, Lval (var p), Lval (var e), intType))
                      [mkStmt (Instr
                       [Set (var p, increm (Lval (var p)) 1, locUnknown);
                        Set (var mp, increm (Lval (var mp)) 1, locUnknown)])]
                      (stmts @
                       [mkStmtOneInstr
                         (Call (None, Lval (var mf.svar),
                                [Lval (var mp); arg2; arg3; arg4],
                                locUnknown))])
              in
              (* Put all the code together, checking p for null. *)
              let setMPReal =
                (mkStmt (Instr [allocate; assign])) :: initialize
              in
              let setMPZero =
                mkStmtOneInstr
                  (Set (mkMem (Lval (var ms)) (Field (mpfld, NoOffset)),
                       zero, locUnknown))
              in
              mkStmt (If (BinOp (Eq, Lval (var p), zero, uintType),
                          { battrs = []; bstmts = [setMPZero]; },
                          { battrs = []; bstmts = setMPReal; },
                          locUnknown))
        in
        let stmts = List.map makeMetagenFields (H.find pkFields pkind) in
        f.sbody.bstmts <- setBaseEnd :: stmts;
        f
    | _ -> E.s (bug "makeMetagenFun: unsupported type or incorrect metadata")

(* Get a list of all the metadata generation functions we've created. *)
let getMetagenDefinitions (acc: global list) : global list =
  H.fold (fun _ f l -> GFun (f, locUnknown) :: l) metagenFundecs acc

(************* STATEMENTS **************)
let rec cureblock (b: block) : block =
  if hasAttribute "nocure" b.battrs then
    visitCilBlock unsafeVisitor b
  else begin
    let res =
      toList
        (List.fold_left
           (fun acc s -> append acc (curestmt s)) empty b.bstmts)
    in
    { bstmts = if compactBlocks then compactStmts res else res;
      battrs = b.battrs
    }
  end

and curestmt (s: Cil.stmt) : stmt clist =
   (* Keep the original statement, but maybe modify its kind. This way we
    * maintain the labels and we have no need to change the Gotos and the
    * cases in the Switch *)
  try
    match s.skind with
    | Break _ | Continue _ | Goto _ -> single s

    | ComputedGoto (e, l) ->
        currentLoc := l;
        let (_, doe, e') = cureExp (CastE(voidPtrType, e)) in
        s.skind <- Instr [];
        CConsL(s, CConsR(doe, mkStmt (ComputedGoto (e', l))))

    | Return (None, l) ->
        currentLoc := l;
        CConsL(unregisterStmt (), CSeq(CList !heapifiedFree, single s))

    | Return (Some e, l) ->
        currentLoc := l;
        let retType, _, _, _ = splitFunctionTypeVI !CC.currentFunction.svar in
        let (doe', e') = cureExpf e in
        let (doe'', e'') = castTo e' retType  in
        let (et, doe2, e2) = cureExp2exp e'' in
        let doe3 = checkReturnValue et e2 in
        let doe4 =
          append doe'
            (append doe''
               (append doe2 doe3)) in
        s.skind <- Instr [];
        CConsL(s,
               append doe4
                 (CConsL(unregisterStmt (),
                         CSeq(CList !heapifiedFree,
                              single (mkStmt (Return (Some e2, l)))))))

    | Loop (b, l, lb1, lb2) ->
        currentLoc := l;
        s.skind <- Loop (cureblock b, l, lb1, lb2);
        single s

    | Block b ->
        s.skind <- Block (cureblock b);
        single s

    | If(be, t, e, l) ->
        currentLoc := l;
        let (_, doe, e') = cureExp (CastE(intType, be)) in
        s.skind <- Instr [];
        CConsL(s,
               CConsR(doe, mkStmt (If(e', cureblock t, cureblock e, l))))
    | Instr il ->
        (* Do each instruction in turn *)
        let b =
          List.fold_left (fun acc i -> append acc (cureinstr i)) empty il in
        s.skind <- Instr [];
        CConsL (s, b)

    | Switch (e, b, cases, l) ->
        currentLoc := l;
        (* Cases are preserved *)
        let (_, doe, e') = cureExp (CastE(intType, e)) in
        s.skind <- Instr [];
        CConsL(s, CConsR(doe, mkStmt (Switch (e', cureblock b, cases, l))))

    | TryFinally (b, h, l) ->
        currentLoc := l;
        s.skind <- TryFinally (cureblock b, cureblock h, l);
        single s

    | TryExcept (b, (il, e), h, l) ->
        currentLoc := l;
        let b' = cureblock b in
        let il' =
          List.fold_left (fun acc i -> append acc (cureinstr i)) empty il in
        let (_, doe, e') = cureExp (CastE(intType, e)) in
        (* Now produce a list of instructions *)
        let il' =
          match compactStmts (toList il' @ toList doe) with
            [] -> []
          | [s] -> begin
              match s.skind with
                Instr il' -> il'
              | _ -> E.s (unimp "Wrong kind of statement after curing the __except. Try to simplify the __except expression.")
          end
          | _ -> E.s (unimp "too many statements after curing the __except. Try to simplify the __except expression.")
        in
        let h' = cureblock h in
        s.skind <- TryExcept (b', (il', e'), h', l);
        single s

  with e -> begin
    ignore (E.log "curestmt error (%s) in %s\n"
              (Printexc.to_string e) !CC.currentFunction.svar.vname);
    single (mkStmtOneInstr (dInstr (dprintf "ccurederror_statement(%a)" d_stmt s)
                              !currentLoc))
  end


and cureinstr (ins: instr) : stmt clist =
  if debugInstr then ignore (E.log "Curing %a\n" d_instr ins);
  try
    match ins with
    | Set (lv, e, l) ->
        currentLoc := l;
        let blv, dolv = cureLval lv ForWrite in
        let (doe, e') = cureExpf e in (* Assume et is the same as lvt *)
        (* Now do a cast, just in case some qualifiers are different *)
        let (doe2, e2) = castTo e' blv.lvt in
        let splitType = isSplitType blv.lvt in
        (* We convert nosplit types to a single fat exp, but
         * split types must remain separate. *)
        let ((_, doe3, e3), e3m) =
          if splitType then
            ((e2.et, empty, e2.ep), e2.em)
          else
            (cureExp2exp e2, emNone)
        in
        let check =
          match blv.lv with
            Mem _, _ ->
              checkMem (ToWrite (e3, e3m)) blv
          | Var vi, off when (vi.vglob || (blv.plvk <> N.Safe &&
                                           blv.plvk <> N.SafeC)) ->
              checkMem (ToWrite (e3, e3m)) blv
          | _ -> empty
        in
        (* If we've got a split type with metadata on our hands,
         * generate the set instruction for the metadata. *)
        let (doe4, setMeta) =
          if splitType && emHasMetaPtr blv.lvm then
            let mdest = mkMem (emGetMetaPtr blv.lvm) NoOffset in
            if isPointerType blv.lvt then
              let doe, mlv = setMetaPointer (typeOfLval mdest) e3m in
              doe, mkSet mdest (Lval mlv)
            else
              empty, mkSet mdest (emGetMetaPtr e3m)
          else
            empty, mkEmptyStmt ()
        in
        let set = mkSet blv.lv e3 in
        append dolv
          (append doe
             (append doe2
                (append doe3
                  (append doe4
                     (CConsR (CConsR (check, setMeta), set))))))

        (* Check if the result is a heapified variable *)
    | Call (Some (Var vi, NoOffset), f, args, l)
        when H.mem heapifiedLocals vi.vname ->
          currentLoc := l;
          let newb, newoff = H.find heapifiedLocals vi.vname in
          let stmt1 = cureinstr (Call (Some (newb, newoff), f, args, l)) in
          stmt1

        (* Check if this is a call to ccured_kind_of *)
    | Call(reso, Lval (Var ccured_kind_of, NoOffset), [ arg ], l)
      when prefix "__ccured_kind_of" (Poly.stripPoly ccured_kind_of.vname) ->
        begin
          (* ignore (E.log "intercepted call to %s\n" ccured_kind_of.vname); *)
          match reso with
            None -> empty
          | Some destlv -> begin
              let kndnumber =
                (* Cure the argument only to find out its kinds *)
                let _, _, arg' = cureExp arg in
                (* Drop all the casts to void-ptr *)
                let rec dropVoidPtrCasts = function
                    CastE(TPtr(TVoid _, _), a) -> dropVoidPtrCasts a
                  | a -> N.k2number (kindOfType (typeOf a))
                in
                dropVoidPtrCasts arg'
              in
              (* Finish off using cureinstr *)
              cureinstr (Set(destlv, integer kndnumber, !currentLoc))
          end
        end

        (* Check if this is a call to ccured_mangling_of *)
    | Call(reso, Lval (Var f, NoOffset), [ arg ], l)
      when (let n = Poly.stripPoly f.vname in
            prefix "__ccured_mangling_of" n ||
            prefix "__ccured_has_empty_mangling" n) ->
        begin
          (* ignore (E.log "intercepted call to %s\n" f.vname); *)
          match reso with
            None ->
              ignore (warn "The result of %s is not assigned\n" f.vname);
              empty

          | Some dest -> begin
              (* Find the mangling, it is a string literal *)
              let mangling =
                (* Cure the argument only to find its mangling *)
                let _, _, arg' = cureExp arg in
                (* Drop all the casts to void-ptr *)
                let rec dropVoidPtrCasts = function
                    CastE(TPtr(TVoid _, _), a) -> dropVoidPtrCasts a
                  | SizeOf t -> t
                  (* Special Case: when we want CCURED_MANGLING_OF(aFunction),
                     the expression aFunction will be implicitly converted to
                     a function pointer.  Instead, strip off the AddrOf and
                     look at the function type itself. *)
                  | SizeOfE (AddrOf(Var func, NoOffset))
		        when isFunctionType func.vtype ->
		      func.vtype
                  | SizeOfE e -> typeOf e
                  | a ->
                      E.s (error "ccured_mangling_of: argument should be SizeOf: it is %a\n" d_exp a)
                in
                let argType = dropVoidPtrCasts arg' in
                (* Compute the deep mangling *)
                mangleSuffixForVar ~showwhy:false
                  (not !MU.shallowMangling) "" argType
              in
              (* Finish off using cureinstr. *)
              if prefix "__ccured_mangling_of" (Poly.stripPoly f.vname) then
                (* Put the right cast in front of the string so that we know
                * what kind to make it *)
                let _, destType = extractTruePointerType (typeOfLval dest) in
                cureinstr (Set(dest,
                               CastE(destType,
                                     (Const(CStr(mangling)))), !currentLoc))
              else (* now the __ccured_has_empty_mangling *)
                let res = if mangling = "" then one else zero in
                cureinstr (Set(dest, res, !currentLoc))
          end
        end

        (* Check if this is a call to a coalesced function *)
    | Call(reso, Lval (Var f, NoOffset), args, l)
        when (f != Poly.getPolyFuncRepresentative f) ->
        cureinstr (Call(reso,
                        Lval (Var (Poly.getPolyFuncRepresentative f),
                              NoOffset),
                        args, l))

    | Call(vio, f, args, l)
      when shouldInterceptHelper f -> begin
        currentLoc := l;
        match f with
            Lval(Var fv, NoOffset) ->
              interceptHelper fv vio args
          | _ -> E.s (bug "bug in shouldInterceptHelper")
      end
    | Call(vio, f, args, l) ->
       currentLoc := l;
        let (ft, dof, f', fkind) =
          match f with
            Lval lv -> begin
              let blv, dolv = cureLval lv ForWrite in
              (* We must check this call if this is a WILD function pointer,
               * or if we are calling a function with more arguments than the
               * prototype specifies *)
              let mustCheckCall =
                match lv with
                  Mem _, _ -> true
                | Var vi, _ ->  begin
                    match blv.lvt with
                      TFun (_, Some fargs, _, _)
                        when List.length fargs < List.length args -> true
                    | TFun (_, None, _, _) -> true
                    | _ -> false
                end
              in
              let dof =
                if mustCheckCall then
                  CConsR (dolv,
                          checkFunctionPointer
                            (mkAddrOf blv.lv)
                            blv.lvm blv.plvk (List.length args))
                else
                  dolv
              in
              (* If this function has metadata, we need to call the metadata
               * pointer, not the main pointer. *)
              let lvt, flv =
                if emHasMetaPtr blv.lvm && isSplitType blv.lvt then
                  fixupType blv.lvt, mkMem (emGetMetaPtr blv.lvm) NoOffset
                else
                  blv.lvt, blv.lv
              in
              (lvt, dof, Lval flv, blv.plvk)
            end
          | _ -> E.s (unimp "Unexpected function expression")
        in
        (* If we're calling a compat library function, we want to strip
         * off metadata and call. *)
        if isCompatFunction f' then
          append dof (callCompatFunction f' vio args)
        else
        let (ftret, ftargs, isva), noProto =
          match unrollType ft with
            TFun(fret, fargs, isva, al) ->
              (fret, fargs, isva), hasAttribute "missingproto" al

          | _ -> E.s (unimp "call of a non-function: %a @!: %a"
                        d_plainexp f' d_plaintype ft)
        in
        let isallocate =
          match f' with
            Lval(Var vf, NoOffset) -> getAllocInfo vf.vname

          | _ -> None
        in
        let (doargs, args') =
          let rec doArgs restargs restargst =
            (* The types of functions have been fixed already *)
            match restargs, restargst with
              [], [] -> empty, []
            | a :: resta, (_, ft, _) :: restt ->
                let (doa, fa') = cureExpf a in
                (* ignore (E.log "cureCall: (fun = %a) a=%a\n  fa'=%a\n\n"
                            d_exp f
                            d_plainexp a d_cureexp fa');  *)
                let (doa', fa'') = castTo fa' ft in
                let (_, doa'', a2) = cureExp2exp fa'' in
                let (doresta, resta') = doArgs resta restt in
                (append doa
                   (append doa'
                      (append doa'' doresta)),  a2 :: resta')
            | a :: resta, [] ->
                (* This is a case when we call with more args than the
                 * prototype has. We better be calling a vararg or a WILD
                 * function *)
                (* Weimer: another case is that the function has no
                 * prototype! *)
                if fkind <> N.Wild && not isva then begin
                  if noProto then begin
                    E.s (bug "Calling non-wild %a with no prototype.\nYou must provide a prototype for this function." d_exp f)
                  end else
                    E.s (bug "Calling non-wild %a with too many args"
                           d_exp f)
                end ;
                let (doa, fa') = cureExpf a in
                let (doa', fa'') =
                  if isva then
                    (doa, fa')
                  else (* A WILD function *)
                    (* Do not cast if already a WILD thing *)
                    if fa'.ek = N.Wild then (doa, fa')
                    else
                      let doa'', fa'' = castTo fa'
                          (fixupType (TPtr(TVoid([]),
                                           [Attr("wild",[])]))) in
                      append doa doa'', fa''
                in
                let (_, doa'', a2) = cureExp2exp fa'' in
                let (doresta, resta') = doArgs resta [] in
                (append doa' (append doa'' doresta), a2 :: resta')
            | _ -> E.s (unimp "too few arguments in call to %a" d_exp f)
          in
          doArgs args (argsToList ftargs)
        in
        let finishcall =
          match vio with
            None -> single (call None f' args')

          | Some destlv -> begin
              let tmptype =
                if isallocate <> None then
                  (* For allocation we make the temporary the same type as
                   * the destination. The allocation routine will know what
                   * to do with it. *)
                  let bdestlv, _ = cureLval destlv ForWrite in
                  bdestlv.lvt
                else
                  (* If it is not allocation we make the temporary have the
                   * same type as the function return type. This is to
                   * prevent the situation when we would need a cast
                   * between non-scalar types *)
                  ftret
              in
              (* We want a fixed-up temporary for split types
               * since the function is going to return a merge comp. *)
              let tmptype =
                if isSplitType tmptype then
                  fixupType tmptype
                else
                  tmptype
              in
              (* Always put the result of the call in a temporary variable so
               * that the actual store into the destination occurs with a Set
               * and the right checks are inserted *)
              let tmp = makeTempVar !CC.currentFunction tmptype in
              (* Now do the call itself *)
              let thecall =
                match isallocate with
                  None -> single (call (Some (var tmp)) f' args')
                | Some ai -> pkAllocate ai (var tmp) f' args'
              in
              (* Now use cureinstr to do the code after Call properly *)
              let aftercall = cureinstr (Set(destlv, Lval (var tmp), l)) in
              (* Now put them together *)
              append thecall aftercall
          end
        in
        append dof (append doargs finishcall)

    | Asm(attrs, tmpls, outputs, inputs, clobs, l) as ins ->
        currentLoc := l;
        let rec doOutputs = function
            [] -> empty, []
          | (i, c, lv) :: rest ->
              let blv, dolv = cureLval lv ForWrite in
              let check =
                match blv.lv with
                  Mem _, _ -> checkMem (ToWrite (zero, emNone)) blv
                | _ -> empty
              in
              if isFatType blv.lvt then
                ignore (error "non-SAFE output parameter in %a\n"
                          d_instr ins);
              let (doouts, outs) = doOutputs rest in
              (append dolv (append check doouts), (i, c, blv.lv) :: outs)
        in
        let (doouts, outputs') = doOutputs outputs in

        (* Now do the inputs *)
        let rec doInputs = function
            [] -> empty, []
          | (i, c, ei) :: rest ->
              (* We make sure the expression is in an Lval first *)
              let elv, doelv =
                match ei with
                  Lval lv -> lv, empty
                | _ ->
                    let tmp = makeTempVar !CC.currentFunction (typeOf ei) in
                    cureLocal tmp;
                    let elv = var tmp in
                    elv, cureinstr (Set(elv, ei, l))
              in
              (* Now we cure the Lval *)
              let (elv', dolv) = cureLval elv ForRead in
              if isFatType elv'.lvt then
                ignore (warn "non-SAFE input parameter %a in %a\n"
                          d_exp ei d_instr ins);
              (* Cast it to a SAFE pointer. Pretend that we are accessing a
               * field. *)
              let docheck1 = checkMem ToRead elv' in
              (* IF the constraint is "m" then we will use this as a pointer *)
              let docheck2 =
                if c = "m" then
                  empty
                else
                  empty
              in
              (* Do the rest of the inputs *)
              let (doins, ins) = doInputs rest in
              (append doelv
                 (append dolv
                    (append docheck1
                       (append docheck2 doins))),
               (i, c, Lval elv'.lv) :: ins)
        in
        let (doins, inputs') = doInputs inputs in
        append doouts (CConsR(doins,
                              mkAsm attrs tmpls outputs' inputs' clobs))

  with e -> begin
    ignore (E.log "cureinstr error (%s):%a (in %s)\n"
              (Printexc.to_string e) d_instr ins !CC.currentFunction.svar.vname);
    single (mkStmtOneInstr (dInstr (dprintf "ccurederror_instruction(%a) at %t"
                                      d_instr ins d_thisloc) !currentLoc))
  end


(* This function takes care of the case where we wish to call a
 * compatible function.  Since compatible pointers are used, we simply
 * strip off the data parts to pass to the function.  WARNING: This
 * function does _not_ yet work properly if we must reconstruct or
 * validate metadata upon return. *)
and callCompatFunction (f: exp) (rlv: lval option) (args: exp list)
    : stmt clist =
  (* Cure each argument and strip off the metadata. *)
  let rec processArgs (args: exp list) : (stmt clist) * (cureexp list) =
    match args with
      arg :: rest ->
        let (doa1, arg') = cureExpf arg in
        let (doa2, rest') = processArgs rest in
        append doa1 doa2, arg' :: rest'
    | [] -> empty, []
  in
  let (doa, args') = processArgs args in
  let dataargs = List.map (fun arg -> arg.ep) args' in
  (* Now call the function, storing the data portion of the return
   * value if necessary. *)
  let docall =
    match rlv with
      Some lv ->
        let ftype = typeOf f in
        let rtype =
          match ftype with
            TFun (t, _, _, _) -> fixupType t
          | _ -> E.s (bug "callCompatFunction: expected function type")
        in
        let tmp = makeTempVar !CC.currentFunction rtype in
        let (blv, dolv) = cureLval (var tmp) ForWrite in
        let makeMetaData =
          if emHasMetaPtr blv.lvm then
            let mt =
              match metaDataType blv.lvt with
                Some t -> t
              | None -> E.s (bug "callCompatFunction: expected metadata")
            in
            let mf = makeMetagenFun blv.lvt mt in
            let arg1 = emGetMetaPtr blv.lvm in
            let arg2 = Lval (blv.lv) in
            let arg3 = integer 1 in
            let arg4 = zero in
            [Call (None, Lval (var mf.svar),
                   [arg1; arg2; arg3; arg4], !currentLoc)]
          else
            []
        in
        let doset = cureinstr (Set (lv, Lval (var tmp), !currentLoc)) in
        (append dolv
           (CConsL (mkStmt (Instr (Call (Some blv.lv, f, dataargs, !currentLoc) :: makeMetaData)),
                   doset)))
    | None ->
        single (mkStmtOneInstr (Call (None, f, dataargs, !currentLoc)))
  in
  append doa docall

(*** Returns true if this function is handled by interceptHelper *****)
and shouldInterceptHelper func : bool =
  match func with
      Lval(Var fv, NoOffset) -> begin
	let name, _ = demangle fv.vname in
        let stripped = Poly.stripPoly name in
        ((String.get stripped 0) = '_') (* For performance, only do the *)
        &&                              (* match for names starting with '_' *)
        match stripped with
	    "__ptrof_nocheck"
	  | "__endof"
	  | "__startof"
	  | "__ptrof"
	  | "__mkptr"
	  | "__mkptr_size"
	  | "__CCURED_RTTITAGFOR"
	  | "__CCURED_RTTISTATICTAGFOR"
	  | "__CCURED_RTTIUNIONCHECK"
	  | "__CHECK_HASRTTITYPE"
            -> (* Intercept these during normal operation, but leave them
                  as is when using the all-Wild solver. *)
              not !N.use_wild_solver
	  | "__trusted_cast"
	  | "__trusted_deepcast"
            -> true
	  | "__stringof_ornull" when !N.useStrings -> true
	  | _ -> false
      end
    | _ (* e.g., a function pointer *) -> false

(*** Intercept some function calls *****)
and interceptHelper
    (fv: varinfo)    (*The function info *)
    (reso: lval option)
    (args: exp list) : stmt clist =
  let name, _ = demangle fv.vname in
  let strippedName = Poly.stripPoly name in
  let funcType = fv.vtype in
  let ftret, fArgs, _, _ = splitFunctionType funcType in
  let formals = argsToList fArgs in
  let preserveCasts: bool = match strippedName with
      "__CCURED_RTTITAGFOR" -> false
    | _ -> true  in
  let (doargs: stmt clist), (args' : cureexp list) =
    if preserveCasts then
      let rec doArgs restargs restargst =
        match restargs, restargst with
          [], [] -> empty, []
        | a :: resta, (_, ft, _) :: restt ->
            let (doa, fa') = cureExpf a in
            let (doa', a2) = castTo fa' ft in
            let (doresta, resta') = doArgs resta restt in
            (append doa (append doa' doresta)),
	    a2 :: resta'
	| _ -> E.s (error "Invalid call to %s\n" fv.vname)
      in
      doArgs args formals
    else (* ignore all casts, except the last cast before a string literal,
            which cureexpf needs. *)
      let rec stripMostCasts e = match e with
          CastE(_, (Const (CStr _ | CWStr _))) -> e
        | CastE(_, e') -> stripMostCasts e'
        | _ -> e
      in
      let rec doArgs restargs restargst =
        match restargs, restargst with
          [], [] -> empty, []
        | a :: resta, (_, ft, _) :: restt ->
            let (doa, fa') = cureExpf (stripMostCasts a) in
            let (doresta, resta') = doArgs resta restt in
            (append doa doresta),
	    fa' :: resta'
	| _ -> E.s (error "Invalid call to %s\n" fv.vname)
      in
      doArgs args formals
  in
  let resulttype =
    if isSplitType ftret then
      fixupType ftret
    else
      ftret
  in
  let resultkind = kindOfType resulttype in
  let result = makeTempVar !CC.currentFunction resulttype in
  let assignToResult (value:exp) =
    single (mkStmtOneInstr (Set(var result, value, !currentLoc))) in
  let getOneArg () : cureexp =
    match args' with [ a ] -> a
      | _ -> E.s (bug "Invalid call to %s\n" fv.vname);
  in
  let getTwoArgs () : cureexp * cureexp =
    match args' with [ a; b ] -> a, b
      | _ -> E.s (bug "Invalid call to %s\n" fv.vname);
  in
  let origCall src =
    (* If we want the actual helper call instead of optimizing *)
    let (_, toExp, src') = cureExp2exp src in
    append toExp
      (single (call (Some (var result)) (Lval(var fv)) [src']))
  in
  let doTheWork: stmt clist = (* Statements that do any needed checking
			       * and put the right value in "result" *)
    match strippedName with
	"__ptrof_nocheck" ->
	  let src = getOneArg () in
	    assignToResult src.ep
      | "__endof" -> begin
	  let src = getOneArg () in
	    match src.ek with
		N.Wild | N.WildC | N.WildT ->
		  (* Just kidding!  If src is wild, call the original endof*)
		  origCall src
	      | _ ->
		  assignToResult (emGet MKEnd "__endof" src.em)
	end
      | "__startof" ->
	  let src = getOneArg () in
	    assignToResult (emGet MKBase "__startof" src.em)
      | "__stringof_ornull" ->  begin (* Only when using strings. *)
	  let ptr = getOneArg () in
	  match ptr.ek with
	    N.Wild | N.WildC | N.WildT ->
	      (* If src is wild, call the original func*)
	      origCall ptr
	  | _ ->
              if not (isNullTerm ptr.ek) then
                E.s (bug "__stringof_ornull with non-nullterm pointer kind.");
              (* This is guaranteed to be either a string pointer or NULL. *)
	      assignToResult ptr.ep
        end
      | "__ptrof" -> begin
	  let arg = getOneArg () in
	  (* Now strip the RTTI from the argument.  The argument should have
	   * the right (static) type already, and there's nothing more we can
	   * do with the RTTI info. *)
	  let src: cureexp =
	    if pkHas MKRtti arg.ek then
	      let _, oldType = extractTruePointerType arg.et in
              let k = N.stripRTTI arg.ek in (* The new kind *)
              let t = match unrollType oldType with
		TPtr(bt, _) -> mkPointerTypeKind bt k
              | _ -> E.s (bug "ptrof: stripping RTTI: %a" d_type arg.et)
              in
              { et = t;
		ep = arg.ep;
		ek = k;
		em = {arg.em with _t = None} }
	    else
	      (* already RTTI-free *)
	      arg
	  in
	  let checkBlock =
	    let srcLval, checks1 = addressToLval src NoOffset false in
	    let checks2 = checkMem ToRead srcLval in
	      mkBlock (toList (append checks1 checks2))
	  in
	  let ifStmt = (* do the checks only if the pointer is not null. *)
	    mkStmt(If(src.ep, checkBlock, mkBlock [], !currentLoc))
	  in
	    append (single ifStmt) (assignToResult src.ep)
	end
      | "__mkptr" -> begin
	  let src, home = getTwoArgs () in
          if src.ek <> N.Safe then
	    E.s (bug "mkptr on a non-SAFE pointer")
          else if resultkind == N.Safe then
            (* SAFE->SAFE, nothing to do *)
	    let (_, toExp, newptr) = cureExp2exp src in
                append toExp (assignToResult newptr)
          else begin
            let normalVersion =
	      let newptr = {home with ep = src.ep} in
	      let (_, toExp, newptr') = cureExp2exp newptr in
                append toExp (assignToResult newptr')
            in
              (* If the result value is e.g. FSeq, we need to check whether src
               * is null, and if so use scalar metadata (zero).  For SEQs,
               * however, we can avoid this check:  the lower bound check will
               * catch the null case for us.  So only insert the
               * "if src is null then ... " if there is no lower bound info. *)
              if pkHas MKBase resultkind then
                (* result := src with home's metadata *)
                normalVersion
              else begin
                (* result := (src != 0) ? src with home's metadata
                 *                      : NULL                     *)
                let nullVersion =
                  let newptr = mkCureexp resulttype Cil.zero
                                 (pkMakeScalarMeta resultkind)
                  in
	          let (_, toExp, newptr') = cureExp2exp newptr in
                    append toExp (assignToResult newptr')
                in
                  single (mkStmt(If(src.ep,
                                    mkBlock (toList normalVersion),
                                    mkBlock (toList nullVersion),
                                    !currentLoc)))
              end
          end
	end
      | "__mkptr_size" -> begin
	  let src, size = getTwoArgs () in
          if src.ek <> N.Safe && src.ek <> N.String then
	    E.s (error "mkptr_size on a non-SAFE pointer (kind=%a)"
                   N.d_opointerkind src.ek);
          match resultkind with
              N.Safe ->
                (* SAFE->SAFE, nothing to do.
                 * We ignore the size in this case *)
	        let (_, toExp, newptr) = cureExp2exp src in
                  append toExp (assignToResult newptr)
            | N.Seq | N.SeqN | N.FSeq | N.FSeqN ->
                (* result := (src != 0) ? {.p = src,
                 *                         .b = src,       /* SEQ,SeqN  only */
                 *                         .e = src + size /*byte arithmetic*/}
                 *                      : NULL                               *)
                let normalVersion =
                  let endof = BinOp(PlusA, src.ep, size.ep, !upointType) in
	          let newptr =
                    if pkHas MKBase resultkind then (* Seq, SeqN *)
                      mkCureexp resulttype src.ep (emBaseEnd src.ep endof)
                    else (* FSeq, FSeqN *)
                      mkCureexp resulttype src.ep (emEnd endof)
                  in
	          let (_, toExp, newptr') = cureExp2exp newptr in
                    append toExp (assignToResult newptr')
                in
                let nullVersion =
                  let newptr = mkCureexp resulttype Cil.zero
                                 (pkMakeScalarMeta resultkind)
                  in
	          let (_, toExp, newptr') = cureExp2exp newptr in
                    append toExp (assignToResult newptr')
                in
                  single (mkStmt(If(src.ep,
                                    mkBlock (toList normalVersion),
                                    mkBlock (toList nullVersion),
                                    !currentLoc)))
            | N.Wild ->
	        E.s (error "mkptr_size can not be used to create a WILD pointer.  Copy the data to a new buffer.")
            | k ->
	        E.s (error "mkptr_size can not be used to create a %a pointer."
                       N.d_opointerkind k)
        end
      | "__CCURED_RTTITAGFOR" ->
          (* __CCURED_RTTITAGFOR(e) is introduced by taggedunion.ml and should
             be replaced by the RTTI tag for e *)
	  let src = getOneArg () in
          let thintype = typeOf src.ep in
(*           ignore (E.log "__CCURED_RTTITAGFOR(%a)\n %a\n"  *)
(*                     d_exp (List.hd args) d_cureexp src); *)
          if N.isRTTI src.ek then begin
            (* Get the dynamic tag of the pointer. *)
            let tag = emGet MKRtti "__CCURED_RTTITAGFOR" src.em in
            assignToResult tag
          end else begin
            (* get the tag from the static type of the value. *)
            let rtti = MU.getRttiForType thintype in
            assignToResult rtti
          end
      | "__CCURED_RTTISTATICTAGFOR" ->
          (* __CCURED_RTTISTATICTAGFOR(sizeof e) is introduced by
             taggedunion.ml and should be replaced by the RTTI tag for e *)
          let arg = dropCasts (getOneArg ()).ep in
	  let t = match arg with
              SizeOfE arg' -> typeOf arg'
            | _ -> E.s (bug "bad call to __CCURED_RTTISTATICTAGFOR: %a."
                          d_plainexp arg)
          in
          let rtti = MU.getRttiForType t in
          assignToResult rtti
      | "__CHECK_HASRTTITYPE" ->
          (* The second arg of "__CCURED_RTTISTATICTAGFOR(e, sizeof field)"
             should be replaced by the tag associated with typeOf field, so
             that the call to __CCURED_RTTISTATICTAGFOR will work correctly.
          *)
          let arg1, arg2 = getTwoArgs () in
	  let arg2' = match dropCasts arg2.ep with
              SizeOfE fieldlv -> MU.getRttiForType (typeOf fieldlv)
            | _ -> E.s (bug "bad call to __CHECK_HASRTTITYPE: %a."
                          d_plainexp arg2.ep)
          in
          single (call (Some (var result)) (Lval(var fv)) [arg1.ep; arg2'])
      | "__CCURED_RTTIUNIONCHECK" ->
          (* __CCURED_RTTICHECK(sizeof lv) is introduced by
             taggedunion.ml and should be replaced by a check that the rtti
             for the union matches the expected type of this field.
          *)
          let arg = getOneArg () in
	  let src = match dropCasts arg.ep with
              SizeOfE (Lval lv) ->
                let lv, _ = cureLval lv NoAccess in
                curelval2cureexp lv
            | _ -> E.s (bug "bad call to __CCURED_RTTICHECK: %a."
                          d_plainexp arg.ep)
          in
          (* ignore (E.log "src = %a\n" d_cureexp src); *)
          let _tag = emGet MKRtti "__CCURED_RTTICHECK (tagged unions)" src.em in
          let desttype = typeOf src.ep in
          let dest_rtti = MU.getRttiForType desttype in
          let dest_is_ptr = isPointerType desttype in
          rttiDowncast src.ep src.em dest_rtti dest_is_ptr DC_union
      | "__trusted_cast"
      | "__trusted_deepcast" ->
          (* This is the identity function *)
          let src = getOneArg () in
	  let (_, toExp, src') = cureExp2exp src in
          append toExp (assignToResult src')

      | _ ->
	E.s (bug "bug in interceptHelper")
  in
  let assignResult =
    match reso with
        None ->
	  (* Nothing to do here, since the side-effects (the checks), have
	   * already been taken care of. *)
	  empty
      | Some destlv ->
	  (* As with other calls, put the result in a temporary and then
	   * assign it to destlv, so that we can cure that assignment
	   * separately. *)
          cureinstr (Set(destlv, Lval (var result), !currentLoc))
  in
    append doargs (append doTheWork assignResult)

(* Given an lvalue, generate all the stuff needed to construct a pointer to
 * it. If foraccess is NoAccess then we will not read/write through this one,
 * but will use it for & or for sizeof. *)
and cureLval (b, off) (foraccess: forAccess) : curelval * stmt clist =
  (* Maybe we have heapified this one *)
  match b, off with
    Var vi, off -> begin
      try
        let newb, newoff = H.find heapifiedLocals vi.vname in
        cureLval (newb, addOffset off newoff) foraccess
      with Not_found -> cureLval1 (b, off) foraccess
    end
        (* Intercept the case (T* )0->f *)
  | Mem z, off when foraccess = NoAccess && isZero z ->
      (* Check out the kind of pointer to the field "f" *)
      let k =
        match off with
          Field(f, _) -> fst (N.kindOfAttrlist f.fattr)
        | _ -> N.Safe
      in
      let meta = pkMakeScalarMeta k in
      { lv = (b, off); lvt = typeOfLval (b, off);
        plvk = k; lvm = meta; }, empty

  | _ -> cureLval1 (b, off) foraccess

and cureLval1 (b, off) (foraccess: forAccess) : curelval * stmt clist =
  let debuglval = false in
  (* As we go along the offset we keep track of the basetype and the pointer
   * kind, along with the current base expression and a function that can be
   * used to recreate the lval. *)
  if debuglval then
    ignore (E.log "Curelval: %a\n" d_lval (b, off));
  let (startinput : curelval), (startss: stmt clist) =
    match b with
      Var vi -> varStartInput vi, empty

    | Mem addr ->
        (* Cure the address and put it in cureexp form *)
        if debuglval then
          ignore (E.log "before Mem: addr=%a\n" d_plainexp addr);
        let (doaddr, caddr) = cureExpf addr in
        if debuglval then
          ignore (E.log " after Mem: caddr=%a\n" d_cureexp caddr);
        let caddrlv, convaddr = addressToLval caddr off (foraccess<>NoAccess) in
        if debuglval then
          ignore (E.log " after addressToLval = %a\n" d_curelval caddrlv);
        caddrlv, append doaddr convaddr
  in
  (* As we go along we need to go into tagged and sized types. *)
  let goIntoTypes (inlv: curelval) : curelval * stmt clist =
    if debuglval then
      ignore (E.log "goIntoTypes: %a\n" d_curelval inlv);
    match unrollType inlv.lvt with
      TComp (comp, _) as t when isFatComp comp &&
                                isSplitType
                                  (getTypeOfFat "curelval1" t) -> begin
        let fdata, fmeta = getFieldsOfMerge t in
        let inlv', doinlv' = beforeField inlv (foraccess<>NoAccess) false in
        { lv = addOffsetLval fdata inlv'.lv;
          lvm = emMeta (mkAddrOf (addOffsetLval fmeta inlv'.lv));
          lvt = getTypeOfFat "curelval1" t;
          plvk = N.SafeC; },
        doinlv'
      end

    | TComp (comp, _) when comp.cstruct -> begin
        match comp.cfields with
          f1 :: f2 :: [] when (f1.fname = "_size" && f2.fname = "_array") ->
            begin
              (* A sized array. Make sure we prepare the lvalue as we need
               * before going into a field. This means that the resulting
               * lvalue will be SAFE or WILD. *)
              let inlv', doinlv' =
                beforeField inlv (foraccess<>NoAccess) false in
              if inlv'.plvk != N.Safe then
                E.s (bug "Sized array in a non-safe area: inlv=%a"
                       d_curelval inlv);
              { lv = addOffsetLval (Field(f2,NoOffset)) inlv'.lv;
                lvt = f2.ftype; plvk = N.Safe; lvm = emNone; }, doinlv'
            end
        | f1 :: f2 :: _ when (f1.fname = "_len" && f2.fname = "_data") ->
            (* A tagged data. Only wild pointers inside *)
            if inlv.plvk = N.Wild then
              E.s (bug "Tagged data inside a tagged area");
            let lv' = addOffsetLval (Field(f2,NoOffset)) inlv.lv  in
            { lv = lv';
              lvt = f2.ftype; plvk = N.Wild;
              lvm = emBase (mkAddrOf lv');}, empty

        | _ -> inlv, empty
      end

    | _ -> inlv, empty
  in

  (* Now do the offsets *)
  let startinput2, startss2 = goIntoTypes startinput in
  let rec doOffset (inlv: curelval)
                  ?(inTaggedUnion: lval option) (* If not None, we are in a
                                      tagged union with the given tag field. *)
                   (off: offset) : curelval * stmt clist =
    match off with
      NoOffset -> inlv, empty

    | Field (f, resto) ->
        if debuglval then
          ignore (E.log "doingField(%s): %a\n" f.fname d_curelval inlv);
        let bflv, acc' = beforeField inlv (foraccess<>NoAccess) false in
        let addf = Field (f, NoOffset) in
        (* If we have metadata, we need to get the metadata field
         * corresponding to this field, if it exists. *)
        let lvm =
          if emHasMetaPtr bflv.lvm then
            let deref = mkMem (emGetMetaPtr bflv.lvm) NoOffset in
            match unrollType (typeOfLval deref) with
              TComp (comp, _) ->
                begin
                try
                  emSetMetaPtr bflv.lvm
                    (mkAddrOf
                       (addOffsetLval
                          (Field (getCompField comp f.fname, NoOffset)) deref))
                with Not_found ->
                  emNone
                end
            | TVoid _ ->
                emNone
            | t -> E.s (bug "doOffset: expected composite metadata, got %a"
                            d_type t)
          else
            bflv.lvm
        in
        (* If we stripped away a metadata ptr, adjust the kind *)
        let plvk =
          if emHasMetaPtr lvm then bflv.plvk else N.stripC bflv.plvk
        in
        let lvm' = match inTaggedUnion with
            Some tagValue when foraccess <> ForWrite ->
              (* Reading a tagged field. It should not already be RTTI *)
              if emHas MKRtti lvm || N.isRTTI plvk then
                E.s (bug "RTTI ptr in tagged union.");
              (* Add the RTTI tag to the metadata, so that we'll remember it
                 later.  Note that we didn't change the kind to an RTTI kind,
                 so we'll have to check for this metadata specially. *)
              emSet MKRtti lvm (Lval tagValue)
          | _ -> lvm
        in
        (* Prepare for the rest of the offset *)
        (* maybe f is the __data field of a tagged union.  If so, remember
           the __Tag field when recursing into f. *)
        let maybeInTaggedUnion: lval option
          = Taggedunion.tagForDataField inlv.lv f in
        let next = { lv = addOffsetLval addf bflv.lv;
                     lvt = f.ftype; lvm = lvm'; plvk = plvk; } in
        let next', donext' = goIntoTypes next in
        let res, dorest = doOffset next'
                            ?inTaggedUnion:maybeInTaggedUnion resto in
        res, append acc' (append donext' dorest)

    | Index (e, resto) ->
        if debuglval then
          ignore (E.log "doingIndex(%a): %a\n" d_exp e d_curelval inlv);
        let bilv, acc' = beforeIndex inlv (foraccess<>NoAccess) false in
        (* Do the index *)
        let (_, doe, e') = cureExp e in
        (* Prepare for the rest of the offset. Notice that beforeIndex gives
         * us the first element of the array *)
        let rec loopOff = function
            Index(z, NoOffset) when isZero z -> Index(e', NoOffset)
          | Index(i, off) -> Index(i, loopOff off)
          | Field(f, off) -> Field(f, loopOff off)
          | _ -> E.s (bug "doingIndex: expected an Index(0) offset: %a"
                        d_plainlval bilv.lv)
        in
        (* If we have metadata, we need to get the metadata offset
         * corresponding to this offset. *)
        let meta =
          if emHasMetaPtr bilv.lvm then
            let deref = mkMem (emGetMetaPtr bilv.lvm) NoOffset in
            emSetMetaPtr bilv.lvm (mkAddrOf (fst deref, loopOff (snd deref)))
          else
            bilv.lvm
        in
        let next =
          { bilv with lv = (fst bilv.lv, loopOff (snd bilv.lv));
                      lvm = meta; }
        in
        let next', donext' = goIntoTypes next in
        let res, dorest = doOffset next' resto in
        res, append acc' (append doe (append donext' dorest))
  in
  let lvoffset, acc2 = doOffset startinput2 off in
  if debuglval then begin
    ignore (E.log "Done lval: %a\n" d_curelval lvoffset);
  end;
  lvoffset, append startss (append startss2 acc2)

(* Cure an expression and return the cureexp version of the result. If you
 * do not care about an cureexp, you can call the wrapper cureexp  *)
and cureExpf (e: exp) : stmt clist * cureexp =
  try
    match e with
    | Lval (lv) ->
        (* ignore (E.log "cureexpf: %a\n" d_plainlval lv); *)
        let blv, dolv = cureLval lv ForRead in
        let check = (* Check a read if it is in memory or if it comes from a
                     * variable that contains arrays or that is tagged
                       *)
          match blv.lv with
            Mem _, _ ->
              checkMem ToRead blv
          | Var vi, off when containsArray vi.vtype || mustBeTagged vi ->
              checkMem ToRead blv
          | _, _ -> empty
        in
        if blv.plvk = N.FSeq then
          optimizeFSeqArithChecks blv dolv check;
        (append dolv check, curelval2cureexp blv)

    | Const (CInt64 (_, ik, _)) -> (empty, mkCureexp (TInt(ik, [])) e emNone)
    | Const ((CChr _)) -> (empty, mkCureexp charType e emNone)
    | Const (CReal (_, fk, _)) -> (empty, mkCureexp (TFloat(fk, [])) e emNone)
    | Const (CEnum(_, _, ei)) -> (empty, mkCureexp (TEnum(ei,[])) e emNone)

     (* All strings appear behind a CastE. The pointer node in the CastE
      * tells us how to represent the string *)
    | CastE ((TPtr(TInt(IChar, _), a) as strt), Const(CStr s)) ->
        stringLiteral (fun i -> CChr (String.get s i))
                      (String.length s) strt charType

    | CastE ( (TPtr((tau),(a)) as strt),
              (Const(CWStr s)) ) ->
        stringLiteral (fun i -> CInt64((List.nth s i),ILongLong,None))
          (List.length s) strt tau

    | Const (CStr s) ->
        E.s (bug "String (%s) without a cast!" s)

    | Const ( (CWStr s) as it) ->
        E.s (bug "Wide String (%a) without a cast!" d_const it)

    | CastE (t, e) -> begin
        let t' = if isSplitType t then t else fixupType t in
        let (doe, fe') = cureExpf e in
        let doe1, fe1 = castTo fe' t' in
        append doe doe1, fe1
    end

    | UnOp (uop, e, restyp) ->
        let restyp' = fixupType restyp in
        let (et, doe, e') = cureExp e in
        assert (not (isFatType restyp'));
          (* The result is never a pointer *)
        (doe, mkCureexp restyp' (UnOp(uop, e', restyp')) emNone)

    | BinOp (bop, e1, e2, restyp) -> begin
        let restyp' = fixupType restyp in
        let (doe1, ce1) = cureExpf e1 in
        let (doe2, ce2) = cureExpf e2 in
        match bop, ce1.ek, ce2.ek with
        | (PlusPI|MinusPI|IndexPI), _, N.Scalar ->
            let (res, doarith) = pkArithmetic ce1 bop ce2.ep in
            (append doe1 (append doe2 doarith), res)
        | MinusPP, _, _ -> (* Subtract the _p components *)
            (append doe1 doe2,
             mkCureexp restyp'
               (BinOp(bop, ce1.ep, ce2.ep, restyp'))
               emNone)
        | (LAnd|LOr), _, _ when doe2 <> empty ->
            (* For these operators, it is not guaranteed that we evaluate
             * both. We evaluate the first one always though *)
            let v = makeTempVar !CC.currentFunction intType in
            let v_is_e1 =
              mkBlock [mkStmtOneInstr (Set(var v, ce1.ep, !currentLoc))] in
            let v_is_e2 =
              mkBlock (toList
                         (CConsR(doe2,
                                 mkStmtOneInstr (Set(var v,
                                                     ce2.ep,
                                                     !currentLoc))))) in
            (CConsR(doe1,
                   mkStmt(If(ce1.ep,
                             (if bop = LAnd then v_is_e2 else v_is_e1),
                             (if bop = LAnd then v_is_e1 else v_is_e2),
                             !currentLoc))),
             mkCureexp restyp' (Lval (var v)) emNone)

        | _, N.Scalar, N.Scalar ->
            (append doe1 doe2,
              mkCureexp restyp' (BinOp(bop,ce1.ep,ce2.ep,restyp')) emNone)

        | _, _, _ -> E.s (unimp "cureBinOp: %a@!et1=%a@!et2=%a@!"
                            d_binop bop d_plaintype ce1.et d_plaintype ce2.et)
    end

    | SizeOf (t) ->
        let t' = if isSplitType t then t else fixupType t in
        (empty, mkCureexp !typeOfSizeOf (SizeOf(t')) emNone)

    | SizeOfE (Lval lv) ->
        (* Intercept the case when we do sizeof an lvalue. This way we can
         * avoid trying to check the safety of reads that might be triggered
         * if we view the lvalue as an expression  *)
        (* ignore (E.log "cureexpf: %a\n" d_plainlval lv); *)
        let blv, _ = cureLval lv NoAccess (* say that we won't access *) in
        (* DRop the side effects *)
        (empty, mkCureexp !typeOfSizeOf (SizeOfE(Lval blv.lv)) emNone)

    | SizeOfStr s -> (empty, mkCureexp !typeOfSizeOf e emNone)

    | SizeOfE (e) -> begin
        let (et, doe, e') = cureExp e in
        (* For split types, we only want the size of the actual data part. *)
        let e'' =
          if isFatType et && isSplitType (getTypeOfFat "cureExpf" et) then
            readPtrField e' et
          else
            e'
        in
        (* Drop all side-effects from this SizeOf, including the checking of
         * safety of the expression. *)
        (empty, mkCureexp !typeOfSizeOf (SizeOfE(e'')) emNone)
    end

    | AlignOf (t) ->
        let t' = fixupType t in
        (empty, mkCureexp !typeOfSizeOf (AlignOf(t')) emNone)

    | AlignOfE (Lval lv) ->
        (* Intercept the case when we do sizeof an lvalue. This way we can
         * avoid trying to check the safety of reads that might be triggered
         * if we view the lvalue as an expression  *)
        (* ignore (E.log "cureexpf: %a\n" d_plainlval lv); *)
        let blv, _ = cureLval lv NoAccess in
        (* Drop the side effect *)
        (empty, mkCureexp !typeOfSizeOf (AlignOfE(Lval blv.lv)) emNone)

    | AlignOfE (e) -> begin
        let (et, doe, e') = cureExp e in
        (* Drop all size-effects from this SizeOf *)
        (empty, mkCureexp !typeOfSizeOf  (AlignOfE(e')) emNone)
    end

    (* Coalesce the address of functions *)
    | AddrOf (Var f, NoOffset)
        when f != Poly.getPolyFuncRepresentative f ->
        cureExpf (AddrOf (Var (Poly.getPolyFuncRepresentative f), NoOffset))

    | AddrOf (lv) ->
        let blv, dolv = cureLval lv NoAccess in
        (* Check that variables whose address is taken are flagged as such,
         * or are globals  *)
        (match blv.lv with
          (Var vi, _) when not vi.vaddrof && not vi.vglob ->
            E.s (bug "addrof not set for %s (addrof)" vi.vname)
        | _ -> ());
        let res, doaddrof = pkAddrOf blv in
        (* ignore (E.log "%a -> %a\n" d_exp e d_cureexp res);  *)
        (append dolv doaddrof, res)

          (* StartOf is like an AddrOf except for typing issues. *)
    | StartOf lv -> begin
        let blv, dolv = cureLval lv NoAccess in
        (* Check that variables whose address is taken are flagged *)
        (match blv.lv with
          (Var vi, _) when not vi.vaddrof && not vi.vglob ->
            E.s (bug "addrof not set for %s (startof)" vi.vname)
        | _ -> ());
        let res, dostartof = pkStartOf blv in
        (append dolv dostartof, res)
    end

  with exc -> begin
    ignore (E.log "cureexpf error (%s): %a in %s\n"
              (Printexc.to_string exc) d_exp e !CC.currentFunction.svar.vname);
    (empty,
     mkCureexp charPtrType (dExp (dprintf "ccurederror_exp: %a" d_exp e)) emNone)
  end


(** Process an initializer for a global variable  **)
and cureinit (v: varinfo) (eio: init option) : init option * stmt clist =
  (* Keep here a list of the offsets for WILD _b fields written, in words *)
  let bComponents : int list ref = ref [] in
  (* Now a function that makes tag words from the bComponents *)
  let getTagInits () : (offset * init) list =
    (* Find out the maximum word *)
    let maxWord =
      List.fold_left (fun sofar one -> max sofar one) (-1) !bComponents in
    if maxWord = -1 then
      []
    else begin
      (* Allocate an array of int64. We'll always use only the low 32 bits
       * though  *)
      let tagArray = Array.make ((maxWord + 1 + 31) lsr 5) (Int64.of_int 0) in
      (* Now go through the offsets again and set the tag bits *)
      List.iter (fun wrd ->
        let tagwrd = wrd lsr 5 in
        tagArray.(tagwrd) <-
           Int64.logor  tagArray.(tagwrd)
             (Int64.shift_left Int64.one (wrd land 31)))
        !bComponents;
      let tagList : (offset * init) list ref = ref [] in
      Array.iteri
        (fun i tagWrd ->
          tagList :=
             (Index(integer i, NoOffset),
              SingleInit (kinteger64 IUInt tagWrd)) :: !tagList)
        tagArray;
      List.rev !tagList
    end;
  in

  (* Collect here the statements *)
  let iStmts: stmt clist ref = ref empty in

  (* Create an initializer *)
  let rec doOne (baseoff: offset) (what: init) : init * init option =
    let t = typeOfLval (Var v, baseoff) in
    match what, unrollType t with
      (* Single initializer for a scalar type *)
      SingleInit e,
      (TInt _ | TFloat _ | TEnum _ | TPtr _ | TBuiltin_va_list _) ->
        let (doe, ci) = cureExpf e in (* Drop the statements *)
        let (docast, ci') = castTo ci t in
        iStmts := append !iStmts (append doe docast);
        let minito =
          (* If there's metadata, which can only happen in the pointer case,
           * produce the appropriate initializer for a metadata comp. *)
          if isSplitType t && pkHasMeta (kindOfType t) then
            let mt =
              match metaDataType t with
                Some t -> t
              | None -> E.s (bug "Expected metadata type")
            in
            let metaFields = getFieldsOfMeta mt in
            let minifields =
              List.map
                (fun (mk, o) ->
                  let data = emGet mk "doOne" ci'.em in
                  (o, SingleInit data))
                metaFields
(*
            let fbaseo, fendo, fmetao = getFieldsOfMeta mt in
            let b, e, m = breakEM ci'.em in
            let minifields =
              match fbaseo, fendo, fmetao with
              | None, None, Some fmeta ->
                  [ (fmeta, SingleInit m) ]
              | None, Some fend, None ->
                  [ (fend, SingleInit e) ]
              | None, Some fend, Some fmeta ->
                  [ (fend, SingleInit e);
                    (fmeta, SingleInit m) ]
              | Some fbase, Some fend, None ->
                  [ (fbase, SingleInit b);
                    (fend, SingleInit e) ]
              | Some fbase, Some fend, Some fmeta ->
                  [ (fbase, SingleInit b);
                    (fend, SingleInit e);
                    (fmeta, SingleInit m) ]
              | _ -> E.s (bug "Unexpected combination of initializers (%a)"
                              N.d_opointerkind ci'.ek)
*)
            in
            Some (CompoundInit (mt, minifields))
          else
            None
        in
        SingleInit ci'.ep, minito

      (* Single or compound initializer for a fat comp containing a
       * split type (this is the boundary between split and nosplit).
       * Could be a pointer, an array, or a comp. *)
    | _,
      (TComp (ci, _) as t) when isFatComp ci &&
                                isSplitType
                                  (getTypeOfFat "cureinit" t) -> begin
        (* Process the data field, which should yield data and metadata
         * initializers; then package these together to init the merge. *)
        let fdata, fmeta = getFieldsOfMerge t in
        let init, minit = doOne (addOffset fdata baseoff) what in
        let inifields =
          match minit with
            Some minit' -> [ (fdata, init); (fmeta, minit') ]
          | None -> E.s (bug "Metadata initializers expected")
        in
        CompoundInit (t, inifields), None
      end

      (* Single initializer for a pointer type that has become fat *)
    | SingleInit e,
      TComp (comp, _) when isFatComp comp -> begin
        let (doe, ci) = cureExpf e in (* Drop the statements *)
        let (docast, ci') = castTo ci t in
        iStmts := append !iStmts (append doe docast);
        let inifields =
          (* See if we are initializing a WILD pointer *)
          (match ci'.ek with
            N.Wild ->
              (* We are initializing a WILD pointer. Keep track of the
               * offsets where we wrote the _b components *)
              let fbaseo = getOneFieldOfFat "cureinit" MKBase t in
              let boff, bwidth = bitsOffset v.vtype
                                            (addOffset fbaseo baseoff) in
              if boff land 31 <> 0 || bwidth <> 32 then
                E.s (bug "Invalid offset (%d) and width (%d) for WILD pointer init" boff bwidth);
              (* Subtract one to adjust for the length word *)
              bComponents := ((boff lsr 5) - 1) :: !bComponents
          | _ -> ());
          let makeInitFields : (mkind * offset) list -> (offset * init) list =
            List.map
              (fun (mk, o) ->
                 let data = emGet mk "cureinit" ci'.em in
                 (o, SingleInit data))
          in
          if isFatComp comp then
            let fptr, fmerge = getFieldsOfMerge t in
            let metat =
              match fmerge with
                Field (f, NoOffset) -> f.ftype
              | _ -> E.s (bug "cureinit: Expected single field")
            in
            let metafields = getFieldsOfMeta metat in
            let minifields = makeInitFields metafields in
            [ (fptr, SingleInit ci'.ep);
              (fmerge, CompoundInit (metat, minifields)) ]
          else
            let fptr, metafields = getFieldsOfFat "cureinit" t in
            (fptr, SingleInit ci'.ep) :: (makeInitFields metafields)
        in
(*
          match ci'.ek, ci'.em, fbaseo, fendo with
          | (N.FSeq | N.FSeqN), { _e = Some e},
            _, Some fend ->
              [ (fptr, SingleInit ci'.ep);
                (fend, SingleInit e)]
          | (N.Seq  | N.SeqN), {_b = Some b; _e = Some e},
              Some fbase, Some fend ->
              [ (fptr, SingleInit ci'.ep);
                (fbase, SingleInit b);
                (fend, SingleInit e)]
          | N.Index, { _b = Some b}, Some fbase, _ ->
              [ (fptr, SingleInit ci'.ep);
                (fbase, SingleInit b)]
          | N.Rtti, {_t = Some t}, Some ftype, _ ->
              [ (fptr, SingleInit ci'.ep);
                (ftype, SingleInit t)]

          | N.Wild, { _b = Some b}, Some fbase, _ ->
              [ (fptr, SingleInit ci'.ep);
                (fbase, SingleInit b)]
          | _ -> E.s (bug "Unexpected combination of initializers (%a)"
                          N.d_opointerkind ci'.ek)
*)
        CompoundInit (t, inifields), None
      end

    (* Compound initializer for a structure *)
    | CompoundInit (_, il),
      TComp (ci, _) -> begin
        (* Check if this is a sized array *)
        match ci.cfields with
          [s; a] when s.fname = "_size" && a.fname = "_array" ->
            (* The initializer for the array *)
            let ainit, minit =
              doOne (addOffset (Field(a, NoOffset)) baseoff) what in
            if minit <> None then
              ignore (warn "A metadata initializer is being ignored.\n");
            (* Do not initialize the size of the array. We do that in the
             * GLOBINIT *)
            CompoundInit (t, [ (Field(s, NoOffset),
                                SingleInit (kinteger IUInt 0));
                               (Field(a, NoOffset), ainit) ]),
            None

        | _ -> begin (* Now a regular structure or union *)
            (* We iterate over each field in the original initializer,
             * building a list of data initializers and a list of metadata
             * initializers. *)
            let il' =
              List.fold_left
                (fun (acc, macc) (off, i) ->
                  let init, minito = doOne (addOffset off baseoff) i in
                  let acc' = (off, init) :: acc in
                  let macc' =
                    match minito with
                      Some minit ->
                        let mci =
                          match metaDataType t with
                            Some (TComp (mci, _)) -> mci
                          | _ -> E.s (bug "Expected comp metadata type")
                        in
                        let field =
                          match off with
                            Field (field, NoOffset) -> field
                          | _ -> E.s (bug "Expected single field")
                        in
                        (Field (getCompField mci field.fname, NoOffset),
                         minit) :: macc
                    | None -> macc
                  in
                  acc', macc')
                ([], [])
                il
            in
            (* Finalize the metadata initializer, if any. *)
            let minito =
              match snd il' with
                [] -> None
              | l -> begin
                  match metaDataType t with
                    Some (TComp _ as mt) ->
                      Some (CompoundInit (mt, List.rev l))
                  | _ -> E.s (bug "Expected array metadata type")
                end
            in
            CompoundInit (t, List.rev (fst il')), minito
        end
    end

    (* Compund initializer for an array *)
    | CompoundInit (_, il),
      TArray (_, leno, _) ->
        (* We iterate over each offset in the original initializer,
         * building a list of data initializers and a list of metadata
         * initializers. *)
        let il' =
          List.fold_left
            (fun (acc, macc) (off, i) ->
              let init, minit = doOne (addOffset off baseoff) i in
              let acc' = (off, init) :: acc in
              let macc' =
                match minit with
                  Some minit' -> (off, minit') :: macc
                | None -> macc
              in
              acc', macc')
            ([], [])
            il
        in
        if isNullTerm (extractPointerTypeAttribute v.vattr) then begin
          (* The last value in the array must be '0' *)
          let last =
            match leno with
              None -> E.s (bug "array initializer for unsized array.")
            | Some lene ->
                let last' = nulltermArrayEndIndex lene in
                constFold true last'
          in
          ignore (E.log "Checking that %s[%a] is null.\n" v.vname d_exp last);
          let last_offset = Index(last, NoOffset) in
          try
            let last_init = List.assoc last_offset (fst il') in
            (* See if this initializer is all 0 *)
            let rec isAllZeroInit (i: init) : unit =
              match i with
                SingleInit e ->
                  if not (isZero e) then
                    E.s (error "array \"%s\" is supposed to be null-terminated, but the last element is initialized to %a.\n" v.vname d_init last_init)

              | CompoundInit (t, ol) ->
                  List.iter (fun (o, i) -> isAllZeroInit i) ol
            in
            isAllZeroInit last_init;
          with Not_found ->
            (* The initializer list is too short.  This is fine; the rest
               are padded with 0. *)
            ()
        end;
        (* Finalize the metadata initializer, if any. *)
        let minito =
          match snd il' with
            [] -> None
          | l -> begin
              match metaDataType t with
                Some (TArray _ as mt) ->
                  Some (CompoundInit (mt, List.rev l))
              | _ -> E.s (bug "Expected array metadata type")
            end
        in
        CompoundInit (t, List.rev (fst il')), minito

   | _ -> E.s (bug "cureinit: invalid type for initializer\n lv=%a,@? lvt=%a\n"
                 d_plainlval (Var v, baseoff)
                 d_plaintype t)
  in
  (* Process an initializer *)
  try
    (* See if it must be tagged or not *)
    if mustBeTagged v then begin
      let dfld, lfld, tfld, words, _ = splitTagType v.vtype in
      (* Get the data initializer *)
      bComponents := [];
      (* Must register the area *)
      extraGlobInit :=
         registerArea
           [ integer CC.registerAreaTaggedInt;
             castVoidStar (mkAddrOf (Var v, Field(dfld, NoOffset)));
             castVoidStar zero ]
           !extraGlobInit;
      let d_t_init =
        match eio with
          None -> [] (* No data, we also let the tags be 0 *)
        | Some ei ->
            let ei', mi' = doOne (Field(dfld, NoOffset)) ei in
            if mi' <> None then
              ignore (warn "A metadata initializer is being ignored.\n");
            (* Now do the tags *)
(*            ignore (E.log "Tags for %s are: %a\n"
                      v.vname
                      (docList num) (List.rev !bComponents)); *)
            match getTagInits () with
              [] -> (* No tag bits set, leave them alone *)
                [(Field(dfld, NoOffset), ei')]
            | tagInits ->
                [ (Field(dfld, NoOffset), ei');
                  (Field(tfld, NoOffset), CompoundInit(tfld.ftype,
                                                       tagInits)) ]
      in
      Some (CompoundInit(v.vtype,
                         (Field(lfld, NoOffset), SingleInit words)
                         :: d_t_init)),
      !iStmts

    end else begin
      (* No tagging *)
      match eio with
        None -> (* Maybe it contains SIZED arrays and should therefore have
                 * an initializer *)
          None, empty
      | Some ei ->
          let ei', mi' = doOne NoOffset ei in
          if mi' <> None then
            ignore (warn "A metadata initializer is being ignored.\n");
          Some ei', !iStmts
    end
  with exc -> begin
    let d_ei =
      match eio with
        None -> text "None"
      | Some ei -> dprintf "Some(@[%a@])" d_init ei
    in
    ignore (E.log "cureinit error (%s): %a in %s\n"
              (Printexc.to_string exc) insert d_ei
              !CC.currentFunction.svar.vname);
    Some (SingleInit (dExp (dprintf "booo_init: %a" insert d_ei))),
    !iStmts
  end

(* Cure an expression and resolve the cureexp into statements *)
and cureExp (e : exp) : expRes =
  let (doe, fe) = cureExpf e in
  let (t', doe', e') = cureExp2exp fe in
  (t', append doe doe', e')

(* sm: find which fields are referenced *)
class computeUsedFields (used: (fieldinfo, bool) H.t) = object (self)
  inherit nopCilVisitor

  (* the whole reason I added 'vinitoffs' is because I do *not*
   * want to visit initializer offsets here; I don't care if a field
   * is initialized (CIL often fills in initializers for all fields
   * even if those initializers weren't present in the original code)
   * as long as it isn't subsequently *used* *)
  method voffs (o:offset) : offset visitAction =
    match o with
    | Field(fi,_) -> (
        (trace "expand" (dprintf "field %s is used\n" fi.fname));
        (H.add used fi true);
        DoChildren
      )
    | _ -> DoChildren
end

(* sm: make a pass over the file and change declared types of arrays *)
(* of chars to be 1 byte longer *)
class expandCharArrays (used: (fieldinfo, bool) H.t) = object (self)
  inherit nopCilVisitor

  (* keep track of which globals have been expanded *)
  val expandedGlobals: (string, bool) H.t = (H.create 117)

  (* given a type, if it's a char array, return a similar array type *)
  (* that is 1 byte bigger; 'fname/loc' is passed for debugging help; *)
  (* 'unrefd' is true if the entity is not referenced *)
  method replaceType (fname:string) (loc:location) (t:typ) (unrefd:bool): typ =
    match t with
    | TArray(baseType, Some length, attrs) when (isCharType(baseType)) -> (
        if (not unrefd) then (
          (trace "expand" (dprintf "expanding array variable/field %s at %a\n"
                                   fname d_loc loc));
          TArray(baseType, Some(BinOp(PlusA, length, one, intType)), attrs)
        )
        else (
          (trace "expand" (dprintf "not expanding %s at %a b/c is unreferenced\n"
                                   fname d_loc loc));
          t     (* unchanged *)
        )
      )
    | _ -> t    (* leave unchanged *)

  (* this gets the types of locals and globals *)
  method vvdec (v:varinfo) = (
    if (v.vglob) then (
      (* sm: bugfix 7/07/02: for globals, only do this once; apparently, it's
       * ok to have static globals defined multiple times (since 'extern'
       * would not make sense, but forward declarations are necessary); the
       * testcase for this is small2/arrayexpand.c *)
      if (not (H.mem expandedGlobals v.vname)) then (
        v.vtype <- (self#replaceType v.vname v.vdecl v.vtype false);
        (H.add expandedGlobals v.vname true)
      )
    )
    else
      (* locals and formals *)
      (* NOTE: according to the visitor docs, formals get hit twice here;
       * luckily, we almost never see arrays as formals... *)
      v.vtype <- (self#replaceType v.vname v.vdecl v.vtype false);

    DoChildren
  )

  method vexpr (e:exp) = (
    match e with
    | Const(CStr s) when false ->
        (* tack one more null byte onto the end *)
        ChangeTo(Const(CStr (s ^ "\000")))

    | SizeOfE(innerExp) -> (
        match (typeOf innerExp) with
        | TArray(baseType, len, attrs) when (isCharType baseType) ->
            (* all arrays of chars get expanded by 1 char, but I want *)
            (* the program to still see the unexpanded size, so make this *)
            (* yield a value one less *)
            (trace "expand" (dprintf "subtracting 1 from %a\n" d_exp e));
            ChangeTo(BinOp(MinusA, e, one, intType))
        | _ ->
            (* leave other sizeofs alone *)
            DoChildren
      )
    | _ -> DoChildren
  )

  (* this gets the types of fields in structures *)
  method vglob (g:global) : global list visitAction = (
    match g with
    | GCompTag(cinfo, loc) -> (
        let vfield (f:fieldinfo) : unit = (
          (* sm: don't expand fields that aren't referenced; this handles *)
          (* fields used specifically for padding; note we look at the *)
          (* attributes of the field's *type*; as far as I can tell, *)
          (* the fields own attributes are never used *)

          (* update: unfortunately, the pkReferenced flag doesn't seem
           * to get set *ever*, regardless of whether the array is
           * used or not; so I switched to my own pre-pass analysis *)
          let unrefd:bool =
            (not (H.mem used f))
          in
          f.ftype <- (self#replaceType f.fname loc f.ftype unrefd)

        ) in
        (List.iter vfield cinfo.cfields);
        DoChildren
      )
    | _ -> DoChildren
  )
end

let doExpandCharArrays (f: file) : unit = (
  (tracei "sm" (dprintf "array-expand post-process..\n"));
  let used : (fieldinfo, bool) H.t = (H.create 111) in
  (ignore (visitCilFile (new computeUsedFields used :> cilVisitor) f));
  (ignore (visitCilFile (new expandCharArrays used :> cilVisitor) f));
  (traceu "sm" (dprintf "array-expand post-process finished\n"))
)

(**** WILD functions ****)
(* make a pass over the file and transform all functions whose pointer is
   tagged

             T0 f(T1 x1, ..., Tn xn) {
                  r = x1 + x2;
                  return r;
             }

    to

             void f(void * __WILD pargs) {
                struct { T0 res; T1 x1; ...; Tn xn } pargs' = pargs;
                r = pargs'->x1 + pargs'->x2;
                pargs'->res = r;
                return;
             }
****)

(* Keep here the original function types *)
let originalFunctionTypes:
    (string, typ * (string * typ * attributes) list option * bool) H.t
    = H.create 17
let collectOriginalFunctionTypes (file: file) =
  H.clear originalFunctionTypes;
  let rec collectOneGlobal = function
      GVarDecl(v, _) -> collectOneFunctionType v
    | GFun(fdec, _) -> collectOneFunctionType fdec.svar
    | _ -> ()
  and collectOneFunctionType (f: varinfo) =
    match f.vtype with
      TFun(rt, args, isva, _) ->
        H.replace originalFunctionTypes f.vname (rt, args, isva)
    | _ -> ()
  in
  iterGlobals file collectOneGlobal

(** Sometimes the code passes integers instead of pointers and vice-versa.
 * Thus we promote all argument of 32-bit to void-ptr __WILD. *)
let mustPromoteType (t: typ) =
  match unrollType t with
    TComp _ -> false (* Do not promote structure types *)
  | _ -> (try bitsSizeOf t <= 32 with SizeOfError _ -> true)

(** Make the structure that contains the arguments and the result *)
let allWildArgumentStructures: compinfo list ref = ref []
let argStructId = ref 0
let makeWildFunctionArgumentStructure
    (rt: typ)
    (args: (string * typ * attributes) list option)
    (isva: bool)
    : compinfo * fieldinfo * fieldinfo list * fieldinfo option =
  let argFields =
    let fieldName = ref 0 in
    List.map
      (fun (n, t, a) ->
        let n' =
          if n = "" then (incr fieldName;
                          "fld" ^ (string_of_int !fieldName)) else n
        in
        (* Promote integers to void-ptr to ensure that an int and a pointer
         * have the same width *)
        let t' =
          if mustPromoteType t then
            TPtr(TVoid [], [Attr("wild", [])])
          else
            t
        in
        (n', t', None, a, !currentLoc)) (argsToList args) in
  (* We'll have an integer result anyway *)
  let retField =
    if mustPromoteType rt then
      ("__res", TPtr(TVoid [], [Attr("wild", [])]), None, [], !currentLoc)
    else
      ("__res", rt, None, [], !currentLoc)
  in
  (* Add a field at the end for the ... *)
  let argFields =
    if isva then
      argFields @ [("__dot_dot_dot", intType, None, [], !currentLoc)]
    else
      argFields
  in
  incr argStructId;
  let ci = mkCompInfo true ("__argumentStructure" ^
                            (string_of_int !argStructId))
      (fun _ -> retField :: argFields) [] in
  allWildArgumentStructures := ci :: !allWildArgumentStructures;
  let resFld, argFlds =
    match ci.cfields with
      resFld :: argFlds -> resFld, argFlds
    | _ -> E.s (E.bug "processWildFunctions:vfunc bad ci")
  in
  if isva then begin
    let dotFld, argFlds =
      match List.rev argFlds with
        [] ->
          E.s (E.bug "makeWildFunctionArgumentStructure: not enough fields")
      | dotfld :: rest -> dotfld, List.rev rest
    in
    ci, resFld, argFlds, Some dotFld
  end else
    ci, resFld, argFlds, None


class processWildFunctionsClass  = object (self)
  inherit nopCilVisitor

  (* Fix a function type *)
  method private fixWildFunctionType (t: typ) : typ =
    match unrollType t with
      TFun(rt, args, isva, attrs) ->
        TFun(voidType, Some [("", (TPtr(TVoid [], [Attr("wild", [])])), [])],
             isva, attrs)
    | _ -> t

  method vtype (t: typ) : typ visitAction =
    match t with

    | TPtr(bt, a) ->
        (* See if this is a WILD pointer *)
        if isWildOrTaggedAttribute a then begin
          match unrollType bt with
            TFun _ -> ChangeTo (TPtr(self#fixWildFunctionType bt, a))
          | _ -> DoChildren

        end else
          DoChildren

    | _ -> DoChildren

  (* Keep here the pointer to the arguments, the return value field, the
   * argument fields, and the optional field for the ... in a vararg function
   *)
  val thePArgs: (exp * fieldinfo
                 * fieldinfo list * fieldinfo option) option ref = ref None
  method private mustChangeReturn () =
    match !thePArgs with
      None -> None
    | Some (x, retField, _, _) ->
        Some (Mem x, Field(retField, NoOffset))

  (* Change the start of a function body *)
  val currentFuncDec = ref dummyFunDec

  method vfunc (fdec: fundec) =
    (* Nothing to do if this is not tagged *)
    currentFuncDec := fdec;
    if not (isWildOrTaggedAttribute fdec.svar.vattr) then begin
      thePArgs := None;
      DoChildren
    end else begin
      (* Fix the type. it might have been fixed already as part of the
       * prototype but we want to be sure  *)
      fdec.svar.vtype <- self#fixWildFunctionType fdec.svar.vtype;
      (* Create the new formal *)
      let formal = makeLocalVar fdec ~insert:false
                      "__thePArgs" (TPtr(TVoid [], [Attr("wild", [])])) in
      (* Get its original type *)
      let rt, args, isva =
        try H.find originalFunctionTypes fdec.svar.vname
        with Not_found -> E.s (bug "processWildFunctions:vfunc no type")
      in
      (* Now create the structure for the result and the arguments *)
      let ci, resFld, argFlds, dotFld =
        makeWildFunctionArgumentStructure rt args isva in
      (* Create a new local variable of the new type *)
      let pArgs = makeLocalVar fdec "__pArgs" (TPtr(TComp(ci, []),
                                                    [Attr("wild", [])])) in
      (* Now initialize the pArgs *)
      let initPArgs : instr list =
        [Set(var pArgs, CastE(pArgs.vtype, Lval (var formal)), !currentLoc)]
      in
      (* Assign the old formals *)
      let initFormals : instr list =
        List.map2
          (fun form argFld ->
            Set(var form,
                CastE (form.vtype,
                       (Lval (Mem (Lval (var pArgs)),
                              Field (argFld, NoOffset)))),
                !currentLoc))
          fdec.sformals
          argFlds
      in
      (* Move the formals to locals *)
      fdec.slocals <- fdec.sformals @ fdec.slocals;
      (* Set the new formal (and ensure that it is shared with the type) *)
      setFormals fdec [formal];
      fdec.sbody.bstmts <-
         mkStmt (Instr (initPArgs @ initFormals)) :: fdec.sbody.bstmts;
      (* Remember the pArgs *)
      thePArgs := Some (Lval(var pArgs), resFld, argFlds, dotFld);
      (* Now do the whole function *)
      DoChildren
    end

  (* We also need to handle the prototypes *)
  method vglob (g: global) =
    match g with
      GVarDecl (vi, l) when isWildOrTaggedAttribute vi.vattr ->
        vi.vtype <- self#fixWildFunctionType vi.vtype;
        DoChildren

    | _ -> DoChildren

  (* Change the return statements *)
  method vstmt (s: stmt) =
    match s.skind with
      Return (Some e, l) -> begin
        (* Replace this with a set instruction *)
        match self#mustChangeReturn () with
          None -> DoChildren
        | Some pReturn ->
            let e' = visitCilExpr (self :> cilVisitor) e in
            s.skind <-
               Block (mkBlock [ mkStmtOneInstr (Set(pReturn, e', l));
                                mkStmt (Return (None, l)) ]);
            (* Ok to continue because we have created a Return None *)
            DoChildren
      end
    | _ -> DoChildren

  (* And change calls as well *)
  method vinst (i: instr) =
    let postInstr = function
        (* intercept calls to ccured_va_start in tagged vararg functions. *)
      | Call(None, Lval(Var va_start, NoOffset),
             [ marker; Lval nextAddrLval ], l)
          when va_start.vname = "__ccured_va_start" &&
               isWildOrTaggedAttribute !currentFuncDec.svar.vattr ->
          (* We must recompute the pointer to the last argument. We point
           * right after the last argument field. *)
           let dotAddr =
             match !thePArgs with
               Some (pArgs, _, _, Some dotFld) ->
                 CastE(TPtr(TVoid [], [Attr("wild", [])]),
                       AddrOf(Mem pArgs, Field(dotFld, NoOffset)))
             | _ -> E.s (E.bug "processWildFunctions: vinst bad thePArgs")
           in
          let setLast = Set(nextAddrLval, dotAddr, l) in
          [setLast; i]

        (* Intercept calls to ccured_va_arg in tagged vararg functions. If we
           are fetcing an integer (or anything of size <= 32) then fetch 64
           bits instead *)
      | Call(res_lval, Lval(Var va_arg, NoOffset),
             [ marker; SizeOf(szt); index ], l)
          when Poly.stripPoly va_arg.vname = "__ccured_va_arg" &&
               isWildOrTaggedAttribute !currentFuncDec.svar.vattr ->
          if (try bitsSizeOf szt <= 32 with SizeOfError _ -> true)  then
            [Call(res_lval, Lval(Var va_arg, NoOffset),
                  [ marker; SizeOf(TPtr(TVoid [], [Attr("wild", [])])); index],
                  l)]
          else
            [i]

      | Call(reto, f, args, l) as i ->
          (* See if this is a tagged function: it is a WILD function pointer
           * or it is called with different number of arguments than what the
           * prototype specifies *)
          let isTaggedCall =
            match f with
              Lval(Mem ptr, _) -> begin
                match typeOf ptr with
                  TPtr(_, a) -> isWildOrTaggedAttribute a
                | t -> E.s (E.bug "processWildFunctions:vinstr isTaggedCall: %a at %a."
			   d_type t d_loc !currentLoc)
              end

            | Lval(Var vi, NoOffset) -> isWildOrTaggedAttribute vi.vattr

            | _ -> E.s (E.bug "processWildFunctions:vinstr isTaggedCall no Lval")
          in
          if not isTaggedCall then
            [i]
          else begin
            (* ignore (E.log "Processing call to tagged %a\n" d_exp f); *)
            (* Make the argument structure based on the actual types of
             * returns and actual arguments *)
            let rt =
              match reto with
                None -> voidType
              | Some ret -> typeOfLval ret
            in
            let actualTypes =
              List.map
                (fun a ->
                  let at = typeOf a in
                  (* If the type is a pointer, then make it WILD. If the a is
                   * AddrOf then the TPtr will have empty attributes *)
                  let at' =
                    match at with
                      TPtr(bt, a) ->
                        TPtr(bt, addAttribute (Attr("wild", [])) a)
                    | _ -> at
                  in
                  ("", at', [])) args
            in
            let ci, retFld, argFlds, _ =
              makeWildFunctionArgumentStructure rt (Some actualTypes) false in
            (* Make a local with that type *)
            let argStruct =
              makeTempVar !currentFuncDec ~name:"__theActualArgs"
                (TComp(ci, [])) in
            argStruct.vattr <- [Attr("wild", []); Attr("tagged", [])];
            (* Set its vaddrof just in case its address is taken *)
            argStruct.vaddrof <- true;
            (* Now initialize the fields *)
            let init : instr list =
              List.map2
                (fun arg afld ->
                  Set((Var argStruct, Field(afld, NoOffset)),
                      arg, !currentLoc))
                args
                argFlds
            in
            (* See if we need to do anything about the return *)
            let initRet =
              match reto with
                None -> []
              | Some retlv ->
                  [ Set(retlv,
                        Lval (Var argStruct, Field(retFld, NoOffset)),
                        !currentLoc) ]
            in
            init @ (Call(None, f,
                         [CastE(TPtr(TVoid [], [Attr("wild", [])]),
                                AddrOf(var argStruct))],
                         !currentLoc) :: initRet)
          end
      | i -> [i]
    in
    ChangeDoChildrenPost([i],
                         mapNoCopyList postInstr)

end

let prepareWildFunctions (file: file) =
  collectOriginalFunctionTypes file;
  argStructId := 0;
  let processWildObj = new processWildFunctionsClass in
  let theFile = ref [] in
  List.iter
    (fun g ->
      allWildArgumentStructures := [];
      ignore (visitCilGlobal (processWildObj :> cilVisitor) g);
      (* Prepend the new compinfos *)
      List.iter
       (fun ci ->
         theFile := GCompTag(ci, locUnknown) :: !theFile)
        !allWildArgumentStructures;
      (* Add back this global *)
      theFile := g :: !theFile)
    file.globals;
  file.globals <- List.rev !theFile



(* a hashtable of functions that we have already made wrappers for *)
let wrappedFunctions = H.create 15

exception DeepExit

let cureFile file =
  if !E.verboseFlag then
    ignore (E.log "Curing file\n");
  E.hadErrors := false;
  H.clear definedFunctionIds;
  functionDescriptorInit := [];
  H.clear allocFunctions;
  (* Initialize the mangled names *)
  H.clear mangledNames;
  (* Pretend that some things are already mangled, to prevent re-mangling.
   * This is also useful to avoid deep mangling and the call to isImported *)
  List.iter (fun n -> H.add mangledNames n (n, ""))
    [ "__ccured_va_count"; "__ccured_va_tags"; ];

  (* Go over all globals once to process some pragmas and collect the defined
   * functions *)
  List.iter
    (function
        GFun (fdec, _) ->
          H.add definedFunctionIds fdec.svar.vid true
      | GPragma (a, l) -> begin
          currentLoc := l;
          match a with
            Attr("ccuredalloc",  AStr(s) :: rest) ->
              if not (H.mem allocFunctions s) then begin
                if !E.verboseFlag then
                  ignore (E.log "Will treat %s as an allocation function\n" s);
                ccuredallocPragma s rest
              end
          | _ -> ()
      end
      | _ -> ()
     )
    file.globals;

  CC.currentFile := file;
  printDeepManglingWarnings file;
  let curing = ref true in
  (* Compute a small file ID *)
  let _ =
    let h = H.hash file.fileName in
    let h16 = (h lxor (h lsr 16)) land 0xFFFF in
    CC.currentFileId := h16;
    if !E.verboseFlag then
      ignore (E.log "File %s has id 0x%04x\n" file.fileName h16)
  in
  let rec doGlobal g =
    try match g with
      (* We ought to look at pragmas to see if they talk about alignment of
       * structure fields  *)
      GPragma ((Attr(an, _) as a), l)-> begin
        (match a with
          Attr("ccuredLogNonPointers", [ ACons("on", _) ]) ->
            MU.logNonPointers := true
        | Attr("ccuredLogNonPointers", [ ACons("off", _) ]) ->
            MU.logNonPointers := false
        | Attr("ccured", [ACons("on", _)]) -> curing := true
        | Attr("ccured", [ACons("off", _)]) -> curing := false
        | _ -> ());
        theFile := consGlobal g !theFile
      end
    | _ -> begin
        if not !curing then theFile := consGlobal g !theFile else
        match g with

        | GVarDecl (vi, l) -> begin
            let g' = cureglobal vi true None l in
            (* See if we should coalesce this one *)
            let vi' = Poly.getPolyFuncRepresentative vi in
            if vi' == vi then (* Keep it if this is a representative *)
              theFile := consGlobal g' !theFile
        end


        | GVar (vi, init, l) ->
            let g' = cureglobal vi false init.init l in
            (* We keep this one always *)
            theFile := consGlobal g' !theFile

        | GCompTagDecl (comp, l) -> begin
            currentLoc := l;
            let tcomp = TComp (comp, []) in
            if isSplitType tcomp then begin
              match metaDataType tcomp with
                Some (TComp (metacomp, _)) ->
                  theFile := (GCompTagDecl (metacomp, l)) :: !theFile
              | _ -> ()
            end;
            (* See if we must coalesce this one *)
            let comp' = Poly.getPolyCompRepresentative comp in
            if comp' == comp then
              theFile := consGlobal g !theFile;
        end

        | GEnumTagDecl _ -> theFile := consGlobal g !theFile

        | GType (t, l) ->
            currentLoc := l;
            if showGlobals then ignore (E.log "Curing GType(%s) at %a\n"
                                          t.tname d_loc l);
(*            ignore (E.log "before GType(%s -> %a)@!"
                      n d_plaintype t); *)
            (* Change the type in place *)
            if not (isSplitType t.ttype) then
              t.ttype <- fixupType t.ttype;
(*
            ignore (E.log "after GType(%s -> %a)@!"
                      n d_plaintype tnew);
*)
            theFile := consGlobal g !theFile

        | GCompTag (comp, l) ->
            if showGlobals then ignore (E.log "Curing GCompTag(%s) at %a\n"
                                          (compFullName comp) d_loc l);
            currentLoc := l;
            let split = hasAttribute "split" comp.cattr in
            (* Change the fields in place, so that everybody sees the change *)
            List.iter
              (fun fi ->
                let newa, newt = moveAttrsFromDataToType fi.fattr fi.ftype in
                fi.fattr <- newa ;
                fi.ftype <- if split then newt else fixupType newt)
              comp.cfields;
            (* Mangle the name if it is polymoprhic  *)
            let suffix = mangleSuffixForComp comp in
            (* Check if this is supposed to be a COMPAT version of a
             * structure *)
            if suffix <> "" && not !N.use_wild_solver then begin
              if Wrappers.isCompatibleStructVersion comp then
                ignore (E.error
                          "The suffix for the compatible version of %s is %s. This means that you have misused this compatible version. Please check your code."
                          comp.cname suffix);
            end;
            if Poly.isPolyName comp.cname then begin
(*              ignore (E.log "suffix for poly comp %s is %s\n"
                   comp.cname suffix); *)
              if suffix <> "" then
                comp.cname <- comp.cname ^ "_" ^ suffix;
            end;
            let comp' = Poly.getPolyCompRepresentative comp in
            begin
              if comp' == comp then
                (* See if we have defined a version of this type already
                * (ignoring the polymorphic prefix) *)
                theFile := consGlobal g !theFile
              else
                if !N.printVerboseOutput then
                  theFile := consGlobal
                       (GText ("// Polymorphic " ^ (compFullName comp)
                               ^ " was coalesced with " ^
                               (compFullName comp') ^ "\n")) !theFile
            end;
            (*if split then ignore (metaDataType (TComp (comp, [])))*)
            if split then begin
              finalizeMetaDataComp comp;
              match metaDataType (TComp (comp, [])) with
                Some (TComp (metacomp, _)) ->
                  theFile := (GCompTag (metacomp, l)) :: !theFile
              | _ -> ()
            end;
            (* If this was "printf_arguments" then check that the char* field
             * is still SAFE *)
            (if comp.cname = "printf_arguments" then
              match comp.cfields with
                _ :: _ :: str :: _ when str.fname = "s" -> begin
                  match str.ftype with
                    TPtr(TInt _, _) -> ()
                  | _ ->
                      E.s (error "The string field in the printf_arguments descriptor is not SAFE! You have misused this field")
                end
              | _ -> E.s (bug "cure.ml: I cannot understand printf_arguments"));

            ()

        | GFun (f, l) when hasAttribute "nocure" f.svar.vattr ->
            f.sbody <- visitCilBlock unsafeVisitor f.sbody;
            theFile := consGlobal g !theFile

        | GFun (f, l) ->
            currentLoc := l;
            if showGlobals then ignore (E.log "Curing GFun(%s) at %a\n"
                                          f.svar.vname d_loc l);
            (* See if is a vararg function *)
            let isva =
              match f.svar.vtype with
              TFun (_, _, isva, _) -> isva
              | _ -> false
            in
            (* Run the oneret first so that we have always a single return
             * where to place the finalizers  *)
            Oneret.oneret f;
            hasRegisteredAreas := false;
            let newa, newt =
              moveAttrsFromDataToType f.svar.vattr f.svar.vtype in
            f.svar.vattr <- N.replacePtrNodeAttrList N.AtVar
                 (dropAttribute "__format__" newa);
            (* Fixup the return type as well, except if it is a vararg *)
            setFunctionType f (fixupType newt);
            recordOriginalFunctionType newt f.svar.vtype;
            (* If the type has changed and this is a global function then we
             * also change its name  *)
            fixupGlobName f.svar;
            (* This might be a polymorphic instance function. See if we have
             * another one with the same mangling *)
            let f' = Poly.getPolyFuncRepresentative f.svar in
            if f'!= f.svar then begin
              if !N.printVerboseOutput then
                theFile :=
                   consGlobal
                     (GText (sprint 80 (dprintf "// %s coalesced with %s"
                                          f.svar.vname f'.vname)))
                     !theFile;
              raise DeepExit;
            end;

            (* Check that we do not take the address of a formal. If we
             * actually do then we must make that formal a true local and
             * create another formal. Watch for taking the address of the
             * last argument in va functions.  *)
            let newformals, (newbody : stmt clist) =
              let islastva = ref isva in (* To detect last argument in va
                                          * functions *)
              let rec loopFormals (argidx: int) (forms: varinfo list) =
                match forms with
                  [] -> [], fromList f.sbody.bstmts
                | form :: restf -> begin
                    let r1, r2 = loopFormals (argidx + 1) restf in
                    let islastva = !islastva && (islastva := false; true) in

                    let mkReplacement () =
                      (* Make a replacement for the formal. We do not want
                      * to use it directly because it is refered to from
                      * the body of the function *)
                      let tmp = makeTempVar f form.vtype in
                      (*ignore (warnOpt "Replacing formal %s in %s with %s\n"
                                form.vname f.svar.vname tmp.vname); *)
                      (* Replace tmp in the locals with the original form *)
                      f.slocals <-
                         form ::
                         (List.filter (fun x -> x.vname <> tmp.vname)
                            f.slocals);
                      tmp
                    in

                    (* Maybe the address of this formal is taken. If that is
                     * so then add a local with the original type and
                     * initialize it from the actual argument. *)
                    if form.vaddrof && (not islastva) then begin
                      (* Now replace form with the temporary in the
                      * formals *)
                      let tmp = mkReplacement () in
                      tmp :: r1,
                      CConsL(mkSet (var form) (Lval(var tmp)), r2)
                    end else
                      (* The regular case *)
                      form :: r1, r2
                end
              in
              loopFormals 0 f.sformals
            in
            setFormals f newformals;
(*
            ignore (E.log "The new formals for %s: %a\n"
                      f.svar.vname
                      (docList (fun v -> text v.vname)) f.sformals);
            ignore (E.log "The new locals: %a\n"
                      (docList (fun v -> text v.vname)) f.slocals);
*)
            (* We fix the formals *)
            List.iter (fun l ->
              l.vattr <- N.replacePtrNodeAttrList N.AtVar l.vattr;
              l.vtype <- fixupType l.vtype) f.sformals;

            (* Now go and collect a list of fieldinfo for all variables with
             * the heapify attribute set *)
            let heapifiedFields_safe, heapifiedFields_tagged =
              List.fold_right
                (fun v (acc_s, acc_t) ->
                  if hasAttribute "heapify" v.vattr then begin
                    ignore (warnOpt "Moving local %s to the heap." v.vname);
                    let newfield = (v.vname, fixupType v.vtype,
                                    None, v.vattr, !currentLoc) in
                    if isWildOrTaggedAttribute v.vattr then
                      (acc_s,  newfield :: acc_t)
                    else
                      (newfield :: acc_s, acc_t)
                  end else
                    (acc_s, acc_t))
                f.slocals
                ([], [])
            in
            let newbody =
              let doHeapify (istagged: bool)
                            (hFields: (string * typ *
                                       int option * attribute list * location) list)
                            (body: stmt clist) : stmt clist =
                if hFields = [] then body
                else begin
                  let kind = if istagged then "tagged" else "" in
                  (* Make a type for all of them *)
                  let tname  = newTypeName ("heapified" ^ kind) in
                  let hCompInfo =
                    mkCompInfo true tname (fun _ -> hFields) [] in
                  (* Add it to the file *)
                  theFile :=
                     consGlobal (GCompTag (hCompInfo, !currentLoc)) !theFile;
                  (* Create a new local variable *)
                  let heapVar =
                    makeLocalVar f
                      ("__heapified" ^ kind)
                      (TPtr(TComp (hCompInfo, []),
                            if istagged then [N.k2attr N.Wild] else [])) in
                  (* Now insert the call to malloc. It will be processed
                   * properly when the body is cureed later *)
                  let callmalloc =
                    call (Some (var heapVar))
                      (Lval(var (MU.findFunc "wrapperAlloc"
                                   "cure:heapify")))
                      [ SizeOfE (Lval (mkMem (Lval (var heapVar)) NoOffset)) ]
                  in
                  (* Now go over all the fields and register their names in a
                  * hash table *)
                  List.iter (fun fi ->
                    H.add heapifiedLocals
                      fi.fname (mkMem (Lval (var heapVar))
                                  (Field(fi, NoOffset))))
                    hCompInfo.cfields;
                  (* Initialize the things to free *)
                  heapifiedFree :=
                     call None
                       (Lval (var (MU.findFunc "wrapperFree"
                                     "cure:heapify")))
                       [castVoidStar
                           (if istagged then
                             (* We must subtract 4 *)
                             BinOp(MinusA,
                                   CastE(!upointType, Lval(var heapVar)),
                                   integer 4, !upointType)
                           else
                             Lval (var heapVar))]
                     :: !heapifiedFree;
                  CConsL (callmalloc, body)
                end
              in
              doHeapify true heapifiedFields_tagged
                (doHeapify false heapifiedFields_safe newbody)
            in
            (* Remove the heapified locals *)
            f.slocals <-
               List.filter
                 (fun l -> not (H.mem heapifiedLocals l.vname))
                 f.slocals;
            (* Fixup the types of the remaining locals  *)
            List.iter cureLocal f.slocals;
            CC.currentFunction := f;           (* so that maxid and locals can
                                             * be updated in place *)
            (* Clean up the iterator variables *)
            iterVars := [];

            f.sbody.bstmts <- toList newbody;

            (* Initialize and register the locals. Since we do this before
             * curing we will not initialize the temporaries created during
             * curing. But then we know that those are always defiend before
             * use. We must initialize the locals before we do the body
             * because the initialization produces the code for unregistering
             * the locals, which we need when we encounter the Return  *)
            let inilocals =
              List.fold_left initializeVar empty f.slocals in


            (* Do the body now *)
            f.sbody <- cureblock f.sbody;
            let bstmts = fromList f.sbody.bstmts in
            assert (checkBeforeAppend inilocals bstmts);
            f.sbody.bstmts <- toList (append inilocals bstmts);
            H.clear heapifiedLocals;
            heapifiedFree := [];
            (*
             * weimer: we need this in case we are defining a function in
             * this file that is NEVER USED in this file but is referenced
             * externally in another file, and the function in question
             * needs a descriptor (e.g., because we're using
             * INFERCURE=wild).
             * gn: do this late after the type of the function was fixed.
             *)
            (match N.nodeOfAttrlist f.svar.vattr with
              Some n when n.N.kind = N.Wild ->
                let _ = getFunctionDescriptor f.svar in ()
            | _ -> ()) ;
            (* Drop it if it is just a model *)
            if not (hasAttribute "curemodel" f.svar.vattr) then
              theFile := consGlobal (GFun (f, l)) !theFile

        | (GAsm _ | GText _ | GPragma _ | GEnumTag _ ) as g ->
            theFile := consGlobal g !theFile
    end
    with DeepExit -> ()

  and cureglobal vi isdecl init (l: location) =
    currentLoc := l;
    if showGlobals then ignore (E.log "Curing GVar(%s) at %a\n"
                                  vi.vname d_loc l);
    (* Leave alone some functions *)
    let _origType = vi.vtype in
    (* Leave alone the allocation functions !!!. GN: Why? *)
    if true || not (isAllocFunction vi.vname) then begin
      (* Remove the format attribute from functions that we do not leave
       * alone  *)
      let newa, newt = moveAttrsFromDataToType vi.vattr vi.vtype in
      vi.vattr <- N.replacePtrNodeAttrList N.AtVar
            (dropAttribute "__format__" newa);
      (* Fixup the type, but if this is an allocator then do not fix the
       * return type.  We avoid modifying the type if we plan on using
       * compat types to call this function. *)
      if not (hasAttribute "compat" vi.vattr) then begin
        vi.vtype <- fixupType newt;
        if mustBeTagged vi then begin
          vi.vtype <- tagType vi.vtype
        end;
        if isFunctionType newt then
          recordOriginalFunctionType newt vi.vtype;
      end;
    end;
    (* If the type has changed and this is a global variable then we also
     * change its name.  We skip this part for functions that we plan
     * on calling directly using compat types. *)
    if not (hasAttribute "compat" vi.vattr) then begin
      fixupGlobName vi;
    end;
    if isdecl then begin (* A declaration *)
      (*matth: don't mangle the names of wrapped (external) functions. *)
      let oldname, suffix = demangle vi.vname in
      (* Give a warning for any function that:
       * (A) is wrapped,
       * (B) has a mangled name
       * (C) is actually called (as opposed to the functions that need
       *     deep-copy wrappers which call true_<name> instead.)
       * These functions are likely to result in linker errors. *)
      if (suffix <> "")
	  && (Wrappers.hasAWrapper oldname)
          && (vi.vname <> "vsprintf_ssvs")
          && (vi.vname <> "vsnprintf_ssvs") then begin
	if !N.use_wild_solver then begin
	  let wrapperIsolationWarning = "Wrappers are not\n"
	   ^"  really supported when using --curetype=wild.  You will still\n"
	   ^"  need to supply a function called "^vi.vname^" that can\n"
           ^"  interface with this code.  See lib/ccuredlib.c for examples."
	  in
	  theFile := consGlobal
	    (GText
	      (Printf.sprintf
		 "\n/* Possible error:  %s */\n"
		 wrapperIsolationWarning))
	      !theFile;
	  if not !suppressWrapperWarnings then begin
            ignore(warn "%s" wrapperIsolationWarning);
	    if not !E.verboseFlag then begin
              ignore(warn
		"Suppressing further warnings on wrapper name mangling.\n");
	      suppressWrapperWarnings := true;
	    end (* not verbose *)
	  end (* not suppressWrapperWarnings *)
	end (* SolveUtil.use_wild_solver *)
	else if suffix = "t" then begin
	  let wrapperIsolationWarning = oldname ^" appears to be external\n"
	   ^"  (it has a wrapper), yet its name was mangled to "^vi.vname^".\n"
           ^"  Tagged functions will be passed wild arguments and must\n"
           ^"  return wild results. To prevent this function from being\n"
           ^"  tagged, make sure it has been properly declared before use\n"
	   ^"  and is being passed the correct number of arguments.\n"
	   ^" For more information, consult the online documentation on\n"
	   ^"  \"Writing Wrappers\"" in
          ignore (error "%s\n" wrapperIsolationWarning);
	  theFile := consGlobal
	    (GText
	      (Printf.sprintf
		 "\n/* Possible error:  %s */\n"
		 wrapperIsolationWarning))
	      !theFile;
	end (* tagged *)
	else begin
	  let wrapperIsolationWarning = oldname ^" appears to be external\n"
	    ^"  (it has a wrapper), yet it has a mangled name: "^vi.vname^".\n"
            ^"  Did you forget to use __ptrof and a version of __mkptr? \n"
            ^"  Or, perhaps, the mangling is due to structures that are referenced from the type of the function.\n"
	    ^" For more information, consult the online documentation on\n"
	    ^"  \"Writing Wrappers\"." in
          ignore (error "%s\n" wrapperIsolationWarning);
	  theFile := consGlobal
	    (GText
	      (Printf.sprintf
		 "\n/* Possible error:  %s */\n"
		 wrapperIsolationWarning))
	      !theFile;
	end
      end; (* is wrapped and name has been mangled *)
      GVarDecl (vi, l)
      (* theFile := consGlobal (GVarDecl (vi, l)) !theFile *)
    end else begin (* A definition *)
      (* Prepare the data initializer. *)
      let init', doinit = cureinit vi init in
      if doinit <> empty then begin
        extraGlobInit :=
           Clist.fold_left
             (fun acc s ->
               match s.skind with
                 Instr [ Call(_, Lval(Var chk, NoOffset), _, _) ] ->
                   let cname = chk.vname in
                   if cname = "CHECK_FSEQALIGN" ||
                      cname = "CHECK_SEQALIGN" ||
                      cname = "CHECK_INDEXALIGN" then
                     CConsR(acc, s)
                   else
                     acc
               | _ -> CConsR(acc, s))
             !extraGlobInit
             doinit
      end;
      (* Now make one pass through the type and initialize the SIZE fields in
       * arrays. We need this because cureinit only gets the SIZEs for the
       * arrays that have initializers *)
      if containsSizedArray vi.vtype then begin
        useGlobalIterVars := true;
        extraGlobInit := initializeVar !extraGlobInit vi;
        useGlobalIterVars := false;
      end;
     (* theFile := consGlobal (GVar(vi, init',l)) !theFile *)
      GVar (vi, {init=init'}, l)
    end
  in (* cureglobal *)

  if showGlobals then ignore (E.log "Curing file\n");
  let doGlobal x =
    try doGlobal x with e -> begin
      ignore (E.log "cureglobal error (%s) on %a at %a\n"
                (Printexc.to_string e) d_shortglobal x d_loc !currentLoc);
      E.hadErrors := true;
      theFile :=
         consGlobal (GAsm (sprint 2 (dprintf "booo_global %a" d_global x),
                           !currentLoc)) !theFile
    end
  in
  extraGlobInit := empty;
  H.clear taggedTypes;
  (* Create the preamble *)
  preamble ();

  (* First, prepare the WILD functions *)
  prepareWildFunctions file;

  (* Now the original file, including the global initializer *)
  iterGlobals file doGlobal;
  (* Now finish the globinit *)
  let newglobinit =
    match file.globinit with
      None ->
        if !extraGlobInit <> empty then
          let gi = getGlobInit file in
          gi.sbody.bstmts <- toList !extraGlobInit;
          Some gi
        else
          None
    | Some g -> begin
        match !theFile with
          GFun(gi, _) :: rest ->
            theFile := rest; (* Take out the global initializer (last thing
                              * added)  *)
            let res =
              let bstmts = fromList gi.sbody.bstmts in
              assert (checkBeforeAppend !extraGlobInit bstmts);
              toList (append !extraGlobInit bstmts)
            in
            gi.sbody.bstmts <- if compactBlocks then compactStmts res else res;
            Some gi
        | _ -> E.s (bug "cure: Cannot find global initializer")
    end
  in
  (* Now add the function descriptor definitions *)
  theFile := !functionDescriptorInit @ !theFile;

  (* Add definitions for all metadata generation functions. *)
  theFile := getMetagenDefinitions !theFile;

  (* Populate the initializer of rttiArrayDefn, which was added to the preamble
     earlier.  Do this after curing, in case new extensions were added. *)
  MU.generateRTTI ();

  let res = List.rev (!theFile) in
  (* Clean up global hashes to avoid retaining garbage *)
  H.clear typeNames;
  H.clear fixedTypes;
  H.clear fixedComps;
  H.clear taggedTypes;
  H.clear sizedArrayTypes;
  functionDescriptorInit := [];
  extraGlobInit := empty;
  globInitIterVars := [];
  iterVars := [];
  theFile := [];
  let res = {file with globals = res; globinit = newglobinit} in
  Globinit.insertGlobInit res ;

  if showGlobals then ignore (E.log "Finished curing file\n");
  let res' = Stats.time "split" Curesplit.splitLocals res in
  (* sm: after everything else runs, make char arrays 1 byte longer *)
  if !N.useStrings && !N.extendStringBuffers then
    doExpandCharArrays res';
  res'
