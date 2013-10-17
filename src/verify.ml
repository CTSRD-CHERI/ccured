(*
 *
 * Copyright (c) 2001-2002, 
 *  Matt Harren         <matth@cs.berkeley.edu>
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
module Dep = Dependent

let findOrCreateFunc f ?(extraGlobal:global option) name t : varinfo = 
  let rec search glist = 
    match glist with
	GVarDecl(vi,_) :: rest when isFunctionType vi.vtype 
	  && vi.vname = name -> vi
      | _ :: rest -> search rest (* tail recursive *)
      | [] -> (*not found, so create one *)
	  let new_decl = makeGlobalVar name t in
          (match extraGlobal with
             (* Something else we were told to add if we created a decl *)
             Some pragma -> f.globals <- pragma :: f.globals
           | None -> ());
	  f.globals <- GVarDecl(new_decl, locUnknown) :: f.globals;
	  new_decl
  in
  search f.globals

let stringOf (i:int): string = Int32.to_string (Int32.of_int i)

let arrayLen eo : int = 
  try
    lenOfArray eo
  with LenOfArray -> E.s (unimp "array without a size")

(* flatten nested arrays *)
let rec getSize t: int * typ =
  match unrollType t with 
      TArray(bt, e, _) ->
        let mylen = arrayLen e in
        let len', bt' = getSize bt in
        (mylen*len'), bt'
    | _ -> 1, t

(* size in bytes. *)
let mySizeof t: int = 
  try
    let s = bitsSizeOf t in
    if s mod 8 <> 0 then raise (SizeOfError("not a multiple of 8", t));
    s / 8
  with SizeOfError (s, t') ->
    E.s (unimp "Could not take the size of %a: %s." d_type t' s)


let fieldDifference f1 f2: int =
  if f1.fcomp != f2.fcomp then
    E.s (bug "fieldDifference on fields in different structs");
  let comp = TComp(f1.fcomp,[]) in
  let o1, _ = bitsOffset comp (Field(f1, NoOffset)) in
  let o2, _ = bitsOffset comp (Field(f2, NoOffset)) in
  let delta = o2 - o1 in
  if delta mod 8 <> 0 then
    E.s (error "fields %s and %s are not byte-aligned." f1.fname f2.fname);
  delta / 8


(* Should we treat a function polymorphically? 
   As a heuristic, only do this for functions that take a void* argument.
   This way most wrappers will not be polymorphic. *)
let treatAsPoly fv: bool =
  (Poly.isPolyName fv.vname)
  && (let rt, args, _, _ = splitFunctionType fv.vtype in
      List.exists
        (fun (n, t, a) -> (* look for a void* that's not metadata *)
           (isVoidPtrType t) && (N.nodeOfAttrlist a) <> None)
        (argsToList args))

(*     && not (startsWith (Poly.stripPoly fv.vname) "__") *)
(*     (\* Do annotate __endof, __stringof, etc. *)
(*        FIXME: find a better way to tell which funcs are external.*\) *)
        

(* exception Unimp *)
let uniqueUnimplLabel = ref 0
let unimplementedT t =  
  ignore (warn "Can't annotate unimplemented type: %a  (Attrs: %a)\n" 
            d_type t d_attrlist (typeAttrs t));
(*   raise Unimp *)
  incr uniqueUnimplLabel;
  dprintf "unimplemented%d" !uniqueUnimplLabel

let rec hasOneMetaField (t:typ): bool = 
  match unrollType t with
      TPtr(bt, a) ->
        let kind, _ = N.kindOfAttrlist a in
        kind = N.Rtti
    | _ -> false

let rec hasTwoMetaFields (t:typ): bool = 
  match unrollType t with
      TPtr(bt, a) ->
        let kind, _ = N.kindOfAttrlist a in
        kind = N.Seq
    | _ -> false

let maybeStack (a: attributes):bool = 
  match N.nodeOfAttrlist a with
      Some n when N.hasFlag n N.pkStack -> true
    | _ -> false

let dumpSizeAttribute (thisFieldOpt:fieldinfo option) (a:attrparam): doc =
  let thisField = match thisFieldOpt with Some h -> h
    | None -> E.s (bug "dumpSizeAttribute when not in a struct field.")
  in
  let rec doit = function
      AInt k -> num k
    | ASizeOf t -> num (mySizeof t)
    | ACons(s, []) -> begin (* This is a field access into the host *)
        try 
          let targetField = getCompField thisField.fcomp s in
          let diff = fieldDifference thisField targetField in
          dprintf "(memAt %d)" diff
        with Not_found -> 
          E.s (bug "Cannot annotate the dependency %a: Cannot find field %s"
                 d_attrparam a
                 s)
      end
    | ABinOp ((PlusA|MinusA|Mult) as bop, e1, e2) -> 
        dprintf "(%a %a %a)" d_binop bop insert (doit e1) insert (doit e2)
    | _ -> E.s (unimp "Cannot annotate the dependency %a" d_attrparam a)
  in
  doit a

let rec encodeType ?(thisField:fieldinfo option) (t:typ):doc = 
  let unimplemented () = unimplementedT t in
  match unrollType t with
      TInt _ | TEnum _ as t' when bitsSizeOf t' = 32 -> 
        text "int" (*int, uint, long, ulong*)
    | TInt _ | TEnum _ as t' when bitsSizeOf t' = 16 ->
        text "short"
    | TInt _ | TEnum _ as t' when bitsSizeOf t' = 8 -> 
        text "char"
    | TPtr(bt, a) -> begin
        let bt' = encodeType ?thisField bt in
        let kind, _ = N.kindOfAttrlist a in
        let ptrAnn kind = 
          let t = chr '(' ++ text kind ++ bt' ++ chr ')' in
          if maybeStack a then text "(local " ++ t ++ chr ')'
          else t
        in
        match bt, kind with
            _, N.Safe when hasAttribute "size" a ->begin
              match filterAttributes "size" a with
                [Attr(_,[sz])] ->
                  dprintf "(sizedP %a %a)" 
                    insert bt' insert (dumpSizeAttribute thisField sz)
              | _ -> E.s (bug "bad size attr")
            end
          | _, N.Safe -> ptrAnn "safeP "
          | _, N.Rtti -> ptrAnn "rttiP "
          | _, N.Seq  -> ptrAnn "seqP "
          | TComp(ci, _), N.Unknown when ci.cname = "RTTI_ELEMENT" ->
              ptrAnn "safeP "
(*           | TVoid [], N.Unknown -> *)
(*               ignore (warn "\nkind is %a, treating as depValue" *)
(*                         N.d_opointerkind kind); *)
(*               "depValue" *)
          | _, _ ->
              ignore (warn "\nkind is %a, unimplemented"
                        N.d_opointerkind kind);
              unimplemented ()
      end
    | TFun _ -> encodeFuncType t
    | TComp(ci, _) when ci.cstruct ->
        text ci.cname
    | TVoid [] -> text "void"
    | _ -> 
        unimplemented ()

and encodeFuncType = function
    TFun(rt, args, va, a) -> 
      (* FIXME: varargs *)
      if va then
        ignore (warn "vararg functions unimplemented.");
      if a <> [] then
        ignore (warn "function attributes unimplemented.");
      let rec doParams argList: doc = 
        match argList with 
        | (_, t, _)::m1::rest when hasOneMetaField t ->
            let t' = encodeType t in
            chr ' ' ++ t' ++ text " (depValue -4)" ++ (doParams rest)
        | (_, t, _)::m1::m2::rest when hasTwoMetaFields t ->
            let t' = encodeType t in
            chr ' ' ++ t' ++ text " (depValue -4) (depValue -8)" 
            ++ (doParams rest)
        | (_, t, _)::rest ->
            let t' = encodeType t in
            chr ' ' ++ t' ++ (doParams rest)
        | [] -> nil
      in
      text "(func " ++ encodeType rt ++ doParams (argsToList args) 
            ++ chr ')'
  | _ ->
      E.s (bug "nonfunc in encodeFuncType")


let depValue n = text "(depValue " ++ num n ++ chr ')'

(* get the string for the type of a metadata field *)
let encodeMetadata (fi:fieldinfo): doc =
  let bitOffset, x = (bitsOffset 
                        (TComp(fi.fcomp,[])) 
                        (Field(fi, NoOffset))) in
  (* assume the pointer starts 4 bytes before the meta struct *)
  let byteOffset = (-1 * (bitOffset / 8)) - 4 in
(*   ignore (E.log "Offset of %s in %s is %d, x = %d.\n"  *)
(*             fi.fname fi.fcomp.cname byteOffset x); *)
  depValue byteOffset

(* For arrays inside structs, unroll them into "len" different fields *)
(* FIXME: this doesn't work well for variable access *)
let encodeArrayType (fieldName:string) (t:typ) : doc =
  if not (isArrayType t) then 
    E.s (bug " non-array passed to encodeArrayType");
  let len, bt = getSize t in
  let acc: doc ref = ref nil in
  let typestr = encodeType bt in
  for i = len - 1 downto 0 do
    let d = dprintf ", \"%s%d\", %a" fieldName i insert typestr in
    acc := d ++ !acc
  done;
  !acc


let allocFunctions: (string, unit) H.t = H.create 7

let getPragmas (f:file): unit =
  List.iter
    (function 
         GPragma (Attr("ccuredalloc",  AStr(s) :: rest), l) ->
           if not (H.mem allocFunctions s) then begin
             ignore (E.log "%s is an allocation func.\n" s);
             H.add allocFunctions s ()
           end
       | _ -> ()
    )
    f.globals;
  ()
  
let isAlloc (vf:varinfo): bool = 
(* FIXME:  what about name mangling by cure.ml?? *)
  let name = Poly.stripPoly vf.vname in
  let name' = Alpha.getAlphaPrefix name in
  H.mem allocFunctions name'

let isDepVar (vf:varinfo) : bool =
  hasAttribute "isDep" (typeAttrs vf.vtype)

(*******  Annotation macros  *****************************************)

let quoted s: string =
  "\"" ^ s ^ "\""

(* Like quoted, but prepends _ to identifiers if Cil.underscore_name is true.*)
let quotedLabel s: doc = 
  if !Cil.underscore_name then
    text "\"_" ++ text s ++ chr '\"'
  else 
    chr '\"'++ text s ++ chr '\"'

let strOf (d:doc):string = 
  sprint 1024 d

let globalAnn label args:  global =
  let annstr = "#ANN(" ^ label ^", " ^ (strOf args) ^")" in
  GAsm(annstr, !currentLoc)
 
let volatile = [Attr("volatile", []);]

let localAnn label args: instr =
  let annstr = "#ANN(" ^ label ^", " ^ (strOf args) ^ ") " in
  Asm(volatile, [annstr], [], [], [], !currentLoc)

let localVarAnn label func v typ totalsize: instr =
  (*combine the function name and the var name *)
  let vname = quotedLabel (func.svar.vname ^ ":" ^ v.vname) in
  let annstr = dprintf "#ANN(%s, %a, %a, %d, %%0)"
                 label insert vname insert typ totalsize in
  let lv = if isArrayType v.vtype then
    (Var v, Index(Cil.zero, NoOffset))
  else
    (Var v, NoOffset)
  in
  Asm(volatile, [strOf annstr],
      [(None, "=m", lv)],
      [(None,"m", Lval lv)], 
      [], !currentLoc)




let ccuredstruct = "ANN_STRUCT"
let ccuredfunc = "ANN_FUNC"    (* A func that is declared or defined *)
let ccuredroot = "ANN_ROOT"    (* A func that is defined *)
let ccuredsubr = "ANN_SUBR"    (* A func that is defined but that should be 
                                  treated polymorphically (a subroutine). *)
let ccuredglobal = "ANN_GLOBAL"
let ccuredglobalarray = "ANN_GLOBALARRAY"
let ccuredrtti = "ANN_RTTITAGS"

let ccuredalloc = "ANN_ALLOC"
let ccuredlocal = "ANN_LOCAL"
(* let ccuredlocalarray = "ANN_LOCALARRAY" *)
  

(*******   Visitor   *******)

let startsWith s prefix =
  let n = String.length prefix in
  (String.length s >= n) && ((Str.first_chars s n) = prefix)

let annotatedFunctions: (varinfo, unit) H.t = H.create 19
let annotateFundec fv = 
  if H.mem annotatedFunctions fv then
    None
  else if treatAsPoly fv then begin
    ignore (E.log "Will treat %s polymorphically.\n" fv.vname);
    None
  end
  else begin
    H.add annotatedFunctions fv ();
    let fname = Poly.stripPoly fv.vname in
    let ftype = encodeFuncType fv.vtype in
    let typestr = quotedLabel fname ++ text ", " ++ ftype in
    let ann = globalAnn ccuredfunc typestr in
    Some ann
  end

class annotationVisitor 
= object(self)
  inherit nopCilVisitor
    
  val mutable currentFunction: fundec = Cil.dummyFunDec

  method vinst i = begin
    match i with 
        Call (Some dest, Lval(Var vf, NoOffset), _, _) (* when isAlloc vf *) ->
         (*  ignore (E.log "looking at %s\n" vf.vname); *)
          if not (isAlloc vf) then DoChildren else begin
          (* FIXME:  what about the other properties of the allocation
           *  functions? *)
          let t = encodeType (typeOfLval dest) in
          self#queueInstr [localAnn ccuredalloc t];
          DoChildren
          end
      | _ -> DoChildren
  end

(*   method vstmt s = begin *)
(*     match s.skind with *)
(*         Loop (b, l, _, _) -> *)
(*           let depvars = List.filter isDepVar currentFunction.slocals in *)
(*           let anns = *)
(*             List.map (fun v -> *)
(*                         let t = encodeType v.vtype in *)
(*                         localVarAnn "LOOP_INV" currentFunction v (quoted t)) *)
(*               depvars *)
(*           in *)
(*           b.bstmts <- (mkStmt (Instr anns))::b.bstmts; *)
(*           DoChildren *)
(*       | _ -> DoChildren *)
(*   end *)

  method vvdec v = begin
    if maybeStack v.vattr then begin
      assert (v.vaddrof);
      assert (not v.vglob);
      (* For a local, this flag would only be set if we take the address of v, 
         right? *)
      (* ignore (E.log "  We take the address of %s.\n" v.vname); *)
      let t = encodeType v.vtype in
      let s = mySizeof v.vtype in
      self#queueInstr 
        [localVarAnn ccuredlocal currentFunction v t s];
      ()
    end
    else if not v.vglob then begin
      match v.vtype with
          TArray (bt, Some size, a) -> begin
            match isInteger (constFold true size) with
              None -> E.s (error "Non-constant array size")
            | Some size' ->
                let size'' = (Int64.to_int size') * mySizeof bt in
                let t = encodeType bt in
                self#queueInstr 
                  [localVarAnn ccuredlocal currentFunction v t size''];
                ()
          end
        | TArray _ -> E.s (unimp "array without a size")
        | _ ->
            assert (not v.vaddrof);
            ()
    end;
    DoChildren
  end

  method vglob g = begin
    try
      match g with 
          GFun (fdec, l) ->
            currentFunction <- fdec;
            (* Step 1: declare the function signature *)

            if fdec.svar.vname = !Globinit.mainname
	      && fdec.svar.vstorage <> Static then begin
                ignore (warn "skipping entrypoint \"%s\"" fdec.svar.vname );
                DoChildren
              end
            else if treatAsPoly fdec.svar then
              let rootAnn = globalAnn ccuredsubr
                              (quotedLabel (Poly.stripPoly fdec.svar.vname)) in
              ChangeDoChildrenPost(
                [rootAnn; g],
                (fun g -> currentFunction <- Cil.dummyFunDec; g)
              )
            else begin
              let anno = annotateFundec fdec.svar in
              let rootAnn = globalAnn ccuredroot 
                              (quotedLabel (Poly.stripPoly fdec.svar.vname)) in
              let newG = match anno with
                  Some ann -> [ann; rootAnn; g]
                | None -> [rootAnn; g]
              in
              ChangeDoChildrenPost(
                newG,
                (fun g -> currentFunction <- Cil.dummyFunDec; g)
              )
            end
        | GVarDecl (vi, l) 
            when isFunctionType vi.vtype (* && vi.vname <> "__ccuredInit" *) ->
            begin
              let anno = annotateFundec vi in
              match anno with
                  Some ann -> ChangeDoChildrenPost( [ann; g],(fun g -> g))
                | None -> DoChildren
            end
        | GCompTag (ci, l) ->
            if ci.cname = "printf_arguments" then begin
              ignore (warn "skipping \"%s\"" ci.cname );
              DoChildren
            end
            else if hasAttribute "tagged" ci.cattr then begin
              if ci.cstruct then begin
                match ci.cfields with
                  [tag; data] ->
                    if ((bitsSizeOf data.ftype) mod 8) <> 0 then
                      E.s (unimp "bitsSizeOf data field not divisible by 8");
                    ignore (E.log "Found tagged union: %s.\n" ci.cname);
                    let annstr = dprintf "\"%s\", \"__tag\", (depValue 4), \"__data\", (taggedUnion %d)"
                                   ci.cname ((bitsSizeOf data.ftype) / 8)
                    in
                    let ann = globalAnn ccuredstruct annstr in
                    ChangeDoChildrenPost(
                      [ann; g],
                      (fun g -> g)
                    )
                | _ -> 
                    E.s (error "I don't recognize the fields in this tagged unio n.");
              end
              else (* the union in a tagged union struct *)
                SkipChildren
            end
            else if ci.cstruct then begin
              (* ignore (E.log "printing struct \"%s\"\n" ci.cname ); *)
              let annstr = ref (text(quoted ci.cname)) in
              let isMetaStruct = Ccutil.hasPrefix "meta_" ci.cname in
              List.iter
                (fun fi ->
                   if fi.fname = Cil.missingFieldName then
                     E.s (unimp "not a real field? in %a" d_global g);
                   if isArrayType fi.ftype then 
                     annstr := !annstr ++ encodeArrayType fi.fname fi.ftype
                   else begin
                     let typestr = try
                       let ptrField = 
                         H.find Dep.metaFields (ci.ckey, fi.fname) in
                       let diff = fieldDifference fi ptrField in
                       depValue diff
                     with Not_found ->
                       if isMetaStruct then
                           encodeMetadata fi
                         else
                           encodeType ~thisField:fi fi.ftype 
                     in
                     annstr := !annstr ++ text ", " ++ text (quoted fi.fname)
                                       ++ text ", " ++ typestr
                   end)
                ci.cfields;
              let ann = globalAnn ccuredstruct !annstr in
              ChangeDoChildrenPost(
                [ann; g],
                (fun g -> g)
              )
            end
            else begin
              ignore (unimplementedT (TComp(ci,[])));
              SkipChildren
            end
        | GVar (vi, {init = Some _}, l)
            when vi.vname = "RTTI_ARRAY" ->
            let arrayName = quotedLabel vi.vname in
            let extensions = Array.to_list (MU.getAllExtensions ()) in
            let strs: doc list = 
              List.map
                (fun ex ->
                   match ex with
                     MU.ExVoid
                   | MU.ExScalar -> text "void"
                   | MU.ExComp ci -> encodeType (TComp (ci, []))
                   | MU.ExAuto(t, n) -> encodeType t
                   | MU.ExNonPointer t -> text "(nonPtr " ++ (encodeType t) 
                                            ++ chr ')'
                   | MU.ExType ti -> E.s (unimp "ExType")
                )
                extensions
            in
            let annstr = docList (fun x -> x) () (arrayName::strs) in
            let ann = globalAnn ccuredrtti annstr in
            ChangeDoChildrenPost( 
              [ann; g],
              (fun g -> g)
            )
        | GVar (vi, _, l) when vi.vname = "RTTI_ARRAY" ->
            E.s (bug "Bad RTTI_ARRAY")
        | GVar (vi, _, l) ->
            (* ignore (E.log "annotating %s: %a\n" vi.vname d_type vi.vtype); *)
            (match vi.vtype with
                 TArray(bt, leno, a) when (bitsSizeOf bt) < 32 ->
                   (* FIXME: hack for chars.  Expand this array so its 
                      length is a multiple of 4. *)
                   let len = arrayLen leno in
                   let len' = ((len + 3) / 4) * 4 in
                   assert (len'>=len && len'<len+4);
                   vi.vtype <- TArray(bt, Some (integer len'), a);
               | _ -> ());
            let ann = 
              match vi.vtype with
                  TArray _ ->
                    let size, bt = getSize vi.vtype in
                    globalAnn ccuredglobalarray 
                      (dprintf "%a, %a, %d" 
                         insert (quotedLabel vi.vname)
                         insert (encodeType bt)
                         size)
                | TFun _ -> E.s (bug "Use GVarDecl for function prototypes.")
                | _ -> globalAnn ccuredglobal (quotedLabel vi.vname
                                               ++ text ", " 
                                               ++ (encodeType vi.vtype))
            in
            ChangeDoChildrenPost( 
              [ann; g],
              (fun g -> g)
            )
      | _ -> 
          DoChildren
    with e -> 
      (* DoChildren *)
      raise e
  end
        
end

(*******  Preprocess  Visitor   *******)

let isMDArray t =
  match t with TArray(TArray _, _, _) -> true
    | _ -> false

let isMDArrayExp e =
  match e with StartOf lv -> isMDArray (typeOfLval lv)
    | _ -> isMDArray (typeOf e)

class preprocessVisitor (calloc: varinfo) = object(self)
  inherit nopCilVisitor

  method vinst i = begin
    match i with
      Call(Some res, Lval(Var vf, NoOffset), [size], l) when
        vf.vname = "malloc" -> 
          let noInitNeeded =
            match unrollType (typeOfLval res) with
              TPtr(bt, _) -> isArithmeticType bt
            | _-> E.s (bug "Allocating a non-pointer")
          in
          if noInitNeeded then
            DoChildren
          else begin
            let i' = Call (Some res, Lval(Var calloc, NoOffset),
                           [integer 1; size], l) in
            ChangeDoChildrenPost([i'], (fun il -> il))
          end
    | _ -> DoChildren
  end

    (* Assert that we never do arith on MD arrays. *)
  method vexpr e = begin
    match e with 
        BinOp((PlusPI 
              | IndexPI
              | MinusPI
              | MinusPP), e1, _, _) when isMDArrayExp e1 ->
          E.s (unimp "I haven't implemented pointer arith on multi-dimensional arrays yet.")
      | _ -> 
         (*  ignore (E.log "[%a] looking at %a : %a\n" d_loc !currentLoc  *)
(*                     d_plainexp e d_plaintype (typeOf e)); *)
          DoChildren
  end

  method vlval lv = begin
    let rec helper (acc:exp) (t: typ) (off:offset) : exp =
      match t with
          TArray(bt, leno, _) -> begin
            let d = arrayLen leno in
            match off with
                NoOffset -> (* Treat as "[0]" *)
                  let n = BinOp(Mult, acc, integer d, intType) in
                  helper n bt NoOffset
              | Field _ -> E.s (error "bad offset to array")
              | Index (e, o) ->
                  let n = BinOp(PlusA,
                                BinOp(Mult, acc, integer d, intType),
                                e,
                                intType) in
                  helper n bt o
          end
        | _ -> acc
    in
    let (lh,offset) = lv in
    let arrayT = unrollTypeDeep (typeOfLval (lh, NoOffset)) in
    if isMDArray arrayT && offset <> NoOffset then begin
      ignore (E.log "MD: Replacing %a\n" d_plainlval lv);
      let newindex = constFold false (helper zero arrayT offset) in
      let newLV = lh, Index (newindex, NoOffset) in
      ignore (E.log "  with  %a\n" d_lval newLV);
      ChangeTo newLV
    end
    else
      DoChildren
  end

(* Handle initialization *)
  method vglob g = begin
    match g with
        GVar (vi, ({init = Some (CompoundInit(at, _) as old)} as i'), l)
          when  isMDArray vi.vtype -> 
            (* ignore (E.log "init is %a\n" d_plaininit old); *)
            (* A simpler solution is possible when we know that the base type
               will always use SingleInit (i.e. is not a struct) *)
            let rec helper (sofar:int) (off:offset) (i:init) (t: typ)
              (acc: (offset * init) list)
              : (offset * init) list =
              let multiplier = match t with
                  TArray(bt, leno, _) -> (arrayLen leno)
                | _ -> 1 (* base case *)
              in
              let index = match off with
                  NoOffset ->
                    (sofar * multiplier)
                | Field _ -> E.s (error "bad offset in init. F")
                | Index (e, o) ->
                    if (o <> NoOffset) then E.s (bug "huh?");
                    let e' = match isInteger e with
                        Some i64 -> Int64.to_int i64
                      | None -> E.s
                              (error "bad offset in init (not const)")
                    in
                    (sofar + e') * multiplier
              in
(*               ignore (E.log  *)
(*                   " t is %a\n  off is %a\n  sofar is %d\n  index is %d\n" *)
(*                   d_type t (d_offset nil) off sofar index); *)
              (* let completeoff = addOffset off sofar in *)
              match i with 
                  SingleInit (exp) ->
                    (Index(integer index, NoOffset), i)::acc
                | CompoundInit (typI, initlist) -> (* recurse over the 
                                                      elements of comp type*)
                    foldLeftCompound ~implicit:true 
                      ~doinit:(helper index) ~ct:typI
                      ~initl:initlist ~acc:acc
            in
            let initList = helper 0 NoOffset old vi.vtype [] in
            i'.init <- Some (CompoundInit(at, List.rev initList));
            (* ignore (E.log "   changed to %a\n"  *)
(*                       d_plaininit (CompoundInit(at, initList))); *)
            DoChildren
      | _ -> DoChildren
  end
end

let fixTypeDecl t : typ = 
  match unrollTypeDeep t with
      TArray(TArray _, _, a) -> begin
        let len, bt = getSize t in
        let newT = TArray(bt, Some (integer len), a) in
        ignore (E.log "Multi-dimensional array:  replacing %a with %a\n"
                  d_plaintype t d_plaintype newT);
        newT
      end
    | _ -> t


(* Later, change the array declarations themselves *)
class preprocessVisitor2 = object(self)
  inherit nopCilVisitor
    
  method vvdec v = begin
    let newT = fixTypeDecl v.vtype in
    v.vtype <- newT;
    DoChildren
  end
    (* FIXME: need a better solution for arrays in structs *)
(*   method vglob g = begin *)
(*    (match g with *)
(*         GCompTag (comp, _) when comp.cstruct -> *)
(*           let fieldVisit fi = *)
(*             fi.ftype <- fixTypeDecl fi.ftype; *)
(*           in *)
(*           List.iter fieldVisit comp.cfields *)
(*        | _ -> ()); *)
(*     DoChildren *)
(*   end *)

(* Fix pointers to array types. we'd actually like to visit all types,
   but for now we avoid arrays in structs*)
  method vtype t = begin
    match unrollTypeDeep t with
        TPtr(bt, a) ->
          let newBT = fixTypeDecl bt in
          ChangeTo (TPtr(newBT, a))
      | _ ->
          DoChildren
  end
end

(*******  Module entry       *****************************************)

let annotate (f: file) : unit = 
  ignore(E.log "Printing annotations:\n");
  getPragmas f;
  let annVisitor = new annotationVisitor in
  visitCilFile annVisitor f;
  let gl = globalAnn ccuredglobalarray 
             (quotedLabel "__ccured_va_tags"
              ++ text ", int, 32") in
  let gl2 = globalAnn ccuredglobal (quotedLabel "__ccured_va_count"
                                    ++ text ", int") in
  (* TODO: __stringof_sq, __Verify_nul_q *)
  f.globals <- gl::gl2::f.globals;
  ()


(* No Preproccessing at the moment *)
let preprocess (f: file) : unit = 
  ignore(E.log "Preprocessing for annotations:\n");
  let callocPragma = GPragma (Attr("ccuredalloc",  
                                   [AStr("calloc");
                                    ACons("zero", []);
                                    ACons("sizemul", [AInt 1; AInt 2])]),
                              locUnknown) in
  let calloc = findOrCreateFunc f ~extraGlobal:callocPragma "calloc"
                        (TFun (voidPtrType, 
                               Some([("nmemb", uintType, []) ; 
                                     ("size", uintType, []) ]), 
                               false, [])) in
  visitCilFile (new preprocessVisitor calloc) f;
  visitCilFile (new preprocessVisitor2) f;
  ()

