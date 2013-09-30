(** See the copyright notice at the end of this file *)

(** Handle the CCured tagged unions *)
open Cil
open Pretty

module H = Hashtbl
module IH = Inthash
module E = Errormsg

module N = Ptrnode

module MU = Markutil
module U = Util

let hasPointers (t: typ) : bool = 
  existsType (function TPtr _ -> ExistsTrue | _ -> ExistsMaybe) t


(** Data structures for discriminated unions. *)

(* Remember the fields that are contained in a discriminated union.
   Indexed on union key and field name. *)
let discriminatedUnionFields: 
  (int * string, unit) H.t = H.create 17


(** Remember the discriminator fields as well. For each one we remember a 
 * list of the sibling fields (of union type) that depend on it. 
 * Indexed by the structure key, and the name of the discriminator field. *)
let discriminatorFields: (int * string, fieldinfo) H.t = H.create 17

(* Is this the union part of a tagged union? *)
let isDiscriminatedUnion (u:compinfo) : bool =
 (not u.cstruct) && (hasAttribute "discriminated_union" u.cattr)

(* Is this a field in a discriminated union? *)
let isDiscriminatedField (f:fieldinfo) : bool =
  H.mem discriminatedUnionFields (f.fcomp.ckey, f.fname)

(** Get the discriminator for a field, given a host. Compute a list of names 
 * of discriminator fields, a list of instructions to compute the 
 * discriminator value, and the discriminator expression. *)
let getDiscriminator (host: lval) (f: fieldinfo) 
  : string list * instr list * exp = 
  let hostcomp: compinfo = 
    match unrollType (typeOfLval host) with 
      TComp (comp, _) when comp.cstruct -> comp
    | _ -> 
        E.s (error "The host for a discriminated field access does not have a structure type")
  in
  let discriminators: (string, unit) H.t = H.create 7 in
  let rec compileDiscr (d: attrparam) = 
    match d with 
      AInt k -> [], integer k
    | ACons (s, []) -> begin (* This is a field access into the host *)
        try 
          let hostf = getCompField hostcomp s in
          if not (isIntegralType hostf.ftype) then 
            E.s (error "The discriminator field \"%s\" does not have an integer type"
                   hostf.fname);
          H.add discriminators s ();
          let discr_lval = addOffsetLval (Field(hostf, NoOffset)) host in
          [], Lval discr_lval
        with Not_found -> 
          E.s (error "Cannot compile the discriminator for %s" f.fname)
    end
    | ABinOp (bop, e1, e2) -> 
        let i1', e1' = compileDiscr e1 in
        let i2', e2' = compileDiscr e2 in
        i1' @ i2',  BinOp(bop, e1', e2', intType)
    | AUnOp (uo,e1) ->
        let i1', e1' = compileDiscr e1 in
        i1', UnOp(uo, e1', intType)
    | ASizeOf t -> [], CastE(intType, SizeOf t)
    | ASizeOfE e1 -> 
        let _, e1' = compileDiscr e1 in
        [], CastE(intType, SizeOfE e1')
    | _ -> E.s (error "Cannot compile the discriminator for %s: %a" 
                  f.fname d_attrparam d)
  in
  match filterAttributes "selectedwhen" f.fattr with
    [ Attr(_, [ ap ]) ] -> 
      let il, res = compileDiscr ap in 
      U.keys discriminators, il, res

  | [] -> E.s (error "Field %s does not have a SELECTEDWHEN clause" f.fname)
  | _ ->  E.s (error "Field %s has more than one SELECTEDWHEN clause" f.fname)

(** Called from markptr to mark a union. this is called after the fields are 
 * marked and have nodes associated *)
let markUnionComp (comp: compinfo) (comptagloc: location) : unit = 
  (* Maybe we must turn this composite type into a struct *)
  if comp.cstruct then 
    E.s (E.bug "You called Taggedunion.markUnionComp on a struct %s"
           comp.cname);

  (* Should we turn it into a struct ?? *)
  if hasAttribute "safeunion" comp.cattr then 
    comp.cstruct <- true

  (****************************************)
  (***** DISCRIMINATED UNIONS *************)
  (****************************************)
  else if hasAttribute "selector" comp.cattr then begin
    () (* We have done it already *)
  end else if hasAttribute "trustedunion" comp.cattr then 
    () 
  else if hasAttribute "tagged" comp.cattr then begin
    ()
  end else if hasAttribute "discriminated_union" comp.cattr then begin
    () (* We have done it already *)
  end else begin
    (* keep track of the widest field *)
    let widestFieldLen = ref 0 in
    let widestFieldNode = ref N.dummyNode in
    List.iter 
      (fun f -> 
        let thisWidth = try bitsSizeOf f.ftype with SizeOfError _ -> 0 in
        if thisWidth > !widestFieldLen then begin
          widestFieldLen := thisWidth;
          match N.nodeOfAttrlist f.fattr with 
            Some n when n != N.dummyNode -> 
              widestFieldNode := n
          | _ -> E.s (E.bug 
                        "markCompInfo: field %s in %s does not have a node"
                        f.fname comp.cname)
        end)
      comp.cfields;
    
    (** Look for incompatible fields *)
    List.iter
      (fun f -> 
        let thisnd =  match N.nodeOfAttrlist f.fattr with
          Some n when n != N.dummyNode -> 
            n
        | _ -> E.s (bug "markCompInfo: no node found for field")
        in
        if thisnd != !widestFieldNode then 
          ignore (N.addEdge 
                    !widestFieldNode thisnd 
                    (N.ECast N.EEK_union) (Some comptagloc))
            )
      comp.cfields
  end
  
let addEdgesToTaggedUnion (union: compinfo) : unit =
  assert(not union.cstruct);
  (* Consider two union fields.  If f1 is a subtype of f2, or vice versa,
     then a program can insert a value into one field and read it from the
     other.  So make f1 and f2 have the same kind. *)
  let doEdge f1 f2: unit = 
    match unrollType f1.ftype, unrollType f2.ftype with
      TPtr(_, a1), TPtr(_, a2) -> begin
        match N.nodeOfAttrlist a1, N.nodeOfAttrlist a2 with
          Some n1, Some n2 -> (* FIXME: check subtyping *)
(*             ignore (E.log "adding edges from %a to %a.\n"  *)
(*                       d_type f1.ftype d_type f2.ftype); *)
            ignore (N.addEdge n2 n1
                      (N.ESameKind N.EEK_taggedUnion)
                      (Some !currentLoc))
        | None, Some n2 -> E.s (bug "missing node for %a." d_type f1.ftype)
        | _, None -> E.s (bug "missing node for %a." d_type f2.ftype)
      end
    | _ -> (* one or both fields are nonpointers.  We don't add edges since
              only pointers have kinds. 
              The only valid cast in this case is ptr -> scalar, so
              we're trusting that value of the pointer is always the first
              field in a fat pointer. *)
(*         ignore (E.log "not adding edge from %a to %a.\n"  *)
(*                   d_type f1.ftype d_type f2.ftype); *)
        ()              
  in
  (* call doEdge on each pair of fields in the union. *)
  let rec outerloop: fieldinfo list -> unit = function
      [] -> ()
    | f1::rest -> 
        (* Register the type to make sure it has an extension in the
           hierarchy. *)
        MU.registerRttiType f1.ftype;

        List.iter (fun f2 -> doEdge f1 f2) rest;
        outerloop rest
  in
  outerloop union.cfields;
  ()


let checkUnionTag =
  let fdec = emptyFunction "CHECK_UNIONTAG" in
  fdec.svar.vtype <- TFun(voidType,
                          Some [ ("tag", intType, []);
                               ],
                          false, []);
  fdec.svar.vstorage <- Static;
  MU.registerGlobalDeclaration fdec.svar;
  fdec

let initFieldFunc =
  let fdec = emptyFunction "CHECK_INITUNIONFIELD" in
  fdec.svar.vtype <- TFun(voidType,
                          Some [ ("selected", intType, []); 
                                 ("unionp", voidPtrType, []); 
                                 ("size", uintType, []); 
                               ],
                          false, []);
  fdec.svar.vstorage <- Static;
  MU.registerGlobalDeclaration fdec.svar;
  fdec

(* Pseudo-function.  cure.ml replaces this with the actual tag. 
   If value is an RTTI pointer, this gives the dynamic type.
   Otherwise, cure.ml uses a tag based on the static type.*)
let rttiTagFor =
  let fdec = emptyFunction "__CCURED_RTTITAGFOR" in
  fdec.svar.vtype <- TFun(MU.rttiType,
                          Some [ ("value", voidPtrType, []); 
                               ],
                          false, []);
  fdec.svar.vstorage <- Static;
  MU.registerGlobalDeclaration fdec.svar;
  fdec

(* Pseudo-function.  cure.ml replaces this with the actual tag. 
   value must be "sizeof(e)". 
   cure.ml uses a tag based on the static type of e. Use this to get the
   tag of a nonpointer.*)
let rttiStaticTagFor =
  let fdec = emptyFunction "__CCURED_RTTISTATICTAGFOR" in
  fdec.svar.vtype <- TFun(MU.rttiType,
                          Some [ ("value", intType, []); 
                               ],
                          false, []);
  fdec.svar.vstorage <- Static;
  MU.registerGlobalDeclaration fdec.svar;
  fdec

(* Pseudo-function.  cure.ml replaces this with the actual check. 
   value must be "sizeof(lv)",  where lv is the field being read. *)
let rttiCheck =
  let fdec = emptyFunction "__CCURED_RTTIUNIONCHECK" in
  fdec.svar.vtype <- TFun(MU.rttiType,
                          Some [ ("value", intType, []); 
                               ],
                          false, []);
  fdec.svar.vstorage <- Static;
  MU.registerGlobalDeclaration fdec.svar;
  fdec

(* Note: this isn't the right signature for __CHECK_HASRTTITYPE.
   We will pass "sizeof field" here as the second arg, and this
   will be replaced by the static RTTI tag of this field during curing. *)
let rttiHasTag =
  let fdec = emptyFunction "__CHECK_HASRTTITYPE" in
  fdec.svar.vtype <- TFun(intType,
                          Some [ ("srtti", MU.rttiType, []); 
                                 ("field", intType, []); 
                               ],
                          false, []);
  fdec.svar.vstorage <- Static;
  MU.registerGlobalDeclaration fdec.svar;
  fdec



(** Check the accesses to all discriminated fields in an lval *)
let checkDiscriminatedFieldAccess ((h, off) : lval) : instr list = 
  let rec loop (lval_to_here: lval) (off: offset) : instr list = 
    match off with 
      Field(ufield, Field(which, resto)) -> 
        if isDiscriminatedField which 
        then begin
          let _, il, (it: exp) = getDiscriminator lval_to_here which in
          il @
          [ Call(None, Lval (var checkUnionTag.svar),
                 [ it ], !currentLoc) ] @
          (loop (addOffsetLval (Field(ufield, Field(which, NoOffset))) 
                   lval_to_here) resto)
        end else begin

          loop (addOffsetLval (Field(ufield, NoOffset)) lval_to_here) 
            (Field(which, resto))
        end
            
    | Field (f, resto) -> 
        (* We have a problem if we are accessing the field of the union 
         * directly *)
        if isDiscriminatedField f then 
          E.s (error "Access to a discriminated union field (%s) that is outside a host structure"
                 f.fname);
        loop (addOffsetLval (Field(f, NoOffset)) lval_to_here) resto

    | Index (e, resto) -> 
        loop (addOffsetLval (Index(e, NoOffset)) lval_to_here) resto

    | NoOffset -> []
  in
  loop (h, NoOffset) off


(*** Define a visitor that traverses the code and adds tags to the unions 
 * that are supposed to be tagged *)

(* Keep track of the tagged unions: a mapping from old_key * field name to a 
 * new offset *)
let taggedUnionFields: (int * string, offset) H.t = H.create 17
(* For each structure that was created to embed a tagged union, keep the 
 * tagField and the union definition for the data field. *)
let taggedUnionEmbeddings: (fieldinfo*compinfo*location) IH.t = IH.create 17


(*  Processes any writes to tagged fields in the lvalue of "(b,off) := rvalue".
 *  For each tagged union reference, inserts commands to change the
 *  tag and initialize the field.
 *)
let findTaggedFieldWrites (vis:cilVisitor) ((b, off) : lval)  ~(rvalue: exp)
 : unit =
  let rec loop (lval_to_here: lval) 
               (restoff: offset) : unit = 
    match restoff with 
      Field(dfield, Field(which, resto)) 
        when IH.mem taggedUnionEmbeddings dfield.fcomp.ckey -> begin
          (* Find the tagfield *)
          let tagField, _, _ = 
            IH.find taggedUnionEmbeddings dfield.fcomp.ckey in
          let tagLval =
            (addOffsetLval (Field(tagField, NoOffset)) lval_to_here) in
          let dataLval =
            (addOffsetLval (Field(dfield, NoOffset)) lval_to_here) in
          let fieldLval = addOffsetLval
                            (Field(dfield, (Field(which, NoOffset)))) 
                            lval_to_here  in (* == dataLval.which *)
	  let sizeofField = bitsSizeOf which.ftype in
	  let setTag = 
            if isPointerType which.ftype then
              (* After solving, there may be a dynamic rtti tag associated
                 with rhs *)
              Call (Some tagLval, (* tagLval := TAG_OF(rhs) *)
                    Lval (var rttiTagFor.svar),
                    [rvalue], !currentLoc)
	    else 
	      Call (Some tagLval,(* tagLval := STATIC_TAG_OF(the field) *)
                    Lval (var rttiStaticTagFor.svar),
                    [SizeOfE (Lval fieldLval)], 
                    !currentLoc)
          in
	  let initFields = 
            if sizeofField > (bitsSizeOf !upointType) then
              (* Check whether the union is already using this tag.  If so,
                 initFieldFunc won't clear the field. *)
              let alreadyHasTag = var (makeTempVar !MU.currentFunction
                                         ~name:"alreadyHasTag" intType) in
              (* Note: this isn't the correct way to call __CHECK_HASRTTITYPE.
                 the "sizeof field" arg will be replaced by the static RTTI
                 tag of this field during curing. *)
              [Call(Some alreadyHasTag, Lval (var rttiHasTag.svar),
                   [Lval tagLval; SizeOfE (Lval fieldLval)],
                   !currentLoc);
	       Call(None, 
		    Lval (var initFieldFunc.svar), 
		    [Lval alreadyHasTag; 
                     AddrOf dataLval; 
                     (SizeOfE (Lval dataLval))], 
		    !currentLoc);
               setTag]
	    else 
              (* When the field is only one word or less, skip initialization
	       * the.  Either this is a scalar, and we don't care;
	       * or it is a single pointer, and whatever write to this field
	       * triggered this initialization will overwrite the entire field.
	       *)
              [setTag]
          in
          (* Queue the outer fields first so they are initialized before
             inner fields. *)
          vis#queueInstr initFields;
          loop 
            (addOffsetLval (Field(dfield, (Field(which, NoOffset)))) 
               lval_to_here)
            resto;
          ()
        end
    | Field (f, resto) -> 
        loop (addOffsetLval (Field(f, NoOffset)) lval_to_here) resto
    | Index (e, resto) -> 
        loop (addOffsetLval (Index(e, NoOffset)) lval_to_here) resto
    | NoOffset -> ()
  in
  loop (b, NoOffset) off 


(* Given an lvalue find all accesses to fields inside tagged unions.  
 *  Returns for each tagged union reference:
 *  - (for reads) a command to check the tag
 *  - (for HASUNIONTAG) a closure that implements HASUNIONTAG for the field.
 *)
let findTaggedFieldReads ((b, off) : lval)
    : (instr * (lval -> instr)) list = 
  let rec loop (lval_to_here: lval) 
               (restoff: offset) : (instr * (lval -> instr)) list = 
    match restoff with 
      Field(dfield, Field(which, resto)) 
        when IH.mem taggedUnionEmbeddings dfield.fcomp.ckey -> begin
          let fieldLval = addOffsetLval
                            (Field(dfield, (Field(which, NoOffset)))) 
                            lval_to_here  in
          let readtest = Call(None, Lval (var rttiCheck.svar),
                              [SizeOfE(Lval fieldLval)], 
                              !currentLoc)
          in
          (* Generate code for CCURED_HASUNIONTAG *)
          let tagField, _, _ = 
            IH.find taggedUnionEmbeddings dfield.fcomp.ckey in
          let tagLval =
            (addOffsetLval (Field(tagField, NoOffset)) lval_to_here) in
          (* FIXME: this is unsound, because we access inner tags without checking that the outer tags were okay. *)
          let hasTag = fun res ->
            (* Note: this isn't the correct way to call __CHECK_HASRTTITYPE.
               the "sizeof field" arg will be replaced by the static RTTI tag
               of this field during curing. *)
            Call(Some res, Lval (var rttiHasTag.svar),
                 [Lval tagLval; SizeOfE (Lval fieldLval)],
                 !currentLoc)
          in
          ((readtest, 
            hasTag)
             (* Do the outer fields first, then inner *)
           :: (loop fieldLval resto))
            
        end
    | Field (f, resto) -> 
        loop (addOffsetLval (Field(f, NoOffset)) lval_to_here) resto
    | Index (e, resto) -> 
        loop (addOffsetLval (Index(e, NoOffset)) lval_to_here) resto
    | NoOffset -> []
  in
  loop (b, NoOffset) off 


let containsTaggedFields ((b,off):lval) : bool =
  let rec helper (off:offset) : bool =
    match off with 
      Field(dfield, _) 
        when IH.mem taggedUnionEmbeddings dfield.fcomp.ckey -> true
    | Field (f, resto) -> helper resto
    | Index (e, resto) -> helper resto
    | NoOffset -> false
  in
  helper off



class taggedUnionsVisitor : cilVisitor = object (self)
  inherit nopCilVisitor
  val mutable ignoreAccesses: bool = false;

  (* Intercept accesses to the fields *)
  method voffs (off: offset) : offset visitAction = 
    match off with 
      Field(fi, resto) -> begin
        (** emit warnings for accessing fields of trusted unions *)
        if hasAttribute "trustedunion" fi.fcomp.cattr then 
          ignore (warn "Accessing field %s of trusted union %s\n" 
                    fi.fname fi.fcomp.cname);
        try
          let newoff = H.find taggedUnionFields (fi.fcomp.ckey, fi.fname) in
          let resto' = visitCilOffset (self :> cilVisitor) resto in
          ChangeTo (addOffset resto' newoff)
        with Not_found -> DoChildren
      end
    | _ -> DoChildren

  (* Check that we are not taking the address of such a field *)
  method vexpr (e: exp) = 
    if ignoreAccesses 
    then DoChildren (*We're in the argument to a ccured_hasuniontag call *)
    else
    (* Process the expression first *)
    let postProcessExp (e: exp) : exp = 
      match e with 
        AddrOf lv | StartOf lv -> begin
          if containsTaggedFields lv then
            ignore (error "You cannot take the address of a field in a tagged union");

          (* Pretend that we are accessing it. If we need some checks, then 
           * we reject this *)
          if [] <> checkDiscriminatedFieldAccess lv then 
            ignore (error "You cannot take the address of a field in a discriminated union");
          e
        end
      | Lval lv -> begin (* Reading an Lval *) 
          let accs = findTaggedFieldReads lv in
          (* Add a check instruction for each read access.*)
          self#queueInstr
            (List.map (fun (readtest, _) -> readtest) accs);
          self#queueInstr
            (checkDiscriminatedFieldAccess lv);
          e
      end
      | _ -> e
    in
    ChangeDoChildrenPost (e, postProcessExp)
          
  (* Add tag-manipulation code for reading and writing *)
  method vinst (i: instr) = 
    (* If true, a Call with this lvalue as the destination should be
     * rewritten into a set and a call *)
    let shouldRewriteCall lv : bool = 
      (containsTaggedFields lv)
      ||
      (match removeOffsetLval lv with 
         _, Field(f, _) -> H.mem discriminatorFields (f.fcomp.ckey, f.fname)
       | _ -> false)              
    in
    (* Postprocess the instructions to ensure that the tag checks for the 
     * reads are added first *)
    let postProcessInstr (i: instr) : instr = 
      (* Step 1. Writes to discriminated fields. *)
      (match i with 
        (* We are seeing a write *)
      | Call(Some lv, _, _, l) -> 
          (* Add checks for the access to discriminated fields *)
          self#queueInstr 
            (checkDiscriminatedFieldAccess lv);
          if shouldRewriteCall lv then 
            E.s (bug "shouldRewriteCall not handled correctly.")
      | Set(lv, rvalue, l) -> begin
          currentLoc := l;
          (* Add checks for the access to discriminated fields *)
          self#queueInstr 
            (checkDiscriminatedFieldAccess lv);
          (* Watch for writing of discriminators. Since a discriminator is of 
           * integer type, it is the last offset. *)
          (match removeOffsetLval lv with 
             lv', Field(f, _) -> begin
               let deps: fieldinfo list = 
                 H.find_all discriminatorFields (f.fcomp.ckey, f.fname)
               in
               if deps <> [] then
                 ignore (E.log "Setting the discriminator field %a, so clearing dependent fields: %a\n"
                           d_lval lv
                           (docList (fun f -> text f.fname))
                           deps);
               let alreadyHasTag = BinOp(Eq, Lval lv, rvalue, intType) in
               List.iter
                 (fun dep_field ->
                    let unionLval = 
                      addOffsetLval (Field(dep_field, NoOffset)) lv' in
                    self#queueInstr [Call(None,
		                          Lval (var initFieldFunc.svar),
		                          [alreadyHasTag;
                                           AddrOf unionLval;
                                           (SizeOfE (Lval unionLval))],
		                          !currentLoc)];
                    ())
                 deps;
               ()
             end
           | _ -> ());
          ()
        end
      | _ -> ());
      (* Step 2. Writes to tagged unions.  We can write to both kinds
         of union at once! *)
      match i with 
      | Call(Some lv, f, args , l) when containsTaggedFields lv ->
          E.s (bug "result of Call is stored in a tagged union.  Should have been handled earlier.")   (* See shouldRewriteCall *)
        (* We are seeing a write *)
      | Set(lv, rvalue, l) -> begin
          currentLoc := l;
          findTaggedFieldWrites (self :> cilVisitor) lv ~rvalue;
          i
        end
      | _ -> i
    in
    match i with 
      (***************************************************************)
      (** Code to implement ccured_hasuniontag()                     *)
      Call(result, Lval(Var f, NoOffset), [e], _) 
            when Poly.stripPoly f.vname = "ccured_hasuniontag"-> begin
        match result with 
	  None -> ChangeTo []  (*The result is ignored *)
	| Some reslv -> 
            (* Step 1. Process result as usual *)
	    let result' = visitCilLval (self :> cilVisitor) reslv in
	    match stripCasts e with
	      (* (Ignore the AddrOf; we only use it instead of the raw field
		 access so that this is a legal function call.) *)
	      AddrOf arglv -> begin
                (* Step 2. Process the argument to fix field accesses only.
                       Don't insert CHECK_UNIONTAG calls. *)
		ignoreAccesses <- true;
		let arglv' = visitCilLval (self :> cilVisitor) arglv in
		ignoreAccesses <- false;

		(* Step 3: Add a check instruction for each field access.
		       If there is more than one, AND the results together.*)
		let accs = findTaggedFieldReads arglv' in
		if accs = [] then
		  E.s (error "argument to ccured_hasuniontag is not a field of a tagged union.");
		let hasUnionTag = 
		  makeTempVar !MU.currentFunction 
                    ~name:"hasUnionTag" intType in
		let hasUnionTagTemp = 
		  makeTempVar !MU.currentFunction 
                    ~name:"hasUnionTagTemp" intType in
		(*  hasUnionTag := true; *)
		self#queueInstr
		  [Set(var hasUnionTag,one,!currentLoc)];
	        (*  for each (tagLval, tagValue) in accs do
		 *    hasUnionTag &= (tagLval == tagValue); *)
                List.iter
		  (fun (_, setifhastag) ->
                     self#queueInstr
                     [ (setifhastag (var hasUnionTagTemp));
		       Set(var hasUnionTag,
			   BinOp(BAnd,
				 Lval(var hasUnionTag),
				 Lval(var hasUnionTagTemp),
				 intType),
			   !currentLoc)])
		     accs;
		
		(* Step 4. Replace instr "result = CHECK_UNIONTAG(...)" with 
                            "result = hasUnionTag". *)
		let new_i = Set(result', Lval(var hasUnionTag),
				!currentLoc) in
		(* Step 5. Postprocess new_i as usual, in case
		   result' is itself a write to a union field. *)
		let new_i' = postProcessInstr new_i in
		ChangeTo [new_i']
	      end
	    | _ ->(* argument <> AddrOf *)
		E.s (bug "ccured_hasuniontag: expecting AddrOf, got %a"
		     d_exp e)
     end
     (** End ccured_hasuniontag *************************************)
      (* Look for writes to tagged union fields and discriminated union tags,
         and make these Set instrs so that postProcessInstr has an easier time
         with them. *)
    | Call(Some lv, f, args , l) when shouldRewriteCall lv ->
          (* Rewrite this into a call and set. *)
          currentLoc := l;
          let tmp = makeTempVar !MU.currentFunction
                      ~name:"calltmp" (typeOfLval lv) in
          let call = Call(Some (var tmp), f, args , l) in
          let set = Set(lv, Lval (var tmp), l) in
          self#queueInstr (visitCilInstr (self :> cilVisitor) call);
	  ChangeDoChildrenPost 
            ([set], fun il -> mapNoCopy postProcessInstr il)
    | _ ->
	ChangeDoChildrenPost ([i], fun il -> mapNoCopy postProcessInstr il)
          
  (* Process a global and add it to MU.theFile *)
  method vglob (g: global) : global list visitAction = 
    match g with
      GCompTag(comp, l) when not comp.cstruct && 
                             hasAttribute "tagged" comp.cattr 
      -> 
        ignore (E.log "%s will be tagged\n" comp.cname);
        (* Create a copy of the union *)
        let union_copy = 
          mkCompInfo false
            comp.cname
            (fun _ -> 
              List.map 
                (fun f -> 
                  (f.fname, f.ftype, f.fbitfield, f.fattr, f.floc))
                comp.cfields)
            comp.cattr
        in
        (* Add this to the file *)
        MU.theFile := GCompTag (union_copy, l) :: !MU.theFile;
        (* Now replace the union with a tag + old union *)
        comp.cstruct <- true;
        comp.cname <- "tagged_" ^ comp.cname;
        let tField = 
          { fcomp = comp; fname = "__tag"; ftype = MU.rttiType;
               fbitfield = None; fattr = []; floc = l } in
        let dField = 
          { fcomp = comp; fname = "__data"; ftype = TComp(union_copy, []);
               fbitfield = None; fattr = []; floc = l } in
        comp.cfields <- [ tField; dField ];

        MU.theFile := g :: !MU.theFile;
        List.iter
          (fun f -> 
             (* Add this field to the replacement map *)
             H.add taggedUnionFields 
             (comp.ckey, f.fname) 
             (Field(dField, Field(f, NoOffset))))
          union_copy.cfields;
        IH.add taggedUnionEmbeddings comp.ckey (tField, union_copy, l);

        SkipChildren

    | GCompTag (comp,l) when (not comp.cstruct
                                && hasAttribute "trustedunion" comp.cattr) 
      -> 
        ignore (E.warn "Will trust all accesses to %s\n" (compFullName comp));
        MU.theFile := g :: !MU.theFile;
        DoChildren
                          
    | GCompTag (comp,l) 
      when not comp.cstruct ->
        currentLoc := l;
        (** See if any of the fields have selectedwhen attribute. Give a 
         * warning if some but not all have it. *)
        let one_has = ref false in
        let all_have = ref true in
        List.iter (fun f -> 
          if hasAttribute "selectedwhen" f.fattr then
            one_has := true
          else
            all_have := false) comp.cfields;

        if !one_has && not !all_have then 
          ignore (warn 
                    "Some, but not all, fields of union %s have SELECTEDWHEN"
                    comp.cname);
        if not !all_have then begin
          MU.theFile := g :: !MU.theFile;
          DoChildren
        end else begin 
          (* Add an attribute to recognize this union later *)
          comp.cattr <- 
             addAttribute (Attr("discriminated_union", []))
               comp.cattr;
          
            
          List.iter 
            (fun f -> 
              H.add discriminatedUnionFields (f.fcomp.ckey, f.fname) ())
            comp.cfields;
          
          (* here we ought to check that the selectors are disjoint *)
          ignore (warn "We are not checking disjointness of selectors for %s yet" comp.cname);
          MU.theFile := g :: !MU.theFile;
          SkipChildren
        end

    | GCompTag (comp, l) when comp.cstruct -> 
        (* See if we have a field that is a discriminated union *)
        List.iter
          (fun comp_f -> 
            match unrollType comp_f.ftype with 
              TComp(u, _) when isDiscriminatedUnion u
              -> begin
                let allTags: string list ref = ref [] in
                List.iter
                  (fun u_f -> 
                     (* Pretend that we are accessing all fields of the union
                      * and obtain the list of discriminator fields. *)
                     let (discr: string list), _, _ = 
                       getDiscriminator 
                         (Mem (CastE(TPtr(TComp(comp, []), []), zero)), 
                          NoOffset)
                         u_f
                     in
                     List.iter 
                       (fun d -> if not (List.mem d !allTags) then
                          allTags := d::!allTags)
                       discr)
                  u.cfields;
                (* For each tag field, mark it as being a tag for the current
                   union. *)
                List.iter 
                  (fun (d:string) -> (* d is the name of a tag field in comp *)
                     H.add discriminatorFields 
                       (comp.ckey, d) comp_f)
                  !allTags
              end
            |  _ -> ())
          comp.cfields;

        MU.theFile := g :: !MU.theFile;
        DoChildren;

    | GFun(f, l) -> 
	MU.currentFunction := f; 
	ignoreAccesses <- false;
        MU.theFile := g :: !MU.theFile;
        DoChildren
    | _ -> 
        MU.theFile := g :: !MU.theFile;
        DoChildren
          
end

let tagForDataField inlv dfield: lval option =
  try
    (* Find the tagfield *)
    let tagField, _, _ = 
      IH.find taggedUnionEmbeddings dfield.fcomp.ckey in
    let tagLval =
      (addOffsetLval (Field(tagField, NoOffset)) inlv) in
    Some tagLval
  with Not_found -> 
    None


let processTaggedUnions (f: file) =
  (* On MSVC the checking functions are not declared static *)
(*   if not !msvcMode then begin *)
(*     checkUnionTag.svar.vstorage <- Extern; *)
(*     initFieldFunc.svar.vstorage <- Extern; *)
(*   end; *)
  (* MU.theFile := [GVarDecl(checkUnionTag.svar, locUnknown)]; *)
  if !MU.theFile <> [] then E.s (bug "MU.theFile in use.");
  let vis = new taggedUnionsVisitor in
  iterGlobals f (fun g -> ignore (visitCilGlobal vis g));

  (* Make initFieldFunc a poly function, since it takes a void* arg. *)
  let polyAttr = Attr("ccuredpoly", [AStr initFieldFunc.svar.vname]) in
  Poly.processPragma polyAttr;
  let polyAttr = Attr("ccuredpoly", [AStr rttiTagFor.svar.vname]) in
  Poly.processPragma polyAttr;
(*   let polyAttr = Attr("ccuredpoly", [AStr rttiCheck.svar.vname]) in *)
(*   Poly.processPragma polyAttr; *)

  (* theFile is populated by taggedUnionsVisitor::vglob *)
  f.globals <- List.rev !MU.theFile; 
  MU.theFile := [];
  ()
  

(* Call this after marking compinfos.  
   We need nodes to be created before we can add edges between union fields. *)
let processTaggedUnionsAfterMarking (f:file) = 
  IH.iter (fun i (_, union, l) -> 
             currentLoc := l;
             addEdgesToTaggedUnion union)
    taggedUnionEmbeddings;
  ()

(* At the end of solving, strip Rtti from the fields of tagged unions.
   RTTI info is stored separately, as the union's tag, so fields don't need
   the kind RTTI. *)
let removeRttiFromFields () : unit =
  IH.iter
    (fun _ (_, comp, _) ->
       List.iter
         (fun f -> match unrollType f.ftype with
            TPtr(_, a) -> begin
              match N.nodeOfAttrlist a with
                Some n -> n.N.kind <- N.stripRTTI n.N.kind
              | None -> E.s (bug "missing node for %a." d_type f.ftype)
            end
          | _ -> ())
       comp.cfields)
    taggedUnionEmbeddings


let init () = 
  H.clear discriminatedUnionFields;
  H.clear discriminatorFields;
  H.clear taggedUnionFields;
  IH.clear taggedUnionEmbeddings


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

