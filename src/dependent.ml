(** See the copyright notice at the end of this file *)

(** Handle the CCured dependent types *)
open Cil
open Pretty

module H = Hashtbl
module E = Errormsg

module N = Ptrnode

module MU = Markutil

let (=?) = Util.equals (* Comparison for cyclic structures. *)

let hasPointers (t: typ) : bool =
  existsType (function TPtr _ -> ExistsTrue | _ -> ExistsMaybe) t


(** Data structures for dependent types *)

(* For each field of a structure on which others depend (call this a meta
 * field) we remember which fields depend on it. Indexed on structure key and
 * the field name. *)
let metaFields: (int * string, fieldinfo) H.t = H.create 17


(** What kind of access are we checking *)
type access =
    ForAddrOf of exp ref (* Where to put the result *)
  | ForRead of exp ref  (* Where to put the result *)
  | ForWrite of exp      (* The thing to be written *)
  | ForCall of exp * exp list (* THe function and the arguments *)

(** Inputs: An access mode, an lval whose last offset is the dependent field,
 * an offset to the rest of the lval and an accumulated list of instructions *)
(** Results: Accumulate to "acc" in reverse order (cons to the front of acc)
 * the replacement instructions. For reads and for taking the address, the
 * result is put in the ref cell contained in the access. For write and
 * function call the result is part of the accumulated instructions. *)
(** Before the action is called all the expressions in the lval and the
 * offset have been processed. *)
type dependentAction = access -> lval -> offset -> instr list -> instr list

(** For each dependent field, keep a set of operations to be performed when
 * reading/writing or taking the address of a field. Indexed by structure key
 * and field name. *)
let dependentFields: (int * string, dependentAction) H.t = H.create 17


(** We need to watch for the prototypes of helper functions. These should all
 * be defined in ccuredannot.h which is forcefully included in all files *)
let helperFunctions: (string, varinfo option) H.t =
  let h = H.create 17 in
  List.iter (fun n -> H.add h n None)
    [ "__mkptr_size"; "__ptrof_size"; "__ptrof_nocheck";
    ];
  h

let setHelperFunction (v: varinfo) =
  try
    match H.find helperFunctions v.vname with
      None -> H.replace helperFunctions v.vname (Some v)
    | _ -> ()
  with Not_found -> ()

let getHelperFunction (vn: string) : varinfo =
  try
    match H.find helperFunctions vn with
      None -> E.s (error "Cannot find prototype for helper function %s" vn)
    | Some v -> v
  with Not_found ->
    E.s (bug "Dependent: %s is not a helper function" vn)


let isPointer e: bool =
  isPointerType (typeOf e)

(** The dependent types are expressed using attributes. We compile an
 * attribute given a mapping from names to lvals.  Returns the names of
 * meta values that this annotation depends on, and the expression.
 *
 * This is a helper for both fields and formals. *)
let compileAttribute
  (map: (string * exp) list) (* mapping from field/formal names to expressions
                              * representing the runtime value.
                              * Must include a mapping for ~this. *)
  ~(this: string)(* name of this field or formal. Used for the __this keyword*)
  (a: attrparam)
    : string list * exp =
  let rec compile (a: attrparam) =
    match a with
      AInt k -> [], integer k
    | ASizeOf t -> [], SizeOf t
    | ACons(name, []) -> begin (* This is a field access into the host *)
        let name' = if name = "__this" then this else name in
        try
          let e = List.assoc name' map in
          [name'], e
        with Not_found ->
          E.s (E.error
                 "Cannot compile the dependency %a: Cannot find %s.\n  Choices are: %a,__this."
                 d_attrparam a
                 name'
                 (docList (fun (s, _) -> text s)) map)
    end
    | ABinOp (bop, e1, e2) ->
        let lv1', e1' = compile e1 in
        let lv2', e2' = compile e2 in
        (* now that we know the types of these expressions,
           fix any MinusA/PlusA that should be pointer arithmetic. *)
        let bop' = match bop, isPointer e1', isPointer e2' with
            MinusA, true, true -> MinusPP
          | MinusA, true, false -> MinusPI
          | PlusA, true, false -> PlusPI
          | _ -> bop
        in
        lv1' @ lv2', BinOp(bop', e1', e2', intType)
    | _ -> E.s (E.error "Cannot compile the dependency %a" d_attrparam a)
  in
  compile a

(** The dependent types are expressed using attributes. We compile an
 * attribute based on a given host. Returns the names of meta values that
 * this annotation depends on, and the expression. *)
let compileFieldAttribute (thisField: fieldinfo)   (* The current field *)
                          ?(newValue: exp option)  (* If this is a write, what
                                                      is the new value of
                                                      thisField? *)
                          (a: attrparam)
                          (host: lval)
    : string list * exp =
  let hostcomp: compinfo =
    match unrollType (typeOfLval host) with
      TComp (comp, _) when comp.cstruct -> comp
    | _ -> E.s (error "The host for a dependent field access does not have a structure type")
  in
  if hostcomp != thisField.fcomp then
    E.s (bug "bad f / host in compileFieldAttribute.");
  let fieldMap : (string * exp) list =
    List.map (fun fi ->
                (* map this field name to the current value of this field
                   in the struct, for use when compiling references to this
                   field.
                   Exception: when doing a write, map thisField to the new
                   value instead of the current value. *)
                match newValue with
                  Some e when fi == thisField ->
                    fi.fname, e
                | _ ->
                    let lv = addOffsetLval (Field(fi, NoOffset)) host in
                    fi.fname, Lval lv)
      hostcomp.cfields
  in
  compileAttribute fieldMap ~this:thisField.fname a

(** Get the meta fields on which a field depends *)
let markDependencies (f: fieldinfo) (a: attrparam) : unit =
  (* Compile the parameter, just to get its dependencies *)
  let host = f.fcomp in
  let (metas: string list), _ =
    compileFieldAttribute f a
      (Mem (CastE(TPtr(TComp(host, []), []), zero)), NoOffset)
  in
  List.iter (fun (meta: string) ->
               H.add metaFields (host.ckey, meta) f)
    metas


(** This function is used to process a dependent field access. See comments
 * for {!Dependent.dependentAction} *)
let rec processDependentFieldAccess
    (why: access)
    (lval_to_here: lval)
    (off: offset)
    (instr_to_here: instr list)
    : instr list =
  match off with
  | Index (e, resto) ->
      processDependentFieldAccess
        why
        (addOffsetLval (Index(e, NoOffset)) lval_to_here)
        resto
        instr_to_here

  | NoOffset -> begin (* We are done. We must generate the instruction if
                       * needed *)
      match why with
        ForWrite e -> (Set(lval_to_here, e, !currentLoc)) :: instr_to_here
      | ForCall (func, args) ->
          (Call(Some lval_to_here, func, args, !currentLoc)) :: instr_to_here
      | ForRead pexp -> pexp := Lval (lval_to_here);
                        instr_to_here
      | ForAddrOf pexp -> begin
          pexp :=
            (match unrollType (typeOfLval lval_to_here) with
              TArray _ -> StartOf lval_to_here
            | _ -> AddrOf lval_to_here);
          instr_to_here
      end
  end

  | Field(dfield, resto) -> begin
      let lval_to_here' =
        addOffsetLval (Field(dfield, NoOffset)) lval_to_here in
      try
        let action: dependentAction =
          H.find dependentFields (dfield.fcomp.ckey, dfield.fname)
        in
        (* We have an action for it. Let's process it *)
        action why lval_to_here' resto instr_to_here
      with Not_found -> begin
        (* Not a dependent field. But perhaps it is a meta field and we are
         * taking the address. That's a NO NO *)
        (* But this should actually have been caught earlier. *)
(*         if (match why with ForAddrOf _ -> true | _ -> false) && *)
(*            H.mem metaFields (dfield.fcomp.ckey, dfield.fname) then  *)
(*           ignore (bug "Taking the address of meta field %s of %s\n" *)
(*                     dfield.fname dfield.fcomp.cname); *)
        processDependentFieldAccess why lval_to_here' resto instr_to_here
      end
  end

let processLval (why: access) (lv: lval) (acc: instr list) : instr list =
  let (h, off) = lv in
  processDependentFieldAccess why (h, NoOffset) off acc


(**** SIZE and COUNT ****)
let processSizeFieldAttribute (f: fieldinfo) (a: attrparam) : unit =
  let comp = f.fcomp in
  if not comp.cstruct then
    ignore (warn "Size dependency on a union field");
  if H.mem dependentFields (f.fcomp.ckey, f.fname) then
    E.s (error "Field %s has duplicate SIZE/COUNT attributes" f.fname);
  (* This must be pointer field *)
  match unrollType f.ftype with
    TPtr _ -> begin (* This is a pointer field *)
      markDependencies f a; (* Remember the dependencies *)
      let action (why: access) (lv: lval) (resto: offset) (acc: instr list)
          : instr list =
        if resto <> NoOffset then
          E.s (error "Dependent size for field that is not a pointer type");
        let hostlv, _ = removeOffsetLval lv in
        match why with
          ForAddrOf _ ->
            E.s (error "Taking the address of dependent pointer field %s"
                   f.fname)
        | ForRead _ ->
            let _, sz = compileFieldAttribute f a hostlv in
            let mkptr_size: varinfo = getHelperFunction "__mkptr_size" in
            let res: varinfo =
              makeTempVar !MU.currentFunction ~name:(f.fname ^ "_withsize")
                f.ftype in
            processDependentFieldAccess why (var res) resto
              (Call (Some (var res), Lval (var mkptr_size),
                     [ Lval lv; sz ], !currentLoc) :: acc)

        | ForWrite e ->
            (* When compiling the attribute, use ~newValue to specify
               the new value of field f.  Alternately, we could write the field
               first, and use some kind of "__check_size" helper. *)
            let _, sz = compileFieldAttribute f ~newValue:e a hostlv in
            let ptrof_size: varinfo = getHelperFunction "__ptrof_size" in
            (* We've done the write. We are done *)
            (Call (Some lv, Lval (var ptrof_size),
                   [ e; sz ], !currentLoc)) :: acc

        | ForCall (func, args) ->
            let ptrof_size: varinfo = getHelperFunction "__ptrof_size" in
            (* Make a new temp for the actual call *)
            let res: varinfo =
              makeTempVar !MU.currentFunction ~name:(f.fname ^ "_withsize")
                f.ftype in
            let _, sz = compileFieldAttribute f ~newValue:(Lval (var res))
                          a hostlv in
            (* We've done the call *)
            (Call (Some lv, Lval (var ptrof_size),
                   [ Lval (var res); sz ], !currentLoc)) ::
            (Call (Some (var res), func, args, !currentLoc)) ::
            acc
      in
      H.add dependentFields (f.fcomp.ckey, f.fname) action
    end

  | TArray(bt, leno, aa) -> begin
      (** SIZE attribute on an array field. This means that the array is at
       * least that long. This must be the last field. *)
      (match List.rev f.fcomp.cfields with
        f' :: _ when f == f' -> ()
      | _ -> E.s (error "You are using \"size\" attribute on the array field %s that is not last in structure %s" f.fname comp.cname));
      (* Get the minimum length of the array *)
      let _min =
        match leno with
          Some min -> min
        | None -> (* Change the type of the field *)
            f.ftype <- TArray(bt, Some zero, aa);
            zero
      in
      markDependencies f a; (* Remember the dependencies *)

      let action (why: access) (lv: lval) (resto: offset) (acc: instr list)
          : instr list =
        let hostlv, lasto = removeOffsetLval lv in
        (* Turn array into a SEQ pointer *)
        let mkptr_size: varinfo = getHelperFunction "__mkptr_size" in
        let res: varinfo =
          makeTempVar !MU.currentFunction ~name:(f.fname ^ "_withsize")
            (TPtr(bt, [])) in
        let _, sz = compileFieldAttribute f a hostlv in
        (* We have to adjust the remaining offset because wer are turning the
         * array into a pointer. *)
        let rest_lv, rest_off =
          match resto with
            Index(e, resto1) -> (Mem (BinOp(IndexPI, Lval (var res),
                                            e, res.vtype)), NoOffset),
                                resto1
          | NoOffset -> (* Perhaps we are taking the address. *)
              (Mem (Lval (var res)), NoOffset), NoOffset

          | _ -> E.s (unimp "Dependent.Unexpected offset: %a.\n"
                        (d_offset nil) resto)
        in
        (* For some strange reason we cannot just use StartOf lv to refer to
         * the start of the array, because that is a FSEQ pointer. We must
         * use a __ptrof instead *)
        let res2: varinfo =
          makeTempVar !MU.currentFunction ~name:(f.fname ^ "_arraystart")
            (TPtr(bt, [])) in
        let acc2 =
          (Call(Some (var res2),
                Lval (var (getHelperFunction "__ptrof_nocheck")),
                [ StartOf lv ], !currentLoc)) :: acc in
        let acc3 =
          (Call (Some (var res), Lval (var mkptr_size),
                 [ Lval (var res2);
                   sz ], !currentLoc) :: acc2)
        in
        match why with
        | ForAddrOf _ ->
            processDependentFieldAccess why rest_lv rest_off acc3

        | ForCall _ | ForRead _ | ForWrite _ ->
            processDependentFieldAccess why rest_lv rest_off acc3
      in
      H.add dependentFields (f.fcomp.ckey, f.fname) action
    end

   | _ -> E.s (error "You cannot use the \"size\" dependency on non-pointer and non-array field %s" f.fname)

let metaFieldAction (mf:fieldinfo) (allDepFields: fieldinfo list)
  (why: access) (lv: lval) (resto: offset) (acc: instr list) : instr list =
  let _comp = mf.fcomp in
  if resto <> NoOffset then
    E.s (error "Compound type for metadata field");
  let hostlv, _ = removeOffsetLval lv in
  match why with
    ForAddrOf _ ->
      E.s (error "Taking the address of metadata field %s"
             mf.fname)
  | ForRead _ -> (* Nothing to do *)
      processDependentFieldAccess why lv resto acc
  | ForWrite _
  | ForCall _ ->
      (* We're writing to the metadata field, so zero any fields that
         depend on this one. *)
      List.fold_left
      (fun acc1 f ->
         match unrollType f.ftype with
           TPtr _ ->
             let lvf = addOffsetLval (Field(f, NoOffset)) hostlv in
             let null = mkCast ~e:zero ~newt:(typeOfLval lvf) in
             let instr = Set(lvf, null, !currentLoc) in
             processDependentFieldAccess why lv resto (instr::acc1)
         | TArray _ ->
             (* FIXME: we should check that the value being written
                is correct. *)
             ignore (warn "Unimplemented: We need to check that the write to this field, which an open array depends on, is safe.\n");
             (* Do nothing. *)
             processDependentFieldAccess why lv resto acc
         | _ ->
             E.s (bug
                    "field %s has dependencies but is not a pointer or array."
                    f.fname)
      )
      acc
      allDepFields

let hasSizeAttr attrs =
  hasAttribute "size" attrs || hasAttribute "count" attrs

(* Move "size" and "count" attributes from an attribute list to a type.
   Returns a list of the attributes other than size and count,
    and the new type.   *)
let moveSizeCountAttrs (a: attributes) (t:typ) : (attributes * typ) =
  let size = filterAttributes "size" a in
  let count = filterAttributes "count" a in
  let a'  = dropAttribute "size" a in
  let a'' = dropAttribute "count" a' in
  let t' = typeAddAttributes (size@count) t in
  a'', t'

(** If there is a __SIZE, call doit on the arg.
    If there is a __COUNT attribute, convert it to SIZE and then call doit.
    Otherwise, return default *)
let rec readAttrs ~(doit: attrparam -> 'a) ~(default: 'a) (t:typ) : 'a =
  let rec loop (a: attributes): 'a =
    let checkrest rest =
      if hasSizeAttr rest then
        E.s (error "Field/formal has duplicate SIZE/COUNT attributes")
    in
    match a with
      Attr("size", [a])::rest ->
        checkrest rest;
        doit a
    | Attr("count", [a])::rest ->
        checkrest rest;
        (* We are counting the size of the element pointed to. We need to
         * compute the sizeof in such a way that we share the pointer kinds
         * with the field itself. *)
        let sz =
          match unrollType t with
            TPtr (bt, _) -> ASizeOf bt
          | TArray(bt, _, _) -> ASizeOf bt
          | _ -> E.s (error "Using \"count\" attribute on something that's not a pointer")
        in
        let a' = ABinOp(Mult, a, sz) in
        doit a'
    | [] -> (* no SIZE/COUNT annotations. Keep the old formal *)
        default
    | (Attr _)::rest -> loop rest
  in
  loop (typeAttrs t)


(** Process a composite type *)
let processComp (comp: compinfo) : unit =
  List.iter
    (fun f ->
       (* If there are any SIZE/COUNT attributes on the field, move them
          to the type. *)
       if hasSizeAttr (f.fattr) then begin
         let a', t' = moveSizeCountAttrs f.fattr f.ftype in
         f.ftype <- t';
         f.fattr <- a';
       end;
       (* Now process the attributes on the type *)
       readAttrs ~doit:(processSizeFieldAttribute f) ~default:() f.ftype)
    comp.cfields;
  (* Now all of the dependent fields have actions associated with them,
     and the metaFields table has been populated.
     Add actions for writes to meta fields in this struct. *)
  List.iter
    (fun mf ->
       if H.mem metaFields (comp.ckey, mf.fname) then begin
         let allDepFields = H.find_all metaFields (comp.ckey, mf.fname) in
         if H.mem dependentFields (comp.ckey, mf.fname) then begin
           (* Others depend on this field, and this field depends on others *)
           if allDepFields =? [mf] then
             (* This field depends only on itself (via __END, probably).
                For both reads and writes, we use the action already in
                dependentFields. For example, if this is a write, we do not
                need to do the usual "zero everyone who depends on this field",
                since this field is being written anyways.
             *)
             ()
           else
             (* This field depends on something other than itself *)
             (* This is a problem because the metaFieldAction we should add to
                dependentFields conflicts with the action that's already in
                dependentFields.  If you want to support this kind of
                dependency, you'll need code to compose actions, and also to
                be careful of the ref cell in ForRead. *)
             E.s (unimp "Field %s in struct %s has a SIZE/COUNT annotation, but  other fields depend on it.  This is not allowed, except for self-dependencies using  __END or __this.\n" mf.fname comp.cname);
         end
         else begin
           (* Others depend on this field, but this field depends on no one.
              This is the "normal" metadata case.
              Just create an action that will clear all of the dependent fields
              when this field is written. *)
           let action = metaFieldAction mf allDepFields in
           H.add dependentFields (comp.ckey, mf.fname) action
         end
       end)
    comp.cfields;
  ()





let dependentVisitor : cilVisitor = object (self)
  inherit nopCilVisitor

  (* Check that we are not taking the address of such a field *)
  method vexpr (e: exp) =
    (* Process the expression first *)
    let postProcessExp (e: exp) : exp =
      match e with
        AddrOf lv | StartOf lv -> begin
          let res = ref e in
          let il' = processLval (ForAddrOf res) lv [] in
          self#queueInstr (List.rev il');
          !res
        end
      | Lval lv -> begin (* Reading an Lval *)
          let res = ref e in
          let il' = processLval (ForRead res) lv [] in
          self#queueInstr (List.rev il');
          !res
      end
      | _ -> e
    in
    (* FIXME: Don't process expressions inside of sizeof.
       but markptr also needs to be updated.*)
(*     match e with *)
(*       SizeOf _ | SizeOfE _ | SizeOfStr _ *)
(*     | AlignOf _ | AlignOfE _ -> *)
(*         SkipChildren *)
(*     | _ -> *)
    ChangeDoChildrenPost (e, postProcessExp)

  (* Add tag-manipulation code for reading and writing *)
  method vinst (i: instr) =
    (* Postprocess the instructions to ensure that the tag checks for the
     * reads are added first *)
    let postProcessInstr (acc: instr list) (i: instr) : instr list =
      match i with
        (* We are seeing a write *)
        Set(lv, e, l) -> begin
          currentLoc := l;
          (* Add checks for the access to discriminated fields *)
          processLval (ForWrite e) lv acc
        end
      | Call (Some lv, f, args, l) ->
          currentLoc := l;
          (* Add checks for the access to discriminated fields *)
          processLval (ForCall (f, args)) lv acc

      | _ -> i :: acc
    in
    match i with
    | _ ->
	ChangeDoChildrenPost
          ([i],
           fun il ->
             List.rev (List.fold_left postProcessInstr [] il))

  (* Process a global and add it to MU.theFile *)
  method vglob (g: global) : global list visitAction =
    match g with

    | GCompTag (comp, l) ->
        currentLoc := l;
        processComp comp;
        DoChildren;

    | GVarDecl(v, l) -> (* Look for the declarations of the functions we need*)
        setHelperFunction v;
        DoChildren

    | GFun(f, l) ->
	MU.currentFunction := f;
        DoChildren

    | _ ->
        DoChildren

end


let init () =
  H.clear metaFields;
  H.clear dependentFields;
  ()

let doit (f: file) =
  init ();
  iterGlobals f (fun g -> ignore (visitCilGlobal dependentVisitor g));
  if not !MU.doAnnotateOutput then init ();
  ()


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
