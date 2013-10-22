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

(** Preprocess a C++ file before Curing. This happens in several passes over
 * the file. *)
open Cil
open Formatcil
open Pretty
open Trace
module E = Errormsg
module H = Hashtbl

let fixUpcasts = true
let fixDowncasts = true
let fixDowncastsMI = true
let fixPtrMemFun = true
let fixPtrMemData = true
let fixVCall = true
let checkVMLookup = true

let fixBaseClassTables = true

let debugPtrMem = false

let doDumpClasses = ref false

let currentFunction : fundec ref = ref dummyFunDec

let theFile : global list ref = ref []
let theFileAfter: global list ref = ref []

let pushGlobal (g: global) = theFile := g :: !theFile

let prefix p s =
  let pl = String.length p in
  pl <= String.length s && String.sub s 0 pl = p

(* Drop all the casts *)
let rec dropCasts = function
    CastE (t, e) -> dropCasts e
  | e -> e



let rec revonto (acc: 'a list) = function
    [] -> acc
  | h::t -> revonto (h::acc) t

(* Whether we have a mangling of a NEW function *)
let isNew (n: string) =
  prefix "__nw" n

(* whether is new[]; implies isNew *)
let isNewArray (n: string) : bool =
  prefix "__nwa" n

(* Whether we have a mangling of a DELETE function *)
let isDelete (n: string) =
  prefix "__dl" n

(* A function to make new names for structures *)
let nameCounters: (string, int ref) H.t = H.create 17
let newName (base: string) =
  let counter =
    try H.find nameCounters base
    with Not_found -> begin
      let res = ref 0 in
      H.add nameCounters base res;
      res
    end
  in
  let res = if !counter = 0 then base else base ^ string_of_int !counter in
  incr counter;
  res

(* make a function type *)
let funType (ret_t: typ)
            (args: (string * typ) list)
            (isva: bool) =
  TFun(ret_t,
       Some (List.map (fun (n,t) -> (n, t, [])) args),
       isva, [])

(* Set a function as polymorphic *)
let setFunctionPoly (n: string) (l: location) =
  pushGlobal (GPragma(Attr("ccuredpoly", [ AStr n ]), l))



(**** NAME DEMANGLING **************)


        (* Skip a prefix consisting of _ and digits. Return None if the name
         * is only _ and digits or the index of the first character that is
         * neither a digit nor _. *)
let rec skipPrefix (n: string) (i: int) : int option =
  let nl = String.length n in
  if i >= nl then None
  else
    let c = String.get n i in
    if c = '_' || (c >= '0' && c <= '9') then
      skipPrefix n (i + 1)
    else
      Some i

(** Skip some digits. Returns the index after the digits and the integer
 * value of the skipped digits. Returns None if no digits were found *)
let skipDigits ((s, l): string * int) (start: int) : (int * int) option =
  let rec loop (i: int) =
    if i >= l then i else
    let c = String.get s i in
    if c >= '0' && c <= '9' then
      loop (i + 1)
    else
      i
  in
  let after = loop start in
  if after = start then None else
  Some (after, int_of_string (String.sub s start (after - start)))


(* If the string needs uncompressing, return the uncompressed string,
 * otherwise return the original *)
let uncompressName (s: string) : string =
  let l = String.length s in
  let debugUncompress = false in
  if debugUncompress then
    ignore (E.log "uncompress: %s\n" s);
  if l < 6 || String.sub s 0 5 <> "__CPR" then begin
    if debugUncompress then
      ignore (E.log "  no __CPR prefix\n");
    s (* Return the original *)
  end else begin
    (* Grab the length of the original *)
    try
      let startOrig, lenOrig =
        match skipDigits (s, l) 5 with
          Some (startOrig, lenOrig) -> startOrig, lenOrig
        | _ ->
            ignore (warn "Cannot find original length in __CPR: %s" s);
            raise Not_found
      in
      if debugUncompress then
        ignore (E.log "  startOrig=%d, lenOrig=%d\n" startOrig lenOrig);
      (* We skip two more _ *)
      if startOrig + 2 >= l || String.sub s startOrig 2 <> "__" then begin
        ignore (warn "Expecting __ after the _CPRnnn in %s\n" s);
        raise Not_found
      end;

      (* Create the original *)
      let orig = String.create lenOrig in
      (* Now loop, looking for JnnnJ in the string. Each such construct
       * denotes a substring that appears at position nnn in the original
       * string *)
      let rec loop (orig_idx: int) (idx: int) =
        if idx >= l then begin
          (* We are done *)
          if orig_idx <> lenOrig then begin
            ignore (warn "Result of uncompress is %d char long and I expected to be %d\n" orig_idx lenOrig);
          end;
          ()
        end else begin
          if orig_idx >= lenOrig then begin
            ignore (warn "The uncompressed string is too large\n");
            raise Not_found
          end;
          let c = String.get s idx in
          if c <> 'J' then begin
            orig.[orig_idx] <- c;
            loop (orig_idx + 1) (idx + 1)
          end else begin
            (* Now we have found a J *)
            if idx >= l then begin
              ignore (warn "J alone at the end of__CPR: %s" s);
              raise Not_found
            end;
            if String.get s (idx + 1) = 'J' then begin
              (* Two consecutive J means one J in the original *)
              orig.[orig_idx] <- 'J';
              loop (orig_idx + 1) (idx + 2)
            end else
              if debugUncompress then
                ignore (E.log "  found JnnnJ at index %d\n" (idx + 1));
              let (idx', posOrigSubstring) =
                match skipDigits (s, l) (idx + 1) with
                  None ->
                    ignore (warn "Expecting number after J in __CPR: %s" s);
                    raise Not_found
                | Some (after, nr) ->
                    (* Make sure we have a J following *)
                    if after >= l || String.get s after <> 'J' then begin
                      ignore (warn "Expecting J after number in __CPR: %s" s);
                      raise Not_found
                    end;
                    (after + 1, nr)
              in
              if debugUncompress then
                ignore (E.log "  nnn=%d\n" posOrigSubstring);
              (* Now we must go and fetch the string at index "nnn" in the
               * original. We must find a number there, which tells us how
               * much to copy. *)
              let posOrigSubstring', lenOrigSubstring =
                match skipDigits (orig, lenOrig) posOrigSubstring with
                  None ->
                    ignore (warn "Expecting number in the orginal substring in __CPR: %s" s);
                    raise Not_found
                | Some (i, n) -> i, n
              in
              (* Copy also the length *)
              let toCopy =
                lenOrigSubstring + posOrigSubstring' - posOrigSubstring in
              if posOrigSubstring + toCopy > orig_idx then begin
                ignore (warn "Original substring is too long");
                raise Not_found
              end;
              (* Now copy the substring over. Copy also the length digits *)
              String.blit orig posOrigSubstring
                          orig orig_idx toCopy;
              loop (orig_idx + toCopy) idx'
          end
        end
      in
      loop 0 (startOrig + 2);
      if debugUncompress then
        ignore (E.log "  RES=%s\n" orig);
      orig

    with Invalid_argument a ->
      ignore (warn "uncompress: Invalid argument(%s) in %s" a s);
      s
    | Not_found -> s
  end


(** Decode a virtual table name. Return the last component, which should be
 * the name of the class to which this belongs *)
let decodeVtblName (n: string) : string =
  try
    (* Strip any ___ddd suffix *)
    let n =
      if Str.string_match
          (Str.regexp "^\\(.+\\)___[0-9]+$") n 0 then
          Str.matched_group 1 n
        else
          n
    in
    (* Now uncompress *)
    let n = uncompressName n in
    let nl = String.length n in
    if not (prefix "__vtbl__" n) then begin
      (* We ignore for now the names that start with __STV____vtbl *)
      if not (prefix "__STV__" n) then
        ignore (warn "Invalid name for vtbl: %s\n" n);
      raise Not_found
    end;
    (* Return the index of the next non-digit *)
    let rec skipDigits (idx: int) : int =
      if idx >= nl then idx else
      let c = String.get n idx in
      if c >= '0' && c <= '9' then skipDigits (idx + 1) else idx
    in
    (* Return the next class name and an index past it *)
    let skipClassName (idx: int) : string * int =
      let idx' = skipDigits idx in
      if idx' >= nl then begin
        ignore (warn "Cannot find length of classname in %s (idx=%d)\n" n idx);
        raise Not_found
      end;
      if idx' = idx then begin
        (* If we see a 'Q' then we might be looking at a class name without a
         * length. It goes to the end *)
        if String.get n idx = 'Q' then
          (* Grab the __ as well *)
          String.sub n (idx - 2) (nl - idx + 2), nl
        else begin
          ignore (warn "Cannot find length of classname in %s (idx=%d)\n" n idx);
          raise Not_found
        end
      end else begin
        (* Get the length of the class name *)
        let cn_len = int_of_string (String.sub n idx (idx' - idx)) in
        if idx' + cn_len > nl then begin
          ignore (warn "Classname length %d is too large in %s\n"
                    cn_len n);
          raise Not_found
        end;
        (* Get the class name *)
        String.sub n idx' cn_len, idx' + cn_len
      end
    in
    (* Now loop over the class names *)
    let rec loop (last: string) (idx: int) : string =
      (* See if we are done *)
      if idx = nl then last
      else begin
        (* We must have a __ here *)
        if idx + 2 >= nl || String.sub n idx 2 <> "__" then  begin
          ignore (warn "Expecting __ at index %d in %s\n" idx n);
          raise Not_found
        end;
        (* If we have 'A' after wards then we have an alias *)
        if String.get n (idx + 2) = 'A' then begin
          (* After A we have a bunch of digits and then we restart *)
          let afterA = skipDigits (idx + 3) in
          loop last afterA
        end else begin
          (* Otherwise we must have a class name *)
          let newc, afterc = skipClassName (idx + 2) in
          loop newc afterc
        end
      end
    in
    (* We start looking immediately after __vtbl *)
    let res = loop "" 6 in
    if res = "" then
      ignore (warn "Could not find a class name in vtbl %s\n" n);
    res
  with Not_found ->
    "" (* An empty class name *)

(* Remember the TYPEINFO compinf *)

let downCastFun: fundec =
  let fdec = emptyFunction "__downcast" in
  (* Will fill in the type once we find VTABLE_ENTRY and TYPEINFO *)
  fdec.svar.vtype <- voidType;
  fdec



(* Remember every time when we set a vt_entry in preparation for a virtual
 * call *)
let vt_entries: (string,
                     (  varinfo * (* the vt_entry that is set*)
                        lval * (* the object from which it is set *)
                        exp * (* the obj->__vptr field *)
                        int (* the offset *) )) H.t = H.create 17


(* Create a prototype for the virtual method lookup function *)
let vmLookupFun =
  let fdec = emptyFunction "__vmLookup" in
  fdec.svar.vtype <- voidType; (* We'll fix the type later *)
  fdec

let checkVMTableEntry =
  mkCompInfo true "__checkVMTableEntry"
    (fun self ->
      [ ("over", TInt(IULong, []), None, [], locUnknown);
        ("parentidx", intType, None, [], locUnknown);
        ("parent", TInt(IULong, []), None, [], locUnknown) ])
    []

let checkVMTable =
  makeGlobalVar "__checkVMTable"
    (TArray(TComp(checkVMTableEntry, []),
            Some (integer 1), []))

(* We keep a hash of all methods in the overriding graph. For each node we
 * keep: the varinfo, the edges to the overriden methods, and the index (when
 * computed) *)
let checkVMTableNodes: (string, (varinfo * string list ref * int ref)) H.t = H.create 517

let addCheckVMTableEntry (overriding: varinfo) (parent: varinfo) =
  (* Add the parent if not already there *)
  if not (H.mem checkVMTableNodes parent.vname) then begin
    H.add checkVMTableNodes parent.vname (parent, ref [], ref (-1))
  end;
  (* Now add the child and the edge *)
  (try
    let (_, parents, _) = H.find checkVMTableNodes overriding.vname in
    if not (List.exists (fun p -> p = parent.vname) !parents) then
      parents := parent.vname :: !parents
  with Not_found ->
    H.add checkVMTableNodes overriding.vname (overriding,
                                              ref [ parent.vname ], ref (-1)))


let initCheckVMTable () =
  H.clear checkVMTableNodes


(** This function is called to produce the table encoding the overriding
 * graph *)
let packCheckVMTable () : global =
  (* Now process the graph to find for each node its immediate neighbor *)
  trace "vtable" (dprintf "Simplifying the override graph\n");
  (* First a function to check if a method overrides another. Watch out for
   * infinite loops (should not happen but we've seen them happening) *)
  let rec overridesRec (alreadySeen: string list)
                       (over: string) (overriden: string) =
    if over = overriden then
      true
    else
      try
        (* Check that we are not looping *)
        if List.exists (fun seen -> seen = over) alreadySeen then begin
          ignore (E.warn "Looping in packCheckVMTable for %s" over);
          false
        end else begin
          let (_, parents, _) = H.find checkVMTableNodes over in
          List.exists (fun p -> overridesRec (over :: alreadySeen)
                                             p overriden) !parents
        end
      with Not_found ->
        E.s (bug "Node %s is not in the override tree\n" over)
  in
  let overrides (over: string) (overriden: string) =
    overridesRec [] over overriden
  in
  (* Process the nodes one at a time and reduce the set of parents to the
   * minimal set such that all previous parents can be reached by
   * transitivity *)
  (trace "vtable" (dprintf "minimizing parent sets\n"));
  H.iter
    (fun _ (vi, parents, _) -> (
      let d_string () (s:string) : doc = (text s) in
      (*(trace "minparent" (dprintf "minimizing parents of %s@!  currently: %a\n"*)
      (*                            vi.vname  (d_list ", " d_string) !parents));*)
      parents :=
         (List.fold_left
           (fun sofar p ->
             (* Find out if p overrides anything in sofar (in that case it
             * replaces it), or if anything in sofar overrides p *)
             let rec loop = function
                 [] -> [ p ] (* Add p to the list *)
               | h :: rest ->
                   if overrides h p then
                     h :: rest (* We are done *)
                   else if overrides p h then
                     loop rest (* maybe p overrides more parents *)
                   else
                     h :: loop rest (* keep both p and h *)
             in
             loop sofar)
           []
           !parents
         )
    ))
    checkVMTableNodes;
  (* Now assign indices to the nodes *)
  (trace "vtable" (dprintf "assigning indices to nodes\n"));
  let idx = ref 0 in
  H.iter
    (fun _ (vi, parents, pidx) ->
      pidx := !idx; (* Set the index *)
      match !parents with
        [ ] -> incr idx (* A root. One entry *)
      | _ -> idx := !idx + List.length !parents (* As many entries as there
                                                 * are parents *)
    )
    checkVMTableNodes;
  (* Now scan the table in the same order and create the list of entries. We
   * hope that this time we scan the entries in exactly the same order as
   * before. We construct the entries in reverse order. *)
  (trace "vtable" (dprintf "scanning table to create list of entries\n"));
  let entries : (exp * int * exp) list ref = ref [] in
  H.iter
    (fun _ (vi, parents, pidx) ->
      match !parents with
        [] -> (* A root, one entry *)
          entries :=
             (mkCast (mkAddrOf (var vi)) !upointType,
              -1,
              mkCast zero !upointType) :: !entries
      | _ -> (* non-root, as many entries as there are parents *)
          entries :=
             List.fold_left
               (fun e p ->
                 (* Lookup the parent *)
                 let p_var, _, p_idx  =
                   try H.find checkVMTableNodes p
                   with Not_found ->
                     E.s (bug "Node %s is not in the override tree\n" p)
                 in
                 (mkCast (mkAddrOf (var vi)) !upointType,
                  !p_idx,
                  mkCast (mkAddrOf (var p_var)) !upointType) :: e)
               !entries
               !parents)
    checkVMTableNodes;
  (* Now put the final NULL entry in *)
  entries := (zero, -1, zero) :: !entries;
  (* Set the type of the table. Do it this late because only now we know the
   * length of the array. *)
  checkVMTable.vtype <-
     TArray(TComp(checkVMTableEntry, []),
            Some (integer (1 + !idx)),
            []);
  (* Generate the initializer list. Remember that "entries" is in reverse *)
  (trace "vtable" (dprintf "generating initializer list\n"));
  let initList =
    (* Get the fields *)
    let fover, fparentidx, fparent =
      match checkVMTableEntry.cfields with
        fover :: fparentidx :: fparent :: _ -> fover, fparentidx, fparent
      | _ -> E.s (bug "packCheckVMTable")
    in
    List.fold_left
      (fun acc (vaddr, parent_idx, parent_addr) ->
        decr idx;
        (Index(integer (1 + !idx), NoOffset),
         CompoundInit (TComp(checkVMTableEntry, []),
                       [ (Field(fover, NoOffset), SingleInit vaddr);
                         (Field(fparentidx, NoOffset),
                          SingleInit (integer parent_idx));
                         (Field(fparent, NoOffset), SingleInit parent_addr)
                       ])) :: acc)
      []
      !entries
  in
  let res =
    GVar (checkVMTable,
          {init = Some (CompoundInit (checkVMTable.vtype, initList))},
          locUnknown) in

  (trace "vtable" (dprintf "finishing up passCheckVMTable\n"));
  initCheckVMTable (); (* Clear up the table *)
  res



(* Create a prototype for the ptmLookup *)
let ptmLookupFun =
  let fdec = emptyFunction "__ptmLookup" in
  fdec.svar.vtype <- voidType; (* We'll fix the type later *)
  fdec

(* Create a prototype for the ptmLookup *)
let ptmLookupData =
  let fdec = emptyFunction "__ptmLookupData" in
  fdec.svar.vtype <-
     funType voidPtrType
       [ ("this", voidPtrType);
         ("ptm", uintType) ] false;
  fdec

let trustedCastFun =
  let fdec = emptyFunction "__trusted_cast" in
  fdec.svar.vtype <-
     funType
       voidPtrType
       [ ("x", voidPtrType); ]
       false;
  fdec

(** Replace the reference to the eh.variant.function with a function call *)

(* For each eh_stack_entry variable remember the temporary that stores the
 * pointer to the FunctionBlock variant *)
let eh_variant_function: (string, varinfo) H.t = H.create 5
let getEhVariantFunctionFun : fundec =
  let fdec = emptyFunction "__getEhVariantFunctionP" in
  (* Will set its type when we encounter the definition of the union *)
  fdec.svar.vtype <- voidType;
  fdec

let setupEhVariantFunctionPointer (eh: varinfo) (l: location)
    : varinfo * instr list =
  try
    H.find eh_variant_function eh.vname, []
  with Not_found -> begin
    let tmpptrtype, _, _, _ =
      splitFunctionTypeVI getEhVariantFunctionFun.svar
    in
    (* Make a temporary to hold the pointer *)
    let tmp =
      makeTempVar !currentFunction
        ~name:(eh.vname ^ "_variant_function")
        tmpptrtype in
    H.add eh_variant_function eh.vname tmp;
    tmp, [Call(Some (var tmp),
               (Lval (var getEhVariantFunctionFun.svar)),
               [ mkAddrOf (var eh) ], l) ]
  end

(** Replace the reference to the eh.variant.throw_spec with a function call *)
(* For each eh_stack_entry variable remember the temporary that stores the
 * pointer to the FunctionBlock variant *)
let eh_variant_throw_spec: (string, varinfo) H.t = H.create 5
let getEhVariantThrowSpecFun : fundec =
  let fdec = emptyFunction "__getEhVariantThrowSpecP" in
  (* Will set its type when we encounter the definition of the union *)
  fdec.svar.vtype <- voidType;
  fdec


let setupEhVariantThrowSpecPointer (eh: varinfo) (l: location)
    : varinfo * instr list =
  try
    H.find eh_variant_throw_spec eh.vname, []
  with Not_found -> begin
    let tmpptrtype, _, _, _ =
      splitFunctionTypeVI getEhVariantThrowSpecFun.svar
    in
    (* Make a temporary to hold the pointer *)
    let tmp =
      makeTempVar !currentFunction
        ~name:(eh.vname ^ "_variant_throw_spec")
        tmpptrtype in
    H.add eh_variant_function eh.vname tmp;
    tmp, [Call(Some (var tmp),
               (Lval (var getEhVariantThrowSpecFun.svar)),
               [ mkAddrOf (var eh) ], l) ]
  end




(** We have functions to set and get the array of virtual tables used when
 * constructing and destructing virtual base classes *)
let getVTArrayFun : fundec =
  let fdec = emptyFunction "__getVTArray" in
  (* Will set its type when we encounter the definition of the VTABLE_ENTRY *)
  fdec.svar.vtype <- voidType;
  fdec
let setVTArrayFun : fundec =
  let fdec = emptyFunction "__setVTArray" in
  (* Will set its type when we encounter the definition of the VTABLE_ENTRY *)
  fdec.svar.vtype <- voidType;
  fdec

let getCaughtObjectAddressFun: fundec =
  let fdec = emptyFunction "__get_caught_object_address" in
  fdec.svar.vtype <- funType voidPtrType [] false;
  fdec


(** Collect information about classes in this file *)
type classinfo =
    { ci: compinfo;
      uname: string; (* This is the uncompressed name, which might be
                      * different than the possibly compressed one in
                      * ci.cname *)
      c_width: int; (* The width in bytes of this class *)
      mutable issoof: classinfo option; (* Whether it is an SO class and in
                                         * that case the main class *)
      mutable soofthis: classinfo option; (* The __SO__class *)
      (* The list of super classes in the order in which they appear in the
       * object *)
      mutable super: superinfo list;
      mutable tinfovi: varinfo option; (* The variable that stores the type
                                        * info. Keep the first one that you
                                        * find. *)
      mutable bclassvi: varinfo option; (* The variable that stores
                                         * information about the superclasses
                                         *)

      mutable __vptr: offset option; (* Whether it is polymorphic (has
                                      * __vptr) and the offset to the __vptr *)

      (* Each class can have a number of vtables *)
      (* list of virtual method names, in the order they appear in the
       * vtable; this list does *not* include the RTTI data member, which is
       * actually the first element of EDG's vtable. Each class actually has
       * a number of vtables, one for itself, and one for each immediate
       * superclas, except maybe the first superclass which shares the vtable
       * with the object.  *)
      mutable vtables: vtableinfo list;


      (* It seems that a class can have multiple vtables even for offset 0.
       * Many of the duplicates start with __STV_. We just keep them here to
       * be able to connetct them to the representatives *)
      mutable duplicate_main_vtables: vtableinfo list;
    }

(* The information for the superclass *)
and super_virt = SV__b (* Not virtual *)
               | SV__p (* virtual and pointer to superclass *)
               | SV__v (* virtual and actual superclass *)

and superinfo =
    { s_info: classinfo;
      s_field: fieldinfo; (* The field of the host where this lives *)
      s_start: int; (* The starting offset (in bytes) *)
      s_width: int; (* The width (in bytes) *)
      s_isvirt: super_virt (* Whether this is a virtual superclass *)
    }

(* Each class can have multiple vtables in the presence of multiple
 * inheritance. In the case of single inheritance there is only one vtable. *)
and vtableinfo =
    { v_host: classinfo; (* The host of the vtable *)
      v_name: string;    (* The name of the variable that contains the table.
                          * This is "" if this is a table full of pure
                          * virtual methods that we added *)
      v_delta_int: int;   (* The offset as an integer that is recorded in the
                           * RTTI. *)
      v_superi: (classinfo * offset) option;
                         (* The information for the superclass to which this
                          * virtual table corresponds. Essentially this
                          * virtual table will be used only when the pointer
                          * to the host is cast to a pointer to this
                          * superclass. This is also the type of the
                          * superclass object that is stored at delta_off in
                          * the host. This is None if delta_int is 0 and
                          * there is no superclass.  *)
      v_methods: varinfo list (* The list of the methods as they appear in the
                             * virtual table. *)
    }

(* In PASS 1 will collect names of compinfos that are equivalent to one of
 * the metadata types. In PASS 2 will replace their uses with the metadata *)
let eqTypeNames: (string, compinfo) H.t = H.create 53
let setSpecialName (ci: compinfo) (meta: compinfo) =
  H.add eqTypeNames ci.cname meta;
  ci.cname <- meta.cname

(* We will also rename some global variables *)
let eqVarNames: (string, varinfo) H.t = H.create 53

(** All the classes that we know about indexed by ci.cname *)
let classes: (string, classinfo) H.t = H.create 117

(** Also all the classes indexed by the uncompressed name *)
let classesByUname: (string, classinfo) H.t = H.create 117


(* sm: map the RTTI variable name to the associated classinfo *)
let rttiToClass: (string, classinfo) H.t = H.create 117

(* Record here the RTTI variables that we have seen so that we can drop
 * duplicate definitions *)
let rttiDefined: (string, varinfo) H.t = H.create 117

(* set the class's rtti (tinfovi) member, and update the 'rttiToClass' map *)
let setRtti (ci: classinfo) (vi: varinfo) : unit =
begin
  ci.tinfovi <- Some vi;
  (H.add rttiToClass vi.vname ci)
end

(* maps the name of the base class variable to the classinfo *)
let baseClassToClass: (string, classinfo) H.t = H.create 117

(* Set the class's baseclass info *)
let setBaseClass (ci: classinfo) (vb: varinfo) : unit =
  ci.bclassvi <- Some vb;
  H.add baseClassToClass vb.vname ci


let dumpClasses () =
  ignore (E.log "The class hierarchy:\n");
  H.iter (fun cname cdata ->
    ignore (E.log " %s%a : %a\n\tName=%s\n\tTINFO:%s\n\tBC:%s\n\tVTBLS:%b\n\n"
              cname
              (* SO stuff *)
              insert (match cdata.soofthis
                         with None -> nil
                       | Some soci -> dprintf "(SO=%s)" soci.ci.cname)
              (* superclasses *)
              (docList (fun si ->
                                    dprintf "%s%s at %d"
                                        (match si.s_isvirt with
                                           SV__b -> ""
                                         | SV__v -> "virtual "
                                         | SV__p -> "virtual (__p) ")
                                        si.s_info.ci.cname
                                        si.s_start))
              cdata.super
              (* class name *)
              (if cdata.uname <> cdata.ci.cname then cdata.uname else "")
              (* RTTI information *)
              (match cdata.tinfovi with
                 None -> if cdata.__vptr <> None then
                         "None (has __vptr)" else "None"
               | Some ti -> ti.vname)
              (match cdata.bclassvi with
                 None -> "None"
               | Some bci -> bci.vname)
              (cdata.vtables <> [])
               ))
    classes



(**************************************************************************8
 **************************************************************************
 **
 **          PASS 0. CREATE META-DATA TYPES
 **
 ****************************************************************************
 ****************************************************************************)
(** This is not an actual scan of the file, but is done before we scan the
 * file *)

(* Indexed by name *)
let metaDataTypes: (string, compinfo) H.t = H.create 17
(* Indexed by the name and order of fields *)
let metaDataTypesFields : (string list, compinfo) H.t = H.create 17
let getMetaDataType (n: string) : compinfo =
  try
    H.find metaDataTypes n
  with Not_found ->
    E.s (unimp "Cannot find metadata type %s\n" n)

(** Create a metadata type. It is importatant that the name and order of
 * fields is the same as that of metadata types generated by EDG because we
 * will use the name and the order to recognize EDG-generated types that we
 * replace with these *)
let newMetaDataType
    (n: string)
    (flds: (string * typ) list) : compinfo =
  let res =
    mkCompInfo true n
      (fun _ ->
        List.map (fun (n, t) -> (n, t, None, [], locUnknown)) flds)
      []
  in
  H.add metaDataTypes n res;
  let fldsnames = List.map (fun (n, _) -> n) flds in
  H.add metaDataTypesFields fldsnames res;
  H.add eqTypeNames n res;
  res


let createMetadataTypes () =
  pushGlobal (GText "// CXXPP-created meta-data types");
(*
struct VTABLE_ENTRY {
   short vtable_field_d ;
   short vtable_field_i ;
   unsigned long vtable_field_f ;
}
*)
  let vtEntry = newMetaDataType "VTABLE_ENTRY"
      [ ("vtable_field_d", TInt(IShort, []));
        ("vtable_field_i", TInt(IShort, []));
        ("vtable_field_f", !upointType)] in
  pushGlobal (GCompTag(vtEntry, locUnknown));
(*
struct __type_info {
   struct VTABLE_ENTRY *__vptr ;
};
*)
  let typeInfoClass = newMetaDataType "__type_info"
      [ ("__vptr", TPtr(TComp(vtEntry, []), [])) ] in
  pushGlobal (GCompTag(typeInfoClass, locUnknown));
(*
struct TYPEINFO {
   struct __type_info tinfo ;
   char const   *name ;
   unsigned char *id ;
   struct BASECLASS_INFO *bc ;
};
*)
  let ucharType = TInt(IUChar, []) in
  let typeInfo = newMetaDataType "TYPEINFO"
      [ ("tinfo", TComp(typeInfoClass, []));
        ("name", TPtr(charType, [ Attr("const", []) ]));
        ("id", TPtr(ucharType, []));
        ("bc", voidType) (* Fix later *) ] in
(*
struct BASECLASS_INFO {
   struct TYPEINFO *tinfo ;
   short offset ;
   unsigned char flags ;
};
*)
  let baseClass = newMetaDataType "BASECLASS_INFO"
      [ ("tinfo", TPtr(TComp(typeInfo, []), []));
        ("offset", TInt(IShort, []));
        ("flags", ucharType) ] in
  (* Emit a forward declaration for this *)
  pushGlobal (GCompTagDecl(baseClass, locUnknown));
  (* Fixup the field for typeInfo *)
  (match typeInfo.cfields with
    _ :: _ :: _ :: bc :: [] -> bc.ftype <- TPtr(TComp(baseClass, []), [])
  | _ -> E.s (bug "baseClass"));
  pushGlobal (GCompTag(typeInfo, locUnknown));
  pushGlobal (GCompTag(baseClass, locUnknown));
(*
struct EH_REGION {
   unsigned long dtor ;
   unsigned short handle ;
   unsigned short next ;
   unsigned char flags ;
}
*)
  let ehRegion = newMetaDataType "EH_REGION"
      [ ("dtor",   TInt(IULong, []));
        ("handle", TInt(IUShort, []));
        ("next",   TInt(IUShort, []));
        ("flags",  TInt(IUChar, [])) ] in
  pushGlobal (GCompTag(ehRegion, locUnknown));
(*
struct EH_TYPESPEC {
   struct TYPEINFO *tinfo ;
   unsigned char flags ;
   unsigned char *ptr_flags ;
};
*)
  let ehTypespec = newMetaDataType "EH_TYPESPEC"
      [ ("tinfo",      TPtr(TComp(typeInfo, []), []));
        ("flags",      ucharType);
        ("ptr_flags",  TPtr(ucharType, [])) ] in
  pushGlobal (GCompTag(ehTypespec, locUnknown));

(*
struct EH_STACK_ENTRY_TRYBLOCK {
   int setjmp_buffer[39] ;
   struct EH_TYPESPEC *catch_entries ;
   void *rtinfo ;
   unsigned short region_number ;
};
*)
  let ehStackEntryTry = newMetaDataType "EH_STACK_ENTRY_TRYBLOCK"
      [ ("setjmp_buffer", TArray(intType, Some (integer 39), []));
        ("catch_entries", TPtr(TComp(ehTypespec, []), []));
        ("rtinfo", voidPtrType);
        ("region_number", TInt(IUShort, [])) ] in
  pushGlobal (GCompTag(ehStackEntryTry, locUnknown));
(*
union EH_STACK_ENTRY_UNION {
   struct EH_STACK_ENTRY_TRYBLOCK try_block ;
};
*)
  let ehStackEntryUnion = newMetaDataType "EH_STACK_ENTRY_UNION"
      [ ("try_block", TComp(ehStackEntryTry, [])) ] in
  ehStackEntryUnion.cstruct <- false;
  pushGlobal (GCompTag(ehStackEntryUnion, locUnknown));
  (* This one actually appears with more fields *)
  H.remove metaDataTypesFields ["try_block"];
  H.add metaDataTypesFields
    ["try_block";"function";"throw_spec"] ehStackEntryUnion;
  (* And sometimes is has an extra field *)
  H.add metaDataTypesFields
    ["try_block";"function";"throw_spec";"alloc_info"] ehStackEntryUnion;
(*
struct EH_STACK_ENTRY {
   struct EH_STACK_ENTRY *next_in_eh_stack_entry ;
   unsigned char kind ;
   union EH_STACK_ENTRY_UNION variant ;
};
*)
  let ehStackEntry = newMetaDataType "EH_STACK_ENTRY"
      [ ("next_in_eh_stack_entry", voidType);
        ("kind", ucharType);
        ("variant", TComp(ehStackEntryUnion, [])) ] in
  (* Fixup the recursive type *)
  (match ehStackEntry.cfields with
    n :: _ -> n.ftype <- TPtr(TComp(ehStackEntry, []), [])
  | _ -> E.s (bug "ehStackEntry"));
  pushGlobal (GCompTagDecl(ehStackEntry, locUnknown));
  pushGlobal (GCompTag(ehStackEntry, locUnknown));
  (* This one sometimes has the first field named just next *)
  H.add metaDataTypesFields (["next"; "kind"; "variant"]) ehStackEntry;
(*
struct ARRAY_INFO {
   unsigned short handle ;
   unsigned int elem_size ;
   long elem_count ;
};
*)
  let arrayInfo = newMetaDataType "ARRAY_INFO"
      [ ("handle", TInt(IUShort, []));
        ("elem_size", uintType);
        ("elem_count", longType) ] in
  pushGlobal (GCompTag(arrayInfo, locUnknown));

(*
struct EH_FunctionBlock {
   struct EH_REGION *regions ;
   unsigned long *obj_table ;
   struct ARRAY_INFO *array_table ;
   unsigned short saved_region_number ;
};
*)
  let ehFunctionBlock = newMetaDataType "EH_FunctionBlock"
      [ ("regions", TPtr(TComp(ehRegion, []), []));
        ("obj_table", TPtr(!upointType, []));
        ("array_table", TPtr(TComp(arrayInfo, []), []));
        ("saved_region_number", TInt(IUShort, [])) ] in
  pushGlobal (GCompTag(ehFunctionBlock, locUnknown));
(*
struct CTORDTOR_LIST {
   struct CTORDTOR_LIST *next ;
   unsigned long ctor ;
   unsigned long dtor ;
};
*)
  let ctordtorList = newMetaDataType "CTORDTOR_LIST"
      [ ("next", voidType); (* Will fill in later *)
        ("ctor", !upointType);
        ("dtor", !upointType) ] in
  (match ctordtorList.cfields with
    n :: _ -> n.ftype <- TPtr(TComp(ctordtorList, []), [])
  | _ -> ());
  pushGlobal (GCompTag(ctordtorList, locUnknown));
(*
struct DESTR_INFO {
   struct DESTR_INFO *next ;
   unsigned long object ;
   unsigned long dtor ;
};
*)
  let destrInfo = newMetaDataType "DESTR_INFO"
      [ ("next", voidType); (* Will fill-in later *)
        ("object", !upointType);
        ("dtor", !upointType) ] in
  (match destrInfo.cfields with
    n :: _ -> n.ftype <- TPtr(TComp(destrInfo, []), [])
  | _ -> ());
  pushGlobal (GCompTag(destrInfo, locUnknown));

(*** PROTOTYPES *)
  getEhVariantFunctionFun.svar.vtype <-
     funType (TPtr(TComp(ehFunctionBlock, []), []))
       [ ("pStackEntry", TPtr(TComp(ehStackEntry, []), [])) ] false;
  (* And add the prototype *)
  pushGlobal (GVarDecl(getEhVariantFunctionFun.svar, locUnknown));

  getEhVariantThrowSpecFun.svar.vtype <-
     funType (TPtr(TPtr(TComp(ehTypespec, []), []), []))
       [ ("pStackEntry", TPtr(TComp(ehStackEntry, []), [])) ] false;
  (* And add the prototype *)
  pushGlobal (GVarDecl(getEhVariantThrowSpecFun.svar, locUnknown));

  getVTArrayFun.svar.vtype <-
     funType (TPtr(TPtr(TComp(vtEntry, []),[]),[]))
       [ ("vptr", TPtr(TComp(vtEntry, []),[]));
         ("minlen", uintType) ]
       false;
  pushGlobal (GVarDecl(getVTArrayFun.svar, locUnknown));


  setVTArrayFun.svar.vtype <-
     funType voidType
       [ ("pThisVptr", TPtr(TPtr(TComp(vtEntry, []),[]), []));
         ("vptrarr", TPtr(TPtr(TComp(vtEntry, []),[]), [])) ]
       false;
  pushGlobal (GVarDecl(setVTArrayFun.svar, locUnknown));


  ptmLookupFun.svar.vtype <-
     cType "void * ()(void *this, struct %c:c *ptmData, void **pAdjThis)"
       [ ("c", Fc vtEntry)];
  pushGlobal (GVarDecl(ptmLookupFun.svar, locUnknown));
  setFunctionPoly ptmLookupFun.svar.vname locUnknown;

  (* Emit now the prototype for ptmLookupData *)
  pushGlobal (GVarDecl(ptmLookupData.svar, locUnknown));
  setFunctionPoly ptmLookupData.svar.vname locUnknown;

  vmLookupFun.svar.vtype <-
     cType "void * ()(void *this, struct %c:c *vtable, int off, void *pSuper, unsigned long pCheckTable, unsigned long overriden, char* location)"
       [ ("c", Fc vtEntry) ];
  pushGlobal (GVarDecl(vmLookupFun.svar, locUnknown));
  setFunctionPoly vmLookupFun.svar.vname locUnknown;

  downCastFun.svar.vtype <-
     cType "void * ()(void * obj , struct %c:vtEntry *vptr, struct %c:typeinfo *destti, struct %c:typeinfo *srcti)"
       [ ("vtEntry", Fc vtEntry);
         ("typeinfo", Fc typeInfo); ];

  pushGlobal (GVarDecl(downCastFun.svar, locUnknown));
  setFunctionPoly downCastFun.svar.vname locUnknown;
  (* See if we must emit a declaration for the checkVMTable *)
  if checkVMLookup then begin
    pushGlobal (GCompTag(checkVMTableEntry, locUnknown));
    pushGlobal (GVarDecl(checkVMTable, locUnknown));
  end;
  pushGlobal (GText "// end of CXXPP meta-data")




    (* Find the virtual pointer table for the source *)
let rec findVptr
    (off: offset) (* Offset so far *)
    (classi: classinfo) : offset option =
  (* See if we have a vptr field. *)
  try
    (* Do we have it ? *)
    let f =
      List.find (fun f -> f.fname = "__vptr") classi.ci.cfields in
    Some (addOffset (Field(f, NoOffset)) off)
  with Not_found -> begin
    (* No, we don't. But maybe our superclass at offset 0 has it *)
    (* Find among superclasses the one that starts at 0 and is not pointer to
     * virtual superclass *)
    try
      let si =
        List.find
          (fun si -> si.s_isvirt <> SV__p && si.s_start = 0)
          classi.super
      in
      findVptr (addOffset (Field(si.s_field, NoOffset)) off) si.s_info
    with Not_found -> (* No such superclass *)
      None
  end
(*
    (* Get the first field *)
    match ci.cfields with
      [] -> (* No fields. No vptr *) None
    | f :: _ -> begin
        match f.ftype with
          TComp(ci', _) ->
            let off' =
              addOffset (Field(f, NoOffset)) off in
            findVptr off' ci'
        | _ -> None
    end
*)
              (* Find the RTTI. Might raise Failure *)
let findRTTI (classi: classinfo) : varinfo =
  (* Maybe we have actually seen it *)
  match classi.tinfovi with
  | Some vi -> vi
  | None -> begin
      (* Did not find one in this class. But if it has a
       * vptr then we know there must be one somewhere. The linker will find
       * it. *)
      match classi.__vptr with
      | None -> raise (Failure ("missing RTTI for " ^ classi.ci.cname))
      | Some _ ->
          let rtti_name =
            let l = String.length classi.ci.cname in
            if prefix "__Q" classi.ci.cname then
              "__T_" ^ (String.sub classi.ci.cname 2 (l - 2))
            else
              "__T_" ^
              (string_of_int l) ^ classi.ci.cname
          in
          (* Find the TYPEINFO *)
          ignore (E.log "Created RTTI for %s\n" classi.ci.cname);
          let tinfo = getMetaDataType "TYPEINFO" in
          let newvi = makeGlobalVar rtti_name (TComp(tinfo, [])) in
          newvi.vstorage <- Extern;
          pushGlobal (GVarDecl (newvi, !currentLoc));
          (* And remember it once we have it *)
          classi.tinfovi <- Some newvi;
          newvi
  end

let soRegexp = Str.regexp "\\(\\(.+[^0-9]\\)\\([0-9]+\\)\\)?__SO__\\(.+\\)$"

(** This function is called on all compinfo that are not metadata. *)
let recordUserStructure (ci: compinfo) =
  let debugSO = false in
  (* See if it is an __SO_ structure. Then it is not a class per-se but a
   * shared object version of a class. *)
  (* There are two forms of names of SO objects: __SO__realname, and
   * __Qn_xxx56__SO__realname. In this latter case the real name for the
   * class is __Qn_xxx50realname. Also we try __realname *)
  let isSo (s: string) : classinfo option =
    if debugSO then ignore (E.log "Check whether %s is a SO class\n" s);

    if Str.string_match soRegexp s 0 then
      (* Get the actual name of the class *)
      let realname = Str.matched_group 4 s in
      if debugSO then
        ignore (E.log " it is with the real name %s\n" realname);
      (* See if we matched at the beginning *)
      let totry : string =
        try
          let prefix = Str.matched_group 2 s in
          let count = int_of_string (Str.matched_group 3 s) in
          if count - 6 <> String.length realname then begin
            ignore (warn "Invalid name for SO class");
            raise Not_found
          end;
          prefix ^ (string_of_int (count - 6)) ^ realname
        with Not_found ->
          (* No match at the beginning *)
          realname
      in
      if debugSO then
        ignore (E.log "  will look for real class %s\n" totry);
      try
        Some (H.find classes totry)
      with Not_found -> begin
        E.s (warn "Could not find the real version of SO: %s\n" s)
          None
      end
    else
      None (* Not an SO class *)
  in
  let issoof = isSo ci.cname in

  if H.mem classes ci.cname then
    ignore (warn "Duplicate definition of %s\n" ci.cname);

      (* Try to find super classes *)
  let rec findSuper (fil: fieldinfo list) : superinfo list =
    match fil with
      [] -> []
    | fi :: restfi ->
        (* If this a regular super class ? *)
        let issuper : super_virt option =
          if prefix "__b_" fi.fname then
            Some SV__b (* Yes, but not virtual *)
          else
            if prefix "__v_" fi.fname then
              Some SV__v (* Yes, it is virtual *)
            else
              if prefix "__p_" fi.fname then
                Some SV__p (* Yes, and virtual *)
              else
                None (* no *)
        in
        match issuper with
          None -> findSuper restfi
        | Some isvirt -> begin
            (* Find the superclass name *)
            let sname =
              match unrollTypeDeep fi.ftype with
                TComp(ci, _) -> ci.cname
              | TPtr(TComp(ci, _), _) -> ci.cname
              | _ -> E.s (bug "findSuper: not a compinfo")
            in
            (* String.sub fi.fname 4 (String.length fi.fname - 4) *)
            let sinfo =
              try Some (H.find classes sname)
              with Not_found -> begin
                (* Maybe it has two leading __ *)
                try Some (H.find classes ("__" ^ sname))
                with Not_found ->
                  None
              end
            in
            match sinfo with
              None ->
                  ignore (warn "Cannot find superclass %s of %s\n"
                            sname ci.cname);
                findSuper restfi
            | Some sinfo ->
                (* Find the offsets *)
                let start, width =
                  try
                    bitsOffset (TComp(ci, [])) (Field(fi, NoOffset))
                  with _ -> begin
                    (-1), 0
                  end
                in
                (* The offsets must be whole bytes *)
                if start < 0 || start land 7 <> 0 || width land 7 <> 0 then begin
                  ignore (warn "Cannot compute bitsOffset for %s.%s"
                            ci.cname fi.fname);
                  findSuper restfi
                end else
                  { s_info = sinfo; s_field = fi; s_isvirt = isvirt;
                    s_start = start lsr 3; s_width = width lsr 3; }
                  :: findSuper restfi
        end
  in
  let bases = findSuper ci.cfields in
  (* Find the size of the class *)
  let c_width =
    try bitsSizeOf (TComp(ci, [])) / 8
    with _ -> E.s (unimp "Cannot find the size of the class %s\n" ci.cname)
  in
  (* Create the data structure *)
  let class_i ={ ci = ci;
                 c_width = c_width;
                 soofthis = None; issoof = issoof;
                 super = bases; bclassvi = None;
                 uname = uncompressName ci.cname;
                 tinfovi = None;
                 __vptr = None; (* For now *)
                 vtables = [];
                 duplicate_main_vtables = [];} in
  (* See if it has a virtual pointer *)
  let __vptr =
    try
      (* Do we have it ? *)
      let f =
        List.find (fun f -> f.fname = "__vptr") class_i.ci.cfields in
      Some (Field(f, NoOffset))
    with Not_found -> begin
      (* No, we don't. But maybe our superclass at offset 0 has it *)
      (* Find among superclasses the one that starts at 0 and is not pointer
       * to virtual superclass *)
      try
        let si =
          List.find
            (fun si -> si.s_isvirt <> SV__p && si.s_start = 0)
            class_i.super
        in
        match si.s_info.__vptr with
          None -> None
        | Some parent_vptr ->  Some (Field(si.s_field, parent_vptr))
      with Not_found -> (* No such superclass *)
        None
    end
  in
  class_i.__vptr <- __vptr;
  H.add classes ci.cname class_i;
  H.add classesByUname class_i.uname class_i;

  (* See if we must set the soofthis *)
  (match issoof with
    Some real ->
      if real.soofthis != None then
        ignore (warn "Duplicate __SO__ (%s)" ci.cname);
      real.soofthis <- Some class_i
  | _ -> ())

(* Sometimes EDG drops some declarations of classes. We remember the compinfo
 * so that we can fill-it in later *)
let emptyCompinfo: (string, compinfo) H.t = H.create 13

let fillInEmptyCompinfo () =
  H.iter (fun n ci ->
    if ci.cfields = [] then begin
      (* It could be that we have renamed this to be a metadata type *)
      if not (H.mem metaDataTypes ci.cname) then begin
        ignore (E.warn "Adding a dummy definition for %s" ci.cname);
        ci.cfields <- [ { fname = "__dummy"; ftype = charType; fcomp = ci;
                          fbitfield = None; fattr = []; floc = locUnknown } ];
        recordUserStructure ci
      end
    end)
    emptyCompinfo

(** Keep track of the type names to avoid capturing them when we rename
 * variables *)
let typeNames: (string, unit) H.t = H.create 113

let initPass1 () : unit =
  H.clear typeNames;
  H.clear emptyCompinfo

(*************************************************************************
 *************************************************************************
 **
 **           PASS 1
 **
 *************************************************************************
 *************************************************************************)
(** The following things happen in this pass. *)
(* 1. We complete the prototypes for a number of run-time function that EDG
 * uses. EDG is sloppy about declaring the argument types *)
(* 2. We add polymorphic declarations for those functions. *)
(* 3. We recognize the EDG definitions for structures that implement the
 * meta-data and we change their names with the standard ones we created in
 * PASS 0. We recognize the structures based on the names and order of the
 * fields. We will replace these structures in PASS 2. *)
(* 4. We collect a list of non-meta-data structure definitions. These must be
 * structures and classes from the original program. The function
 * "recordUserStructure" is called for all such structures and it attempts to
 * construct a class hierarchy. *)
(* 5. We read the "inherits" pragmas and we use that to aid the construction
 * of the class hierarchy. *)
(* 6. We rename the local variables to use names as close as possible with
 * those from the original source program *)
(* 7. We recognize definitions and initialization of global variables that
 * represent RTTI. We record them in the class hierarchy. *)
let pass1 = function
    (* Variable declarations *)
    GVarDecl(vi, l) as g -> begin
      (* Add ccuredalloc pragmas for NEW *)
      if isNew vi.vname then begin
        pushGlobal
           (GPragma(Attr("ccuredalloc", [ AStr(vi.vname);
                                          ACons("nozero",[]);
                                          ACons("sizein", [AInt 1])]), l));
        pushGlobal g
        (* Make DELETE polymorphic *)
      end else if isDelete vi.vname then begin
        setFunctionPoly vi.vname l;
        pushGlobal g
        (* Fix the prototype for throw_setup. *)
      end else if vi.vname = "__throw_setup" then begin
        let tinfo = getMetaDataType "TYPEINFO" in
        vi.vtype <-
           funType voidPtrType
             [ ("tinfo", (TPtr(TComp(tinfo, []), [])));
               ("arg2", uintType); ("arg3", intType) ] false;
        setFunctionPoly vi.vname l;
        pushGlobal g

              (* Fix the prototype for setjmp *)
      end else if vi.vname = "setjmp" then begin
        vi.vtype <- funType intPtrType [ ("jmpbuf", intPtrType) ] false;
        pushGlobal g

        (* Fix the prototype for memcpy *)
      end else if vi.vname = "memcpy" then begin
        (* Only if not already present *)
        let _, args, _, _ = splitFunctionType vi.vtype in
        if args == None then
          vi.vtype <- funType voidPtrType [ ("dest", voidPtrType);
                                            ("src", voidPtrType);
                                            ("len", uintType) ] false

        (* Fix the prototype for __vec_delete *)
      end else if vi.vname = "__vec_delete" then begin
        vi.vtype <-
           funType voidType
             [ ("this", voidPtrType);
               ("arg2", intType); ("arg3", intType); ("dtor", voidPtrType);
               ("arg5", intType); ("arg6", intType) ] false;
        (* And make it polymorphic *)
        setFunctionPoly vi.vname l;
        pushGlobal g

        (* Fix the prototype for __vec_new *)
      end else if vi.vname = "__vec_new" then begin
        vi.vtype <-
           funType voidPtrType
             [ ("this", voidPtrType);
               ("arg2", intType); ("arg3", intType);
               ("ctor", voidPtrType); ] false;
        (* And make it polymorphic *)
        setFunctionPoly vi.vname l;
        pushGlobal g
        (* Fix the prototype for __vec_new_eh *)
      end else if vi.vname = "__vec_new_eh" then begin
        vi.vtype <-
           funType voidPtrType
             [ ("this", voidPtrType); ("arg2", uintType); ("arg3", uintType);
               ("ctor", voidPtrType); ("dtor", voidPtrType) ] false;
        (* And make it polymorphic *)
        setFunctionPoly vi.vname l;
        pushGlobal g


        (* Fix the prototype for record_needed_destruction *)
      end else if vi.vname = "__record_needed_destruction" then begin
        let destr_info = getMetaDataType "DESTR_INFO" in
        vi.vtype <-
           funType intPtrType [ ("dinfo", (TPtr(TComp(destr_info, []), []))) ]
             false;
        pushGlobal g

              (* Fix the prototype for __memzero *)
      end else if vi.vname = "__memzero" then begin
        vi.vtype <-
           funType voidType [ ("this", voidPtrType);
                              ("len", uintType) ] false;
        (* And make it polymorphic *)
        setFunctionPoly vi.vname l;
        pushGlobal g

        (* Fix the prototype for __suppress_optim_in_try *)
      end else if vi.vname = "__suppress_optim_on_vars_in_try" then begin
        vi.vtype <- funType voidType [ ("this", !upointType) ] true;
        pushGlobal g;
        pushGlobal (GPragma(Attr("ccuredvararg", [ AStr vi.vname;
                                                   ASizeOf !upointType ]), l))

        (* Fix the prototype for __throw_setup_dtor *)
      end else if vi.vname = "__throw_setup_dtor" then begin
        let tinfo = getMetaDataType "TYPEINFO" in
        vi.vtype <-
           funType voidPtrType
             [ ("tinfo", TPtr(TComp(tinfo, []), []));
               ("arg2", uintType); ("arg3", intType);
               ("dtor", !upointType) ] false;
        (* And make it polymorphic *)
        setFunctionPoly vi.vname l;
        pushGlobal g

        (* Fix the prototype for __dynamic_cast and __dynamic_cast_ref *)
      end else if vi.vname = "__dynamic_cast" ||
                  vi.vname = "__dynamic_cast_ref" then
        begin
          let tinfo = getMetaDataType "TYPEINFO" in
          let vte = getMetaDataType "VTABLE_ENTRY" in
          vi.vtype <-
             funType voidPtrType
               [ ("obj", voidPtrType);
                 ("vptr", TPtr(TComp(vte, []), []));
                 ("arg3", TPtr(TComp(tinfo, []), []));
                 ("ob2", voidPtrType);
                 ("arg4", TPtr(TComp(tinfo, []), []));] false;
            (* And make it polymorphic *)
            setFunctionPoly vi.vname l;
            pushGlobal g

        (* Add canpointtostack to curr_eh_stack_entry *)
      end else if vi.vname = "__curr_eh_stack_entry" then begin
        vi.vattr <- addAttribute (Attr("mayPointToStack", [])) vi.vattr;
        pushGlobal g

      end else if vi.vname = "__caught_object_address" then begin
        (* Drop this and replace with a function *)
        pushGlobal (GVarDecl(getCaughtObjectAddressFun.svar, l));
        setFunctionPoly getCaughtObjectAddressFun.svar.vname l;

      end else
        pushGlobal g
    end
        (* Structure definitions *)
  | (GCompTag (ci, l) as g) -> begin
      (* See if it is one of the metadata *)
      try
        (* There are indexed by the list of field names *)
        let fnames = List.map (fun fi -> fi.fname) ci.cfields in
        let metaci = H.find metaDataTypesFields fnames in
        (* Change the names only if the name starts with __T *)
        if not (prefix "__T" ci.cname) then raise Not_found;

        (if metaci.cname = "TYPEINFO" then begin
          match ci.cfields with
            _ :: _ :: _ :: bc :: [] when bc.fname = "bc" -> begin
              (* Make sure to rename the BASECLASS_INFO if not defined *)
              match unrollTypeDeep bc.ftype with
                TPtr(TComp(bc_ci, _), _) when bc_ci.cfields == [] ->
                  let vte = getMetaDataType "BASECLASS_INFO" in
(*
                  ignore (E.log "Changing name of %s to %s\n"
                            ci.cname vte.cname);
*)
                  setSpecialName bc_ci vte
              | _ -> ()
            end
          | _ -> ignore (warn "Found TYPEINFO without bc\n"); ()
        end);

        (if metaci.cname = "EH_FunctionBlock" then begin
          match ci.cfields with
            _ :: _ :: at :: _ :: [] when at.fname = "array_table" -> begin
              (* Make sure to rename the ARRAY_INFO if not defined *)
              match unrollTypeDeep at.ftype with
                TPtr(TComp(at_ci, _), _) when at_ci.cfields == [] ->
                  let vte = getMetaDataType "ARRAY_INFO" in
(*
                  ignore (E.log "Changing name of %s to %s\n"
                            ci.cname vte.cname);
*)
                  setSpecialName at_ci vte
              | _ -> ()
            end
          | _ -> ignore (warn "Found EH_FunctionBlock without at\n"); ()
        end);
        setSpecialName ci metaci;
        () (* Drop this one *)

      with Not_found -> begin
        (* Did not find among metadata *)
        (* Give a warning if this is a structure name that starts with __T
        * and we got here. This means that we are not renaming all
        * meta-data structures. *)
        if prefix "__T" ci.cname then
          ignore (E.warn "CXXPP: Unknown meta-data structure %s at %a\n"
                         ci.cname  d_loc l);
        (* Record this user-structure *)
        if ci.cstruct then recordUserStructure ci;
        (* Maybe it has a field with name __vptr whose type is a pointer to
        * an undefined structure. Replace that structure with VTABLE_ENTRY*)
        List.iter
          (fun f ->
            if f.fname = "__vptr" then begin
              match unrollType f.ftype with
                TPtr(TComp(ci, _), _)
                  when ci.cfields == [] && prefix "__T" ci.cname ->
                    let vte = getMetaDataType "VTABLE_ENTRY" in
                    setSpecialName ci vte
              | _ -> ()
            end)
          ci.cfields;
        pushGlobal g;
      end
  end

  (*** PASS 1. Compinfo declarations *)
  | GCompTagDecl (ci, l) as g when ci.cfields == [] ->
      (* Remember the empty compinfos *)
      if not (H.mem emptyCompinfo ci.cname) then H.add emptyCompinfo ci.cname ci;
      pushGlobal g

  (*** PASS 1. Remember typenames so that we don't rename variables to
   * capture those names **)
  | GType (ti, _) as g ->
      H.add typeNames ti.tname ();
      pushGlobal g

  (*** PASS 1. Function definitions *)
  | GFun (fdec, l) as g ->
      (* Rename some of the locals *)
      let localNames : (string, int ref) H.t = H.create 113 in
      (* Populate the localNames with all the names of the types *)
      H.iter (fun tname _ -> H.add localNames tname (ref 0)) typeNames;

      let renameLocal (loc: varinfo) =
        (* See if its name is of the form __dddd_dd_xxxx. Then try to rename
        * it xxxx. These are the true locals to which EDG has prepended the
        * digits *)
        let nl = String.length loc.vname in
        let totry =
          (* Ignore the leading __ and digits *)
          match skipPrefix loc.vname 0 with
          | None -> (* Only _ and digits. Leave alone *) loc.vname
          | Some idx ->
              (* Maybe what follows is Tddddddd *)
              if String.get loc.vname idx = 'T' then begin
                match skipPrefix loc.vname (idx + 1) with
                  None -> (* This is __Tddddddddd *) "edgtmp"
                | Some _ -> loc.vname (* leave alone *)
              end else
                String.sub loc.vname idx (nl - idx)
        in
        (* Now see if the name is available. Actually get the current counter
        * for it *)
        let counter =
          try H.find localNames totry
          with Not_found -> begin
            let c = ref (-1) in
            H.add localNames totry c;
            c
          end
        in
        incr counter;
        loc.vname <-
           totry ^ (if !counter = 0 then "" else "__" ^ string_of_int !counter)
      in
      List.iter renameLocal fdec.slocals;
      List.iter renameLocal fdec.sformals;
      pushGlobal g

  (* this recognizes the global variable definition of an RTTI entry,
   * and connects it to the corresponding classinfo *)
  | GVar (vi, {init = Some (CompoundInit(_, [ _;
                                      (_, SingleInit cname);
                                      _;
                                      (_, SingleInit bclass)]))}, l) as g
      when (match vi.vtype with TComp(ci, _)
                   when ci.cname = "TYPEINFO" -> true | _ -> false)
    -> (* Maybe we are merging and EDG emitted the type definition multiple
        * times. We keep a table of representatives, indexed by the name with
        * the suffix stripped *)
      let lookupname =
        if Str.string_match
            (Str.regexp "^\\(.+\\)___[0-9]+$") vi.vname 0 then
          Str.matched_group 1 vi.vname
        else
          vi.vname
      in
      let keepThisOne =
        try
          let orig_vi = H.find rttiDefined lookupname in
          (* We have found another one already defined *)
          H.add eqVarNames vi.vname orig_vi;
          false (* Do not process this one *)
        with Not_found -> begin
          (* We'll make this the representative. Its name can have a suffix
           * so we have to index it with the LOOKUPNAME. Later, after PASS 2
           * we will change the names to be the LOOKUPNAME. *)
          H.add rttiDefined lookupname vi;
          true
        end
      in
      if not keepThisOne then (* Drop it and we are done *) () else
      begin
        (* Use the lookupname to lookup whose class this belongs to *)
        let uname = uncompressName lookupname in
        if not (prefix "__T_" uname) then begin
          ignore (warn "TYPEINFO global with unexpected name: %s\n" vi.vname);
        end else begin
          (* Now find the classinfo structure *)
          try begin
            let cinfo =
              let mname =
                match skipPrefix uname 4 with
                  Some l -> String.sub uname l (String.length uname - l)
                | None ->
                    E.s (unimp "Invalid name for type_info variable %s\n"
                           vi.vname)
              in
              (* Now skip some digits *)
              try
                H.find classesByUname mname
              with Not_found -> begin
                try H.find classesByUname ("__" ^ mname)
                with Not_found -> begin
                  ignore (warn "Found type info but not a class definition for %s\n"
                            mname);
                  raise (Failure "")
                end
              end
            in
            (* Keep only the first typeinfo or else we'll be using not-yet
             * defined variables *)
            if cinfo.tinfovi == None then begin
              setRtti cinfo vi;
              (* Now see if we recognize the base class information *)
              match dropCasts bclass with
                Const _ as c when isZero c -> () (* No base class *)
              | StartOf (Var vb, NoOffset) ->
                  setBaseClass cinfo vb

              | _ ->
                  ignore (warn "Cannot recognize the base class for %s\n"
                            vi.vname);
            end;
          end
          with Failure _ -> ();
        end;
        pushGlobal g
      end

  | g -> pushGlobal g


let renameRTTI () =
  H.iter
    (fun lookupname vi ->
      (try
        (* If this RTTI was mapped to a class, copy the mapping *)
        H.add rttiToClass lookupname (H.find rttiToClass vi.vname)
      with Not_found -> ());
      vi.vname <- lookupname)
    rttiDefined

(********************************************************************8
 *********************************************************************
 **
 ** PASS 2
 ** Apply the renaming for meta-data
 **
 *********************************************************************
 *********************************************************************)
(* The following happen in PASS 2. NOTE THAT PASS2 is done in REVERSE ORDER
 * to reduce by 2 the List.rev on globals.  *)
(* 1. We go over all the types and offsets and we replace uses of meta-data
 * structure with the ones that we generated. *)
(* 2. We drop the definitions of the old meta-data *)
(* 3. We replace the declarations for the empty compinfo with definitions for
 * structs with a dummy field *)
(* 4. Scan the virtual tables and populate the classinfo with information
 * about their contents *)

let compinfoReplacement (ci: compinfo) =
  try
    H.find eqTypeNames ci.cname
  with Not_found -> ci

(* given an 'init' initializer which looks like
 *   { delta, 0, ((void ( * )())& some_name ) }
 * extract some_name as a varinfo; if the initializer doesn't
 * have this structure, raise Not_found *)
let takeApartVtableEntry (entry: init) : int * int * varinfo =
  match entry with
  | CompoundInit(_,
          [ (_, SingleInit (Const(CInt64(delta, _, _))));  (* delta *)
            (_, SingleInit (Const(CInt64(fieldi, _, _)))); (* fieldi *)
            (_, SingleInit addr) ])
    ->
      let d = Int64.to_int delta in
      let i = Int64.to_int fieldi in
      let vi =
        match dropCasts addr with
          AddrOf (Var vi, NoOffset) -> vi
        | _ ->
            ignore (warn "vtable_f field is not the address of a varible");
            raise Not_found
      in
      if i <> 0 then
        ignore (warn "Found vtable entry with non-zero fieldi");
      d, i, vi

  | _ ->
      ignore (warn "Cannot take apart vtable entry: %a\n" d_init entry);
      raise Not_found

let constructVtableEntry (delta: exp) (fieldi: int) (v: varinfo) =
  let vte = getMetaDataType "VTABLE_ENTRY" in
  let f1, f2, f3 =
    match vte.cfields with
      f1 :: f2 :: f3 :: _ -> f1, f2, f3
    | _ -> E.s (bug "constructVtableEntry")
  in
  CompoundInit(TComp(vte, []),
                 [ (Field(f1, NoOffset), SingleInit delta);  (* delta *)
                   (Field(f2, NoOffset), SingleInit (integer fieldi)); (* fieldi *)
                   (Field(f3, NoOffset), SingleInit (mkCast (mkAddrOf (var v)) !upointType)) ])

(** Produce an expression that computes an offset of *)
let offsetOfExp (off: offset) =
  match off with
    Field(fi, restoff) -> (* Must start with a field *)
      CastE(TInt(IShort, []),
            AddrOf (Mem (CastE(TPtr(TComp(fi.fcomp, []), []), zero)),
                    off))
  | _ -> E.s (bug "offsetOfExp")

(** Find superclass that lies at a given offset in the object. Return the
 * information for it and an offset from the host to the subobject.
 * Optionally you can pass a size of the super object, which makes the search
 * more precise. If size is negative then it means that we need to look
 * always for __p fields (pointers to superclasses). Returns None if there is
 * no superclass (this could happen only for off = 0). Raises Not_found if
 * something goes wrong. *)
let rec findSuperAtOffset
    (classi: classinfo)
    (off: int)
    (size: int)
    (why: unit -> doc) : (classinfo * offset) option =
  (* Search the super classes at the given offset *)
  let rec search = function
      [] ->
        if off = 0 then
          None
        else begin
          ignore (warn "Could not find a parent class at offset %d in %s%a\n  (when %t)\n"
                    off classi.ci.cname
                    insert
                    (if size <> 0 then
                      dprintf "(of size %d)" size else nil)
                    why);
          raise Not_found
        end

    | superi :: rest ->
        if superi.s_start = off &&
          (size <= 0 || superi.s_width = size) then begin (* We found it *)
               Some (superi.s_info, Field(superi.s_field, NoOffset))
             end
        else (* Maybe we are looking for something that is INSIDE one of
              * our immediate superclasses *)
          if superi.s_start <= off &&
            off < superi.s_start + superi.s_width then begin
              match findSuperAtOffset
                  superi.s_info (off - superi.s_start) size why with
                None -> (* Should not happen. Continue and will fail. *)
                search rest
              | Some (foundi, foundoff) ->
                  Some (foundi, addOffset foundoff
                          (Field(superi.s_field, NoOffset)))
          end else
            (* Try the next superclass *)
            search rest
  in
  search classi.super

let deltaSuper = function
    None -> zero
  | Some (classi, off) ->
      (* Treat the first field as a special case *)
      if fst (bitsOffset (TComp(classi.ci, [])) off) = 0 then
        zero
      else
        offsetOfExp off

(****** PURE VIRTUAL FUNCTIONS *******)
(** Keep track of the pure_virtual methods invoked *)
let pureVirtualId = ref 0 (* An ID to create new ones *)

(* For each one keep the fundec *)
let pureVirtuals: (string, fundec) H.t = H.create 113

(* Make a new pure virtual ID function *)
let newPureVirtual () : varinfo =
  incr pureVirtualId;
  (* Create it with a void type for now *)
  let pv = emptyFunction
           ("__pure_virtual_called" ^ string_of_int !pureVirtualId) in
  pv.svar.vtype <-  TFun(voidType, None, false, []);
  pv.svar.vstorage <- Static;
  pv.svar.vinline <- true;
  H.add pureVirtuals pv.svar.vname pv;
  pv.svar

(* Keep here the actual pure_virtual_called *)
let pure_virtual_called: varinfo option ref = ref None

(* Initialize the pure virtual handling *)
let initPureVirtuals () =
  pureVirtualId := 0;
  pure_virtual_called := None;
  H.clear pureVirtuals


(* Add bodies for the new pure virtual functions *)
let addPureVirtualBodies () =
  (* First we must make sure to propagate the types among the pure_virtuals
   * that override eachother. If a pure virtual is overriden by a non-pure
   * function then we have already set its type *)
  let changed = ref true in
  while !changed do
    changed := false;
    H.iter (* Scan all pure virtuals *)
      (fun _ fdec ->
        (* Find who is overridden by this one *)
        let rt, args, isva, a = splitFunctionType fdec.svar.vtype in
        if args <> None then begin (* It has a type *)
          List.iter
            (fun attr ->
              match attr with
                Attr(_, [AStr overriden_name]) -> begin
                  try
                    let over = H.find pureVirtuals overriden_name in
                    let _, args', _, a' =
                      splitFunctionType over.svar.vtype in
                    if args' == None then begin
                      changed := true;
                      trace "vtable"
                        (dprintf "Propagating type of %s to %s\n"
                           fdec.svar.vname over.svar.vname);
                      over.svar.vtype <- TFun(rt, args, isva, a')
                    end
                  with Not_found ->
                    E.s (bug "%s overrides a non-pure virtual method\n"
                           fdec.svar.vname)
                end
              | _ -> E.s (bug "Invalid override attribute"))
            (filterAttributes "override" a)
        end)
      pureVirtuals
  done;

  (* Now do the generation of the bodies *)
  H.iter
    (fun _ fdec ->
      (* Do not share the bodies *)
      let pvc = match !pure_virtual_called with
        Some vi -> vi
      | None -> E.s (bug "addPureVirtualBodies")
      in
      fdec.sbody <-
         mkBlock [ mkStmtOneInstr (Call(None,
                                        Lval (var pvc),
                                        [], locUnknown)) ];
      (* Make sure to establish the sharing. We first need to make the
       * formals. *)
      let rt, args, isva, a = splitFunctionType fdec.svar.vtype in
      (* We clean up the function type. makeFormalVar will add the formals *)
      fdec.svar.vtype <- TFun(rt, Some [], isva, a);
      let formIdx = ref (-1) in
      List.iter
        (fun (an, at, aa) ->
          incr formIdx;
          ignore (makeFormalVar fdec ("arg" ^ string_of_int !formIdx) at))
        (argsToList args);
      theFile := GFun(fdec, locUnknown) :: !theFile)
    pureVirtuals;

  (* Now clean up the hashes *)
  initPureVirtuals ()



(** Process the initializer for a virtual table. This is invoked after PASS 2
 * renaming has been performed on the initializer. May throw an exception *)
let processVirtualTable (g: global list) : global list =
  (* Get the components out *)
  let vi, initList, l, ci, al, aa =
    match g with
      [GVar(vi, {init=Some (CompoundInit(TArray(TComp(ci, _), al, aa),
                                   initList))}, l)]
      -> vi, initList, l, ci, al, aa
    | _ -> E.s (bug "processVirtualTable")
  in
  (trace "vtable" (dprintf "%t: I see a vtable, name is %s\n"
                           d_thisloc vi.vname));
  (* Now decode the virtual table name *)
  let ofclass = decodeVtblName vi.vname in
  (* Now grab the RTTI that must be the first entry *)
  let offrtti,rtti,methodEntries =
    match initList with
      (offrtti, rtti) :: rest -> offrtti, rtti, rest
    | _ ->
        (ignore (warn "Found a vtable with no entries: %s" vi.vname));
        raise Not_found
  in
  (* Now take apart the first entry in the list; it should be
  *     { delta, 0, ((void ( * )())& rtti_data_name ) }         *)
  let delta, fieldi, rttivi = takeApartVtableEntry rtti in
  (trace "vtable" (dprintf "and I see the RTTI: %s. Delta is %d\n"
                           rttivi.vname delta));

  (* query the rtti->class map *)
  let classi:classinfo =
      (* Find the host based on the name *)
    if ofclass <> "" then begin
      try H.find classesByUname ofclass
      with e -> begin
        ignore (warn "Cannot find classinfo for vtbl %s (looking for %s)\n"
                  vi.vname ofclass);
        raise e
      end
    end else begin
      (* Find the host based on RTTI *)
      try (H.find rttiToClass rttivi.vname)
      with e -> begin
        ignore (warn "Cannot find classinfo for %s\n" rttivi.vname);
        raise e
      end
    end
  in

  trace "vtable" (dprintf "corresponds to class %s\n" classi.ci.cname);

  (* Now find out to which parent it corresponds. Go through the superclasses
   * and find out whose offset matches this delta. *)
  let (whose_table_is_this: (classinfo * offset) option) =
    findSuperAtOffset classi delta 0
      (fun _ -> dprintf "finding owner of vtable %s" vi.vname)
  in
  let newdelta = deltaSuper whose_table_is_this in
  (match whose_table_is_this with
    None ->
      trace "vtable" (dprintf " table is the main one (and no superclass)\n")
  | Some (_, offsuper) ->
      if isZero newdelta then
        trace "vtable" (dprintf " table is the main one (and for some parents as well)\n")
      else
        trace "vtable" (dprintf " table is for %a parent\n"
                                (d_offset nil) offsuper));
  (* work through the remaining entries in the vtable, making
   * a list of method names that appear there and producing a new initializer
   * list *)
  let (methods : varinfo list), (methodEntries' : (offset * init) list) =
    (* given an entry in the virtual table, extrac the name of the method
     * involved and produce a new entry in which the offset is expressed as
     * an expression *)
    let processOneEntry (i: init) : varinfo * init =
      let delta', fieldi', method' = takeApartVtableEntry i in
      (trace "vtable" (dprintf " virtual method: %s\n" method'.vname));
      let newoff =
        if delta' = 0 then zero else
        match (findSuperAtOffset classi (- delta') 0
                   (fun _ -> dprintf "finding offset for entry in vtable %s"
                                vi.vname))
        with
          None -> zero
        | r ->
            let newdelta = deltaSuper r in
            UnOp(Neg, newdelta, typeOf newdelta)
      in
      let method_pv =
      if method'.vname = "__pure_virtual_called" then begin
        (* Save the actual pure_virtual_called *)
        if !pure_virtual_called = None then
          pure_virtual_called := Some method';
        let res = newPureVirtual () in
        trace "vtable" (dprintf "   turned into %s\n" res.vname);
        res
      end else
        method'
      in
      method_pv, constructVtableEntry newoff fieldi' method_pv
    in
    List.fold_right
      (fun (off, i) (methods, restinit) ->
        let m', i' = processOneEntry i in
        (m' :: methods, (off, i') :: restinit))
      methodEntries ([], [])
  in
  (* store this list of methods in the classinfo *)
  trace "vtable" (dprintf "Setting the methods for %s\n\n" vi.vname);
  (* Now build the vtableinfo *)
  let vti =
    { v_host = classi;
      v_name = vi.vname;
      v_delta_int = delta;
      v_methods = methods;
      v_superi = whose_table_is_this; }
  in
  (* See if we have seen a table for this offset already. If we have then we
   * put this one in duplicates. *)
  (if delta = 0 &&
      (List.exists
         (fun vti -> vti.v_delta_int = delta)
         classi.vtables) then
    classi.duplicate_main_vtables <- vti :: classi.duplicate_main_vtables
  else
    classi.vtables <- vti :: classi.vtables);

  (* Now reconstruct the initializer for the virtual table *)
  let initList' =
    (offrtti, constructVtableEntry newdelta fieldi rttivi) ::
    methodEntries'
  in
  (* Now reconstruct the global *)
  let res =
    GVar(vi, {init=Some (CompoundInit(TArray(TComp(ci, []), al, aa),
                                initList'))}, l) in
  (* Append to that declarations for all the pure_virtuals that we have
   * created. We must append because we are in the pass were we do everything
   * in reverse.  *)
  let pureVirtualsDecls =
    List.fold_left
      (fun acc mth ->
        if prefix "__pure_virtual_called" mth.vname then
          GVarDecl(mth, l) :: acc
        else
          acc)
      []
      methods in
  res :: pureVirtualsDecls

(* Add the override attribute to a function type. Also propagate the type to
 * the overriden method if that one is a pure_virtual without a type *)
let addOverrideAttribute (ftyp: typ) (parent: varinfo) : typ =
  let vrt, vargs, visva, va = splitFunctionType ftyp in
  (* Compute the new type  *)
  let newTyp = TFun(vrt, vargs, visva,
                    addAttribute (Attr("override", [AStr parent.vname])) va) in
  (* If the parent does not have a type already, but we have one then we
   * propagate the type to the parent *)
  let prt, pargs, pisva, pa = splitFunctionType parent.vtype in
  if prefix "__pure_virtual_called" parent.vname &&
     pargs = None && vargs <> None then
    (* Keep the parent's attribute because that includes the override
     * attribute *)
    parent.vtype <- TFun(vrt, vargs, visva, pa);
  newTyp



(** Find the main virtual table. Throws Not_found if it cannot find it.  *)
let findMainVTable (classi: classinfo) : vtableinfo =
  List.find (fun vti -> vti.v_delta_int = 0) classi.vtables



(** Match the VTI with the main virtual table of the PARENT, or if
 * IS_DUPLICATE with the main virtual table of the current host. *)
let matchVTable (vti: vtableinfo) (is_duplicate: bool) : unit =
  (* parent table *)
  let parent_table_o =
    if is_duplicate then
      try Some (vti.v_host, findMainVTable vti.v_host)
      with Not_found -> E.s (bug "matchVTable duplicate but no main found")
    else begin (* With the main one of the parent *)
      match vti.v_superi with
        None -> None (* Done. No parent along this line. *)
      | Some (superi, _) -> begin
          try
            Some (superi, findMainVTable superi)
          with Not_found ->
            (* Maybe the parent does not have virtual methods *)
            if superi.vtables <> [] then
              ignore (warn "Cannot find main virtual table for %s\n"
                        superi.ci.cname);
            None
      end
    end
  in
  match parent_table_o with
  | None -> ()
  | Some (parent, parentTable) ->
      (* For each method find the one it overrides *)
      let rec loopEntries (idx: int)
                          (over: varinfo list) (sup: varinfo list) =
        match over, sup with
          _, [] -> (* The parent always finishes first *) ()
        | [], _ :: _ ->
            ignore (E.warn "The virtual table %s is shorter than the one for the parent %s\n" vti.v_name parent.ci.cname)

        | o :: resto, s :: rests ->
            trace "vtable" (dprintf " Looking at %s[%d]:%s\n"
                                    vti.v_name idx o.vname);
            (* See if this override is already marked *)
            if s != o &&
              (* If this is a duplicate main table then we do not care about
               * the pure_virtuals. Let them be disconnected *)
               (not is_duplicate ||
                not (prefix "__pure_virtual_called" o.vname)) &&
              not (List.exists
                     (function (Attr(_, [AStr up])) ->
                       up = s.vname | _ -> false)
                     (filterAttributes "override" (typeAttrs o.vtype))) then
              begin
                trace "vtable" (dprintf "  overrides %s\n" s.vname);
                if checkVMLookup then addCheckVMTableEntry o s;

                (* Add an attribute in the type of the method *)
                o.vtype <- addOverrideAttribute o.vtype s;

              end;
            (* Continue with the other entries *)
            loopEntries (idx + 1) resto rests
      in
      loopEntries 0 vti.v_methods parentTable.v_methods


(** Process the initialization of a baseclass table. We must turn the magic
 * offsets into actual offset computations. While doing this we will call
 * findSuperAtOffset and this way we will verify that our understanding of
 * the class hierarchy is correct. *)

(** A set of tables that are defined in the code but we cannot connect to
 * classes. Hopefully these are not used *)
let orphanBaseclassTables: (string, unit) H.t = H.create 111

let processBaseClassTable (gl: global list) : global list =
  (* Get the components out *)
  let vi, initList, l, ci, al, aa =
    match gl with
      [GVar(vi, {init=Some (CompoundInit(TArray(TComp(ci, _), al, aa),
                                   initList))}, l)]
      -> vi, initList, l, ci, al, aa
    | _ -> E.s (bug "processBaseClassTable")
  in
  (trace "vtable" (dprintf "%t: I see a bclass table, name is %s\n"
                           d_thisloc vi.vname));
  (* Now see whose base class is this *)
  let classi =
    try H.find baseClassToClass vi.vname
    with Not_found ->
      (* It appears that sometimes certain baseclass tables are not used.
       * Just remember this one and we'll check later if it actually gets
       * used *)
      H.add orphanBaseclassTables vi.vname ();
      raise Not_found
  in
  (* Now change the name of the variable *)
  vi.vname <- "__BC_" ^ classi.ci.cname;
  H.add baseClassToClass vi.vname classi;
  trace "vtable" (dprintf "  changed name to %s\n" vi.vname);
  (* Now rewrite the entries *)
  let initList' =
    List.fold_right
      (fun i acc ->
        match i with
          (idx,
           CompoundInit (bct, [ (f1, SingleInit super);
                                (f2, SingleInit (Const(CInt64(delta, _, _))));
                                (f3, SingleInit (Const(CInt64(flags, _, _))))
                              ]))
          ->
            let newdelta =
              try
                begin
                  (* Find the claimed super class *)
                  let claimed_superi =
                    match dropCasts super with
                      AddrOf (Var superrtti, NoOffset) -> begin
                        try H.find rttiToClass superrtti.vname
                        with e ->
                          ignore (E.warn
                                  "Cannot find class for the RTTI %s (from %s)\n"
                                    superrtti.vname vi.vname);
                          raise e
                      end
                    | _ ->
                        ignore (warn "Cannot understand RTTI in %s\n"
                                  vi.vname);
                        raise Not_found
                  in
                  (* If the claimed superi has a SO, then it is the SO that
                   * actually lives in the entry *)
                  let claimed_superi =
                    match claimed_superi.soofthis with
                      None -> claimed_superi
                    | Some i -> i
                  in
                  (* If the "flags" is odd then we are actually looking for a
                   * virtual parent. To do this we must pass a negative size
                   * fo findSuperAtOffset *)
                  let size =
                    if (Int64.to_int flags) land 1 = 0 then
                      claimed_superi.c_width
                    else
                      -1
                  in
                  (* Find out what super class is at the given offset *)
                  match
                    (findSuperAtOffset classi (Int64.to_int delta) size
                           (fun _ -> dprintf "verifying baseclass entry in %s"
                               vi.vname))
                  with
                    None -> (* This should not happen *)
                      ignore (warn "Can't verify baseclass entry %s (no super at offset)"
                                vi.vname);
                      raise Not_found
                  | Some (superi, superoff) as super_result ->
                      (* Now check that indeed this is the same as the one
                       * claimed *)
                      let check_against =
                        if size >= 0 then (* This is NOT a virtual superclass *)
                          claimed_superi
                        else begin (* A virtual superclass *)
                          match claimed_superi.issoof with
                            Some i -> i
                          | None -> claimed_superi
                        end
                      in
                      if superi != check_against then begin
                        ignore (warn "baseclass table claims %s and we found a %s"
                                  check_against.ci.cname
                                  superi.ci.cname)
                      end;
                      (* And change the offset *)
                      let newdelta = deltaSuper super_result in
                      newdelta
                end
              with _ -> Const(CInt64(delta, IInt, None))
            in
            let i' =
              (idx,
               CompoundInit (bct, [ (f1, SingleInit super);
                                    (f2, SingleInit newdelta);
                                    (f3,
                                     SingleInit (Const(CInt64(flags,
                                                              IInt,None))))
                                   ])) in
            i' :: acc

        | _ ->
            ignore (warn "Cannot understand baseclass table entry");
            i :: acc)
      initList
      []
  in
  [GVar(vi, {init=Some(CompoundInit(TArray(TComp(ci, []), al, aa),
                              initList'))}, l)]


(** A visitor use in pass 2 **)
class pass2VisitorClass : cilVisitor = object (self)
  inherit nopCilVisitor


  (* PASS 2. Types. Changed the compinfo to the equivalence class *)
  method vtype (t: typ) =
    match t with
      TComp(ci, a) ->
        let ci' = compinfoReplacement ci in
        if ci' != ci then begin
          ChangeTo (TComp(ci', a))
        end else
          SkipChildren

    | _ -> DoChildren

  (* PASS 2. Offsets *)
  method voffs (o: offset) =
    match o with
      Field(fi, resto) ->
        let ci = compinfoReplacement fi.fcomp in
        if ci != fi.fcomp then begin
          (* Find the field with the same name in the new compinfo *)
          try
            let fi' = List.find (fun f -> f.fname = fi.fname) ci.cfields in
            ChangeTo (Field(fi', visitCilOffset (self :> cilVisitor) resto))
          with Not_found ->
            (* Some fields were dropped *)
            if (fi.fname = "function" || fi.fname = "throw_spec")
                 && ci.cname = "EH_STACK_ENTRY_UNION" then
              DoChildren
            else
              E.s (bug "Cannot find field \"%s\" in replacement for %s\n"
                     fi.fname ci.cname)
        end else
          DoChildren
    | _ -> DoChildren

  method vinitoffs (o: offset) =
    (self#voffs o)     (* treat initializer offsets same as lvalue offsets *)

  (* PASS 2. Expressions. *)
  method vexpr (e: exp ) =
    match e with
      (* Remove some casts *)
      CastE(t, e) -> begin
        let t' = visitCilType (self :> cilVisitor) t in
        let e' = visitCilExpr (self :> cilVisitor) e in
        match unrollTypeDeep t', unrollTypeDeep (typeOf e') with
          TPtr(TComp(ci1, _), _), TPtr(TComp(ci2, _), _) when ci1 == ci2 ->
            ChangeTo e'
        | _ -> DoChildren
      end
    | _ -> DoChildren

   (* PASS 2. Variable uses *)
  method vvrbl (v: varinfo) =
    if v.vglob then
      try
        let orig = H.find eqVarNames v.vname in
        ChangeTo orig
      with Not_found ->
        DoChildren
    else
      DoChildren

   (* PASS 2. Global declarations. *)
  method vglob (g: global) =
    match g with
      (* Same thing for declarations and definitions *)
      GCompTagDecl (ci, l) | GCompTag(ci, l) ->
        let ci' = compinfoReplacement ci in
        if ci != ci' then
          ChangeTo [] (* Drop it since it is not the one we need to keep *)
        else begin
          (* See if this was a declaration for an emptyCompInfo. In that case
           * change the declaration into a definition. *)
          if H.mem emptyCompinfo ci.cname then begin
            (* Remove it so we don't add more than one definition *)
            H.remove emptyCompinfo ci.cname;
            ChangeTo [GCompTag(ci, l)]
          end else
            DoChildren (* Scan the field definitions *)
        end
      (* EDG sometimes emits multiple copies of a TYPEINFO in different
       * files. When we merge we get rid of them *)


    (* Drop some declarations and definitions for variables we removed *)
    | GVar(vi, _, l) | GVarDecl(vi, l) when H.mem eqVarNames vi.vname -> ChangeTo []

    (* sm: recognize the vtable as an array of VTABLE_ENTRY *)
    | GVar(vi,
           {init=Some (CompoundInit (TArray(TComp(ci, _), al, aa),
                               initList))}, l) as g
        when ci.cname = "VTABLE_ENTRY"
      ->  ChangeDoChildrenPost([g],
                               fun a ->
                                 try processVirtualTable a with _ -> a)

      (* Recognize the initialization for a BASECLASS_INFO *)
    | GVar(bcvi,
           {init=Some (CompoundInit (TArray(TComp(ci, _), al, aa),
                               initList))}, l) as g
        when ci.cname = "BASECLASS_INFO"
      ->
        if fixBaseClassTables then
          ChangeDoChildrenPost([g],
                               fun a ->
                                 try processBaseClassTable a with _ -> a)
        else begin (* Just change its name *)
          bcvi.vname <- newName "base_class";
          DoChildren
        end

    | _ -> DoChildren
end
let pass2Visitor = new pass2VisitorClass


(*************************************************************************
 *************************************************************************
 **
 **  PASS 3
 **
 *************************************************************************)
(* The following things happen in pass 3: *)
(* 1. We recognize the initializers for a number of meta-data global
 * variables. In there we remove some casts since the types of cetain fields
 * in our metadata are different from those of EDG *)
(* 2. We change the names of the global and local variables that contain
 * meta-data. These are detected based on their types. These newly created
 * names will be important for detecting manipulations of meta-data.  *)
(* 3. Detect virtual method calls and insert calls to __vmLookup *)
(* 4. Detect pointer to members and replace them with __ptmLookup (see below
 * for the pattenrs used) *)
(* 5. Process references to caught_object_address and replace them with calls
 * to a run-time function *)
(* 6. Emit forward declarations of RTTI varinfos so that we can use them in
 * downcast *)
(* 7. We check whether we actually use the orphan base class tables *)
(* 8. We remove casts in calls to __throw_setup_dtor *)
let vt_array_len: exp option ref = ref None


(*** POINTER TO MEMBER **)
(* EDG implements a pointer to member as follows:

  tmp1 = ( struct P* )(( char * )obj + (int)ptmLV.vtable_field_d);
  if((int)ptmLV.vtable_field_i < 0) {
     tmpfun = ptmLV.vtable_field_f;
  } else {
     vt_entry = ...;
     tmp1 = ( struct P* )(( char * )tmp1 + (int)vt_entry->vtable_field_d);
     tmpfun = vt_entry->vtable_field_f;
  }
  tmpfun2 = ( fun_ptr_type )tmpfun;
  ( *tmpfun2 )(tmp1, ...)
*)
(** Keep a state machine to recognize and process pointer-to-member
 * implementations *)
type ptmData = { ptmThis: varinfo;  (* The temporary that contains the
                                     * adjusted "this" pointer *)
                 ptmObj: exp; (* The unadjusted "this" pointer *)
                 ptmDataLval: lval;
                 mutable ptmStatus: ptmStatus; }
and ptmStatus =
    PTM_ThisAdjusted (* This is the initial state. The [this] pointer has been
                      * adjusted *)
  | PTM_FunPtr of varinfo (* The function pointer has been calculated in the
                           * given varinfo *)

let ptrMemData: ptmData option ref = ref None

(* We recognize the above code in three stages. First we see the assignment
 * to [tmp1] and we create a [ptmData] to remember [tmp1], [obj] and [ptmLV].
 * We drop the assignment to tmp1 *)
(* Then we recognize the conditional statament, we do a quick check (on the
 * 'then' branch only) and we drop it. We also record in the [ptmStatus]
 * field that we are in [PTM_FunPtr] status and we record [tmpfun] *)
(* In the last stage we recognize the assignment to [tmpfun2] and we replce
 * it with

  tmpfun2 = __ptmLookup(( void* )obj, & ptmLV, & tmp1 );

*)

let initPass3Function (fd: fundec) =
  currentFunction := fd;
  H.clear eh_variant_function;
  (* We can reset the counters for some local names *)
  H.remove nameCounters "eh_stack_entry";
  H.remove nameCounters "eh_obj_table";
  H.remove nameCounters "vt_array";
  ptrMemData := None;
  H.clear vt_entries;
  theFileAfter := [];
  vt_array_len := None


(* This function is called when we are about to insert a vmLookup for a given
 * static type and a given offset into the virtual table. Find the
 * representative method *)
let findOverrideRepresentative (tThis: typ) (off: int) : varinfo option =
  try
    match unrollTypeDeep tThis with
      TPtr(TComp(ci, _), _) -> begin
        let classi =
          try H.find classes ci.cname
          with e -> begin
            ignore (warn "No classinfo found for %s\n" ci.cname);
            raise e
          end
        in
        (* Find the main virtual table. I hypothesize that when the main
         * virtual table cannot be found then we have a class with only pure
         * virtual methods, without descendents. This means that the class
         * cannot be instantiated, so no virtual method table is emitted. In
         * that case let the exception travel *)
        let mainTable = findMainVTable classi in

        (* Find the method in the main virtual table *)
        let mth : varinfo =
          if List.length mainTable.v_methods <= off - 1 then begin
            ignore (warn "Virtual method is at offset %d too large for %s\n"
                      off ci.cname);
            raise Not_found
          end;
          (* Lookup off - 1 because off reflects the facts the the vtable
           * contains the RTTI in the first entry *)
          List.nth mainTable.v_methods (off - 1)
        in
(*
        ignore (E.log "%a: It appears that vmLookup will call %s\n"
                  d_loc !currentLoc mth.vname);
*)
        Some mth
      end
    | _ ->
        ignore (warn "addOverrideAttribute on a non pointer: %a" d_type tThis);
        None
  with _ ->
    None




(** A visitor use in pass 3 **)
class pass3VisitorClass : cilVisitor = object (self)
  inherit nopCilVisitor

  (* PASS 3. Types. Changed the compinfo to the equivalence class
  method vtype (t: typ) =
    match t with
      TComp(ci, a) -> begin
        try
          let ci' = H.find eqTypeNames ci.cname in
          if ci' != ci then
            ChangeTo (TComp(ci', a))
          else
            SkipChildren
        with Not_found ->
          SkipChildren
      end
    | _ -> DoChildren
  *)

  (* Initializers *)
  method vinit (forg: varinfo) (off: offset) (i: init) =
    match i with
      (* Initializer for REGIONS. Remove the cast in the initializer for dtor
       * since we changed the type to a non-pointer type *)
      CompoundInit ((TComp(ci, _) as t), [(off_dtor, idtor); i2; i3; i4])
        when ci.cname = "EH_REGION" -> begin
          match idtor with
            SingleInit e ->
              let idtor' = SingleInit (mkCast (dropCasts e) !upointType) in
              ChangeTo (CompoundInit (t, [(off_dtor, idtor'); i2; i3; i4]))

          | _ -> E.s (unimp "Unexpected initializer for EH_REGION")
        end

       (* Initializer for VTABLE_ENTRY. Remove the cast for the
        * vtable_field_f field since it is a non-pointer type *)
    | CompoundInit (t, [i1; i2; (off_fnc, ifnc)])
        when (match unrollType t with
                  TComp(ci, _) -> ci.cname = "VTABLE_ENTRY"
                | _ -> false) -> begin
          match ifnc with
            SingleInit e ->
              let ifnc' = SingleInit (mkCast (dropCasts e) !upointType) in
              ChangeTo (CompoundInit (t, [i1; i2; (off_fnc, ifnc')]))

          | _ -> E.s (unimp "Unexpected initializer for VTABLE_ENTRY")
        end



        (* Initializer for DESTR_INFO. Remove casts *)
    | CompoundInit ((TComp(ci, _) as t),
                    [i1; (off_obj, iobj); (off_dtor, idtor)])
        when ci.cname = "DESTR_INFO"  -> begin
          let iobj' =
            match iobj with
              SingleInit e -> SingleInit (mkCast (dropCasts e) !upointType)
            | _ -> E.s (unimp "Unexpected initializer for DESTR_INFO")
          in
          let idtor' =
            match idtor with
              SingleInit e -> SingleInit (mkCast (dropCasts e) !upointType)
            | _ -> E.s (unimp "Unexpected initializer for DESTR_INFO")
          in
          ChangeTo (CompoundInit (t, [i1; (off_obj, iobj');
                                       (off_dtor, idtor')]))
        end

        (* Initializer for CTORDTOR_LIST. Remove casts *)
    | CompoundInit ((TComp(ci, _) as t),
                    [i1; (off_ctor, ictor); (off_dtor, idtor)])
        when ci.cname = "CTORDTOR_LIST" -> begin
          let ictor' =
            match ictor with
              SingleInit e -> SingleInit (mkCast (dropCasts e) !upointType)
            | _ -> E.s (unimp "Unexpected initializer for CTORDTOR_LIST")
          in
          let idtor' =
            match idtor with
              SingleInit e -> SingleInit (mkCast (dropCasts e) !upointType)
            | _ -> E.s (unimp "Unexpected initializer for CTORDTOR_LIST")
          in
          ChangeTo (CompoundInit (t, [i1; (off_ctor, ictor');
                                       (off_dtor, idtor')]))
        end

    | _ -> DoChildren (* Do not recurse *)

   (* Pass 3. Variable uses *)
  method vvrbl (v: varinfo) =
    if v.vglob then begin
      if H.mem orphanBaseclassTables v.vname then
        ignore (warn "Using baseclass table %s which was thought to be orphan\nThis happens when the RTTI that mentions the baseclass table is not present\n"
                  v.vname)
    end;
    DoChildren

   (* Pass 3. Variable declarations *)
  method vvdec (vi: varinfo) =
    match unrollType vi.vtype with
      (* Change the names of the regions variables *)
      TArray(TComp (ci, _), _, _) when ci.cname = "EH_REGION" ->
        vi.vname <- newName "eh_regions";
        SkipChildren
       (* Change the names of the eh_stack_entries *)
    | TComp(ci, _) when ci.cname = "EH_STACK_ENTRY" ->
        vi.vname <- newName "eh_stack_entry";
        SkipChildren

       (* Change the names of the tinfos. Only if it is Static and the name
        * does not start with __T_. Otherwise we keep the name because it
        * encodes the class.  *)
    | TComp(ci, _) when
           ci.cname = "TYPEINFO"
           && vi.vstorage = Static && not (prefix "__T_" vi.vname) ->
        vi.vname <- newName "tinfo";
        SkipChildren

       (* Change the names of eh_typespecs *)
    | TArray(TComp(ci, _), _, _) when ci.cname = "EH_TYPESPEC" ->
        vi.vname <- newName "eh_typespecs";
        SkipChildren

      (* Change the names of the regions variables *)
    | TArray(TComp (ci, _), _, _) when ci.cname = "EH_THROWINFO" ->
        vi.vname <- newName "eh_throwinfo";
        SkipChildren

       (* Change the name of the VTABLE_ENTRYs *)
    | TPtr(TComp(ci, _), _) when ci.cname = "VTABLE_ENTRY" ->
        vi.vname <- newName "vt_entry";
        SkipChildren

       (* Change the name of the VTABLE_ENTRYs *)
    | TComp(ci, _) when ci.cname = "VTABLE_ENTRY"
                     && prefix "__T" vi.vname
                     && vi.vstorage = Static ->
        vi.vname <- newName "ptr_mem";
        SkipChildren

       (* See if we have extern declarations for virtual tables with no
        * length. Put the length 1 so that CCured does not make the array
        * sized *)
    | TArray(TComp(ci, _), None, a)
        when (ci.cname = "VTABLE_ENTRY" && vi.vstorage = Extern) ->
          vi.vtype <- TArray(TComp(ci, []), Some (integer 1), a);
          SkipChildren

       (* Constructors and destructors for classes with virtual base classes
        * sometimes manipulate VTABLE_ENTRYs in strange ways. Rename some
        * temporaries to help in detecting those situations *)
    | TPtr(TPtr(TComp(ci, _), _), _) when ci.cname = "VTABLE_ENTRY" ->
        vi.vname <- newName "vt_array";
        SkipChildren

    | TComp(ci, _) when ci.cname = "DESTR_INFO" ->
        vi.vname <- newName "destr_info";
        SkipChildren


     (* Initializer for virtual tables for virtual bases *)
    | TArray(TPtr(TComp(ci, _), _), _, _) when ci.cname = "VTABLE_ENTRY"
      ->
        vi.vname <- newName "join_vtbl";
        SkipChildren

    | _ -> DoChildren

    (* PASS 3. Instructions *)
  method private vinstHelp (i: instr) =
    match i with
      (* Catch assignments to the obj_table *)
    | Set (((Var eh_ot, (Index _)) as lv), e, l)
        when prefix "eh_obj_table" eh_ot.vname
      ->
        ChangeTo [Set(lv, mkCast (dropCasts e) !upointType, l)]

      (* Call to suppress_var_optim_in_try. Turn all arguments into integers *)
    | Call (None, Lval(Var so, NoOffset),
            args, l) when so.vname = "__suppress_optim_on_vars_in_try"
      ->
        let args' =
          List.map (fun a -> mkCast (dropCasts a) !upointType) args in
        ChangeTo [Call(None, Lval(Var so, NoOffset), args', l) ]


      (* Look for the start of a sequence that implements pointer-to-member *)
      (*
         tmp1 = ( C * )(( char* )obj + (int)lv.vtable_field_d)
      *)
    | Set ((Var tmp1, NoOffset),
           CastE(TPtr(TComp(destci, _), _),
                 BinOp(PlusPI,
                       CastE(TPtr(TInt(IChar, _), _), obj),
                       CastE(TInt _, Lval lv), _)), l)
        when (fixPtrMemFun &&
              (match removeOffsetLval lv with
                lv', Field(field_d, NoOffset)
                  -> field_d.fname = "vtable_field_d"
              | _ -> false))
      ->
        let lv' = fst (removeOffsetLval lv) in
        if debugPtrMem then begin
          ignore (E.log "Found ptrmem: adjusted %a to %s dictated by %a\n"
                    d_exp obj tmp1.vname d_lval lv');
          if !ptrMemData <> None then
            ignore (warn "ptrMem for %s was already started\n" tmp1.vname);
        end;
        let data =
          { ptmThis = tmp1;
            ptmObj = obj;
            ptmDataLval = lv';
            ptmStatus = PTM_ThisAdjusted; } in
        (* Store the data for both the this pointer and the datavar *)
        ptrMemData := Some data;
        (* Drop this instruction *)
        ChangeTo [ ]

         (* And now look for the final step in the pointer-to-member
          * implementation. The actual casting of the function pointer *)
    | Set ((Var trueFptr, NoOffset),
           CastE(TPtr(TFun _, _),
                 Lval (Var fptr, NoOffset)), l)
        when fixPtrMemFun &&
             (match !ptrMemData with
                  Some data -> begin
                    match data.ptmStatus with
                      PTM_FunPtr fptr' when fptr == fptr' -> true
                    | _ -> false
                  end
                | _ -> false)
      ->
        if debugPtrMem then ignore (E.log "Found ptrmem stage 3\n");
        let data =
          match !ptrMemData with Some d -> d
           | _ -> E.s (bug "ptrmem3")
        in
        (* Set the vaddrof flags *)
        (match data.ptmDataLval with
          Var v, _ -> v.vaddrof <- true;
        | _, _ -> ());
        data.ptmThis.vaddrof <- true;
        (* Reset the machine *)
        ptrMemData := None;
        ChangeTo [ cInstr "%v:trueFptr = %v:ptmLookup((void*)%e:ptmObj, &%l:ptmData, &%v:ptmThis);"
                     l
                     [ ("trueFptr", Fv trueFptr);
                       ("ptrLookup", Fv ptmLookupFun.svar);
                       ("ptmObj", Fe (dropCasts data.ptmObj));
                       ("ptmData", Fl data.ptmDataLval);
                       ("ptmThis", Fv data.ptmThis) ] ]

        (* Sometimes a pointer to a member function is computed in the code *)
    | Set (((Var ptmf, Field(vtable_f, NoOffset)) as lhs),
           CastE (_, AddrOf (Var f, NoOffset)), l)
        when (fixPtrMemFun && vtable_f.fname = "vtable_field_f" )->
          ChangeTo [Set(lhs, mkCast (AddrOf (Var f, NoOffset)) !upointType, l) ]

          (* Record the last vt_entry = ... This is computing a vtable
           * entry for the next virtual method dispatch *)
    | Set ((Var vte, NoOffset), e, l)
        when fixVCall && prefix "vt_entry" vte.vname
      -> begin
        (* Break the e *)
        (match dropCasts e with
          | BinOp(PlusPI,
                  (* sm: weakened "Var obj" to just "host", for structs/virtcall4.cc *)
                  (Lval(host, vptr_off) as vptrfield),
                  Const(CInt64(i64, _, _)), _) ->
                    (* See that the last offset in vptr_off is the __vptr *)
                    let rec splitOff = function
                        Field(vptr, NoOffset) when vptr.fname = "__vptr"
                        -> NoOffset
                      | Field(f, off) -> Field(f, splitOff off)
                      | Index(i, off) -> Index(i, splitOff off)
                      | NoOffset -> E.s (unimp "Cannot find the __vptr")
                    in
                    let objlval = (host, (splitOff vptr_off)) in
                    let idx = Int64.to_int i64 in
                    (*
                    ignore (E.log "Found %s := VTE(%a)[%d]\n" vte.vname d_exp obj off);
                    *)
                    if H.mem vt_entries vte.vname then
                      ignore (warn "Loosing vt_entry for %s\n" vte.vname);
                    H.add vt_entries vte.vname
                      (vte, objlval, vptrfield, idx)

          | _ -> E.s (unimp "vt_entry is not set as expected: %a" d_exp e));
        (* Drop this instruction *)
        ChangeTo []
      end

          (* Now the virtual dispatch *)
    | Call (res, Lval (Mem (CastE(pfType,
                                  Lval (Mem (Lval (Var vte, NoOffset)),
                                        Field (vt_fnc, NoOffset)))),
                       NoOffset), this :: restargs, l)
        when fixVCall && (vt_fnc.fname = "vtable_field_f" &&
              prefix "vt_entry" vte.vname)
      ->
        begin
          (*
          ignore (E.log "Found vcall VTE=%s THIS=%a\n" vte.vname d_exp this);
          *)
          (* Grab the saved last_vt_entry *)
          let (vte', objlval, vptr, off) =
            try
              H.find vt_entries vte.vname
            with Not_found ->
              E.s (unimp "Found dynamic dispatch but without vt_entry set")
          in
          if vte != vte' then
            E.s (unimp "Invalid saved data for dynamic dispatch");
          (* Erase the saved information. Hopefully EDG does not reuse it for
           * more than one dynamic dispatch *)
          H.remove vt_entries vte.vname;
          (* Break apart the THIS argument *)
          let tThis =
            match this with
              (* (struct C * )(( char* )this + (int)vt_entry->vtable_field_d) *)
              CastE(tThis,
                    BinOp(PlusPI,
                          CastE (TPtr(TInt(IChar, _), _),
                                 this),
                          CastE (TInt _,
                                 Lval (Mem (Lval (Var vte', NoOffset)),
                                       Field (v_d, NoOffset))), _))
                when v_d.fname = "vtable_field_d" ->
                  if vte' != vte then
                    E.s (unimp "Invalid THIS argument in virtual call (VTE)\n");
                  (* Now we should check that this == obj *)
                  tThis
            | _ -> E.s (unimp "Invalid THIS argument in virtual call\n");
          in
          (* Make a temporary variable to store the pSuper returned by
          * __vmLookup *)
          let pSuper = makeTempVar !currentFunction ~name:"pSuper" tThis in
          pSuper.vaddrof <- true;
          (* Lookup the type of a method that we might be calling here.  *)
          let over = findOverrideRepresentative tThis off in
          (* Add the appropriate attribute to the pftype. *)
          let pfType' =
            match over with
              None -> pfType
            | Some mth -> begin
                (* This must be a function pointer *)
                match pfType with
                  TPtr(tfun, a) ->
                    TPtr(addOverrideAttribute tfun mth, a)
                | _ -> E.s (bug "virtual dispatch on a non-function pointer")
            end
          in
          (* Make a temporary variable to store the function pointer *)
          let pFun    = makeTempVar !currentFunction ~name:"vmptr" pfType' in
          (* Now call __vmLookup to set the two variables *)
          let i1 =
            (* See if we must check its result *)
            let checkTable, checkOverriden =
              match checkVMLookup, over with
                true, Some mth ->
                  (* We run the risk of using the method before it is
                   * declared. Stick a declaration for it *)
                  theFileAfter := GVarDecl(mth, !currentLoc) :: !theFileAfter;
                  mkCast (StartOf (var checkVMTable)) !upointType,
                  mkCast (mkAddrOf (var mth)) !upointType
              | true, None ->
                  (* This means that we have not found a representative for
                   * the method that we are calling. Since we need to check
                   * this, make it such that this vmLookup will fail: pass a
                   * null pointer instead of the method to be called. *)
                  ignore (warn "Cannot find a representative for virtual method #%d in a table of %a\n" off d_type tThis);
                  mkCast (StartOf (var checkVMTable)) !upointType,
                  mkCast zero !upointType
              | false, _ ->
                  mkCast zero !upointType,
                  mkCast zero !upointType
            in
            Call (Some (var pFun),
                  Lval (var vmLookupFun.svar),
                  [ mkCast (mkAddrOf objlval) voidPtrType;
                    mkCast vptr voidPtrType;
                    integer off;
                    mkCast (mkAddrOf (var pSuper))
                      (TPtr (voidPtrType, [])) ;
                    checkTable; checkOverriden;
                    mkString (sprint 80 (d_loc () !currentLoc))
                  ], l)
          in
(*
          let i1 =
            fInstr "%v = %v((void * )&%l, (void* )%e, %d, (void** )& %v)"
              l [ Fv pFun; Fv vmLookupFun.svar;
                  Fl objlval; Fe vptr; Fd off; Fv pSuper ] in
*)
          (* And now make the real invocation *)
          let i2 =
            Call (res, Lval (mkMem (Lval (var pFun)) NoOffset),
                  Lval (var pSuper) :: restargs, l)
          in
          ChangeTo [i1; i2]
        end

          (* Setting of eh_stack.variant.function *)
    | Set ((Var ehs, Field(variant, Field(func, restoff))), what, l)
        when (prefix "eh_stack_entry" ehs.vname &&
              variant.fname = "variant" &&
              func.fname = "function")
      ->
        (* If we are actually setting the obj_table change the name and
        * the type of the obj_table variable *)
        (match restoff with
          Field(fot, NoOffset) when fot.fname = "obj_table" -> begin
            match dropCasts what with
              StartOf (Var ot, NoOffset) ->
                ot.vname <- newName "eh_obj_table";
                (* Change the type also to avoid pointers *)
                (match ot.vtype with
                  TArray(_, len, a) ->
                    ot.vtype <- TArray(!upointType, len, a)
                | _ -> E.s (unimp "Unexpected type of eh_obj_table"))
            | _ -> E.s (unimp "Unexpected form of obj_table")
          end
        | _ -> ());
        (* See if we need to make a temporary pointer to the function
        * variant *)
        let (tmpptr: varinfo), (setup: instr list) =
          setupEhVariantFunctionPointer ehs l
        in
        ChangeTo (setup @
                  [ Set((mkMem (Lval (var tmpptr)) restoff), what, l) ])


          (* Using of eh_stack_entry.variant.function *)
    | Set (destlv, Lval(Var eh, Field(variant,
                                      Field(func, restoff))), l)
        when (prefix "eh_stack_entry" eh.vname &&
              variant.fname = "variant" &&
              func.fname = "function")
      ->
        (* See if we need to make a temporary pointer to the function
        * variant *)
        let (tmpptr: varinfo), (setup: instr list) =
          setupEhVariantFunctionPointer eh l
        in
        ChangeTo (setup @
                  [ Set(destlv, Lval (mkMem (Lval (var tmpptr))
                                        restoff), l) ])

          (* Setting of eh_stack.variant.throw_spec *)
    | Set ((Var ehs, Field(variant, Field(func, restoff))), what, l)
        when (prefix "eh_stack_entry" ehs.vname &&
              variant.fname = "variant" &&
              func.fname = "throw_spec")
      ->
        (* See if we need to make a temporary pointer to the throw_spec
         * variant *)
        let (tmpptr: varinfo), (setup: instr list) =
          setupEhVariantThrowSpecPointer ehs l
        in
        ChangeTo (setup @
                  [ Set((mkMem (Lval (var tmpptr)) restoff), what, l) ])

          (* Using of eh_stack_entry.variant.throw_spec *)
    | Set (destlv, Lval(Var eh, Field(variant,
                                      Field(func, restoff))), l)
        when (prefix "eh_stack_entry" eh.vname &&
              variant.fname = "variant" &&
              func.fname = "throw_spec")
      ->
        (* See if we need to make a temporary pointer to the function
        * variant *)
        let (tmpptr: varinfo), (setup: instr list) =
          setupEhVariantThrowSpecPointer eh l
        in
        ChangeTo (setup @
                  [ Set(destlv, Lval (mkMem (Lval (var tmpptr))
                                        restoff), l) ])

          (* Call to _vec_delete. Remove some casts *)
    | Call (None, (Lval (Var vd, NoOffset) as lv),
            [a1; a2; a3; dtor; a5; a6], l)
        when vd.vname = "__vec_delete" ->
          ChangeTo [Call (None, lv, [a1; a2; a3;
                                      mkCast (dropCasts dtor) voidPtrType;
                                      a5; a6], l)]

            (* Call to _vec_new. Remove some casts *)
    | Call (res, (Lval (Var vd, NoOffset) as lv),
            [a1; a2; a3; ctor;], l)
        when vd.vname = "__vec_new" ->
          ChangeTo [Call (res, lv, [a1; a2; a3;
                                     mkCast (dropCasts ctor) voidPtrType],
                          l)]

            (* Call to _vec_new_eh. Remove some casts *)
    | Call (res, (Lval (Var vd, NoOffset) as lv),
            [a1; a2; a3; ctor; dtor], l)
        when vd.vname = "__vec_new_eh" ->
          ChangeTo [Call (res, lv, [a1; a2; a3;
                                     mkCast (dropCasts ctor) voidPtrType;
                                     mkCast (dropCasts dtor) voidPtrType],
                          l)]

      (* Call to __throw_setup_dtor. Turn all arguments into integers *)
    | Call (res, Lval(Var tsd, NoOffset),
            [a1; a2; a3; dtor], l) when tsd.vname = "__throw_setup_dtor"
      ->
        ChangeTo [Call(res, Lval(Var tsd, NoOffset),
                       [a1; a2; a3; mkCast (dropCasts dtor) !upointType], l) ]


            (* Setting of vt_array variables *)
    | Set((Var vta, NoOffset), rhs, l) when prefix "vt_array" vta.vname -> begin
        (* See if the right-hand side is a cast of a VTABLE_ENTRY * *)
        let rhs' = dropCasts rhs in
        match typeOf rhs' with
          (* The right-hand side is an array of VTABLEs *)
        | TPtr(TPtr(TComp(ci, _), _), _) when ci.cname = "VTABLE_ENTRY"-> begin
            (match rhs' with
              StartOf (Var a, NoOffset) -> begin
                match a.vtype with
                  TArray(_, Some len, _) ->
                    vt_array_len := Some len
                | _ -> E.s (unimp "Setting vt_array from non-constant length array")
              end
            | _ -> E.s (unimp "Setting vt_array from a non-constant array"));
            SkipChildren
        end

        | TPtr(TComp (ci, _), _) when ci.cname = "VTABLE_ENTRY" ->
            (* Find out the last array length that was used to set vt_array
            * in this function *)
            let len =
              match !vt_array_len with
                Some len -> len
              | None -> E.s (unimp "Trying to use getVTArrayFun but no vt_array_len")
            in
            ChangeTo [Call(Some (Var vta, NoOffset),
                           Lval (var getVTArrayFun.svar),
                           [ rhs'; len ], l)]
        | _ -> SkipChildren
    end

          (* Disguising the vt_array variables into vptr fields *)
    | Set(((Mem host, Field(vptr, NoOffset)) as dest), rhs, l)
        when vptr.fname = "__vptr" -> begin
        (* See if the right-hand side is a cast of a VTABLE_ENTRY * * *)
          let rhs' = dropCasts rhs in
          match typeOf rhs' with
            TPtr(TPtr(TComp (ci, _), _), _) when ci.cname = "VTABLE_ENTRY" ->
              ChangeTo [Call(None,
                             Lval (var setVTArrayFun.svar),
                             [ mkAddrOf dest;
                               rhs' ], l)]
          | _ -> SkipChildren
        end

          (* Reading of caught_object_address *)
    | Set(dest, Lval(Mem(CastE(t, AddrOf(Var caught_object_address,
                                         NoOffset))),
                     NoOffset), l)
        when caught_object_address.vname = "__caught_object_address" ->
          ChangeTo [Call(Some dest, Lval (var getCaughtObjectAddressFun.svar),
                         [ ], l)]

            (* Another way EDG reads caught_object_address *)
    | Set(dest, Lval(Mem(CastE(t, Lval(Var caught_object_address, NoOffset))),
                     NoOffset), l)
        when caught_object_address.vname = "__caught_object_address" ->
          let tmp = makeTempVar !currentFunction ~name:"caught_scalar" t in
          ChangeTo [ Call(Some (var tmp),
                          Lval (var getCaughtObjectAddressFun.svar),
                          [ ], l);
                     Set(dest, Lval(Mem(Lval(var tmp)), NoOffset), l); ]

            (* Calling of a constructor on caught_object_address *)
    | Call(dest, Lval(Var ct, NoOffset), args, l)
        when prefix "__ct__" ct.vname
      -> begin
        (* See if any of the arguments contains an caught_object_address *)
        let newtmp: varinfo option ref = ref None in
        let doOneArg = function
            CastE(t1, CastE(_, Lval(Var caught_object_address, NoOffset)))
          | CastE(t1, Lval(Var caught_object_address, NoOffset))
              when caught_object_address.vname = "__caught_object_address" ->
                (* Make a new temporary *)
                if !newtmp <> None then
                  E.s (unimp "Multiple arguments with __caught_object_address");
                let tmp =
                  makeTempVar !currentFunction ~name:"caught_object" t1 in
                newtmp := Some tmp;
                Lval (var tmp)
          | a -> a
        in
        let args' = List.map doOneArg args in
        (* See if we must initialize the tmp *)
        match !newtmp with
          None -> SkipChildren (* Leave alone *)
        | Some tmp ->
            ChangeTo [ Call(Some (var tmp),
                            Lval (var getCaughtObjectAddressFun.svar),
                            [], l);
                       Call (dest, Lval(Var ct, NoOffset), args', l) ]
      end

    | i -> SkipChildren

  method vinst (i: instr) =
    try self#vinstHelp i with _ (* an error in vinst *) -> SkipChildren

  (* PASS 3. Statements *)
  method private vstmtHelp (s: stmt) =
    (* Look for the conditional test that is part of implementing
     * pointer-to-member calls *)
    match s.skind with
      If(BinOp(Lt,
               CastE(TInt _, Lval ptmLV),
               zr, _), b1, b2, l) when
           (fixPtrMemFun && isZero zr &&
            (match removeOffsetLval ptmLV with
              _, Field(fieldi, NoOffset) -> fieldi.fname = "vtable_field_i"
            | _ -> false))
      ->
        (* We ought to check that lv is really the same with the one stored
         * in ptrMemData *)
        let pData =
          match !ptrMemData with
            Some data -> data
          | _ -> E.s (unimp "Cannot find stored status for call to PTM")
        in
        if debugPtrMem then ignore (E.log "Found ptrmem second step\n");
        (* Get the function pointer from the THEN branch *)
        let fptr =
          match b1.bstmts with
            [t1] -> begin
              match t1.skind with
                Instr [ Set((Var fptr, NoOffset),
                            Lval ptmLV, _)]
                  when (match removeOffsetLval ptmLV with
                         _, Field(field_f, NoOffset)
                             -> field_f.fname = "vtable_field_f"
                        | _ -> false)
                -> fptr
              | _ ->
                  E.s (unimp "THEN branch in ptm is not one instr")
            end
          | _ -> E.s (unimp "THEN branch in ptm conditional is not one stmt")
        in
        (* Drop this whole statement and update the state *)
        pData.ptmStatus <- PTM_FunPtr fptr;
        ChangeTo (mkEmptyStmt ())

    | _ -> DoChildren

  method vstmt (s: stmt) =
    try self#vstmtHelp s with _ (* an error in vstmt *) -> SkipChildren

     (* PASS 3. Globals *)
  method vglob = function
    | GFun (fdec, l) ->
        initPass3Function fdec;
        DoChildren


    | GVar _ -> DoChildren (* To catch the initializer *)

    | GVarDecl _ -> DoChildren

    | GCompTagDecl (ci, l) as g -> begin
        (* If this is the declaration of a class that has RTTI then emit a
         * declaration for the RTTI, so that we can use downcast *)
        try
          let classi = H.find classes ci.cname in
          match classi.tinfovi with
            Some tivi ->
              ChangeTo [ g; GVarDecl (tivi, l) ]
          | _ -> SkipChildren
        with Not_found ->
          SkipChildren
    end
    | g -> SkipChildren
end
let pass3Visitor = new pass3VisitorClass

(***************************************************************************8
 ****************************************************************************
 **
 **    PASS 4
 **
 ** CASTS
 **
 **
 ****************************************************************************
 ***************************************************************************)

    (* Look for downcast in presence of MI: ( C* )p is done as
        if((unsigned long)p != (unsigned long)( P* )0) {
           tmp = ( char* )p - offset_ct;
        } else {
           tmp = ( char* )0;
        }
        ... ( C* )tmp ...
    *)
(* Keep a map indexed by the name of tmp, giving (tmp, p, offset_ct, C) *)
let downcastsMI: (string, (varinfo * exp * int * compinfo)) H.t = H.create 11

let trueThis: varinfo option ref = ref None
let initPass4Function (fd: fundec) =
  currentFunction := fd;
  H.clear downcastsMI;
  trueThis := None


(* let accumInstr: instr list ref = ref [] *)

type castType =
    UpCast of offset
  | EqCast (* Cast between two identical types *)
  | DownCast of varinfo * varinfo * offset (* The infos for the variables
                        * storing the RTTI for the destination and source and
                        * the offset to the vptr *)
  | DownCastError of string
  | PtrToMemCast of exp * exp (* the object being cast and the pointer to the
                        * VTABLE_ENTRY that stores the information for the
                        * cast *)
  | DowncastMI of exp * int * compinfo (* A possible downcast of the
                      * compinfo - offset *)
  | UnknownCast

(* sm: return true if we have information about class 'name' *)
let hasClassInfo (name:string) : bool =
begin
  try
    (ignore (H.find classes name));
    true
  with Not_found ->
    false
end

let checkCast (olde: exp) (oldt: typ) (newt: typ) : castType =
  match unrollTypeDeep newt, unrollTypeDeep oldt with
    TPtr(TComp(newci, _), _), TPtr(TComp(oldci, _), _) ->
      if newci == oldci then
        EqCast
      else begin
        try begin
          let newclassi = H.find classes newci.cname in
          let oldclassi = H.find classes oldci.cname in
          (* Check for upcast. This is safe, but maybe we can even eliminate
          * the cast. *)
          let rec isUpcast
              (srcci: compinfo) (* current source *)
              (destci: compinfo)
              (off: offset) (* offset followed so far from a
              * oldci to srcci *)
              : offset option (* Some if this is a upcast *) =
            (* Get the first field *)
            match srcci.cfields with
              [] -> (* No fields. No upcast *) None
            | f :: _ -> begin
                match f.ftype with
                  TComp(ci', _) ->
                    let off' = addOffset (Field(f, NoOffset)) off in
                    if ci' == destci then
                      (* Got it *) Some off'
                    else (* Did not get it. Keep trying *)
                      isUpcast ci' destci off'
                | _ -> (* Cannot be an upcast *) None
            end
          in
          (* CHECK FOR UPCAST *)
          match isUpcast oldci newci NoOffset with
            Some off -> UpCast off
          | _ -> begin (* Not an upcast. Maybe it is a downcast *)
              match isUpcast newci oldci NoOffset with
                Some _ -> begin
                  try
                    (* Find the destination type info. Might throw Failure *)
                    let destti = findRTTI newclassi in
                    (* Find the source type info. Might throw Failure *)
                    let sourceti = findRTTI oldclassi in
                    let vptr_off =
                      match oldclassi.__vptr with
                        Some off -> off
                      | _ -> raise (Failure "VPTR")
                    in
                    DownCast (destti, sourceti, vptr_off)
                  with Failure s -> DownCastError s
                end
              | _ -> UnknownCast
          end
        end
        with Not_found -> begin
          let aboutWhat:string =
            match (hasClassInfo oldci.cname),
                  (hasClassInfo newci.cname) with
            | true,true -> "(have it for both?!"
            | false,true -> "for source"
            | true,false -> "for destination"
            | false,false -> "for either"
          in
            ignore (warn "Found cast from %s * -> %s * but no class information %s\n"
                         oldci.cname newci.cname aboutWhat);
            UnknownCast
        end
      end
  | _ -> begin (* One or both types are not struct * *)
      (* Maybe it is a cast for an access to pointer to member *)
    match olde, oldt with
      BinOp(PlusPI,
            CastE(TPtr(TInt(IChar, _), _), obj),
            BinOp(MinusA, ptm, Const(CInt64(one, _, _)),
                  TInt(IUInt, _)), _),
      TPtr(TInt(IChar, _), _) when fixPtrMemData && Int64.to_int one = 1 ->
        PtrToMemCast (obj, ptm)

              (* Or maybe it is a cast for a downcast with MI *)
    | Lval(Var tmp, NoOffset),
      TPtr(TInt(IChar, _), _)
          when fixDowncastsMI && H.mem downcastsMI tmp.vname -> begin
            let (_, obj, off, oldci) = H.find downcastsMI tmp.vname in
            H.remove downcastsMI tmp.vname;
            DowncastMI (obj, off, oldci)
          end

              (* Sometimes EDG puts a downcast with MI without first having a
               * conditional ! *)
    | BinOp(MinusPI,
            CastE(TPtr(TInt(IChar, _), _), obj),
            Const(CInt64(off, _, _)), _),
      TPtr(TInt(IChar, _), _) when fixDowncastsMI -> begin
        match unrollTypeDeep (typeOf obj) with
          TPtr(TComp(srcci, _), _) ->
            DowncastMI (obj, Int64.to_int off, srcci)

        | _ -> UnknownCast
      end

    | _ -> UnknownCast
  end

class pass4VisitorClass : cilVisitor = object (self)
  inherit nopCilVisitor

    (* PASS 4. Types *)
  method vtype (t: typ) =
    match t with
      TPtr(t, ap) -> begin
        match unrollType t with
          TComp(ci, ac) -> begin
            (* Now check if we have a pointer to a struct that has a __SO.
             * Turn the pointer into a pointer to the SO. *)
            try
              let cl_data = H.find classes ci.cname in
              match cl_data.soofthis with
                None -> DoChildren
              | Some so_ci -> ChangeTo (TPtr(TComp(so_ci.ci, ac), ap))
            with Not_found -> DoChildren
          end
        | _ -> DoChildren
      end
    | _ -> DoChildren

     (* PASS 4. Expressions. While doing expressions we can accumulate some
      * instructions in accumInstr. *)
  method private vexprHelp (e: exp) =
    match e with
    | CastE(newt, olde) -> begin
        (* First transform the types *)
        let newt' = visitCilType (self :> cilVisitor) newt in
        let olde' = visitCilExpr (self :> cilVisitor) olde in
        (* Intercept the special case when both types involved are pointers
         * to classes *)
        let oldt' = typeOf olde' in
        match checkCast olde' oldt' newt' with
        | EqCast -> ChangeTo olde'
        | UpCast off when fixUpcasts ->
            let olde'' = mkAddrOf (mkMem olde' off) in
            ChangeTo (olde'')
        | DownCast (destti, sourceti, vptr_off) when fixDowncasts ->
            let vptr =  Lval (mkMem olde' vptr_off) in
            (* Make a temporary for the result *)
            let tmp = makeTempVar !currentFunction ~name:"down_cast" newt' in
            self#queueInstr
               [Call(Some (var tmp),
                     Lval (var downCastFun.svar),
                     [ mkCast olde' voidPtrType;
                       vptr;
                       mkAddrOf (var destti);
                       mkAddrOf (var sourceti); ], !currentLoc)];
            ChangeTo (Lval (var tmp))
        | DownCastError why ->
            ignore (warn "Found downcast (%a -> %a) but could not process it: %s\n" d_type oldt' d_type newt' why);
            DoChildren
        | PtrToMemCast (obj, ptm)->
            (* Make a temporary for the result *)
            let tmp =
              makeTempVar !currentFunction ~name:"ptm" newt' in
            self#queueInstr
              [Call(Some (var tmp),
                    Lval (var ptmLookupData.svar),
                    [ mkCast (dropCasts obj) voidPtrType;
                      ptm ], !currentLoc)];
            ChangeTo (Lval (var tmp))

        | DowncastMI (obj, off, srcci) -> begin
(*
            ignore (E.log "found a downcast with MI adjustment\n");
*)
            (* Search for the classinfo *)
            try
              let newclassi =
                match unrollTypeDeep newt' with
                  TPtr(TComp(ni, _), _) -> H.find classes ni.cname
                | _ -> raise Not_found
              in
              let oldclassi = H.find classes srcci.cname in
              (* Now search the parent for a field to child *)
              let szParent =
                try bitsSizeOf (TComp(oldclassi.ci, [])) with _ -> 0 in
              let found =
                try
                  match findSuperAtOffset newclassi off (szParent / 8)
                           (fun _ -> dprintf "checking downcast")
                  with
                    Some _ -> true
                  | None -> false
                with _ -> false
              in
              if found then
                begin
                  (* Found it. Generate the call to __downcast *)
                  try
                    (* Find the destination type info *)
                    let destti = findRTTI newclassi in
                    (* Find the source type info *)
                    let sourceti = findRTTI oldclassi in
                    let vptr_off =
                      match oldclassi.__vptr with
                        Some off -> off
                      | _ -> raise (Failure "VPTR")
                  in
                    let vptr =  Lval (mkMem obj vptr_off) in
                    (* Make a temporary for the result *)
                    let tmp =
                      makeTempVar !currentFunction ~name:"down_cast" newt' in
                    self#queueInstr
                      [Call(Some (var tmp),
                            Lval (var downCastFun.svar),
                            [ mkCast obj voidPtrType;
                              vptr;
                              mkAddrOf (var destti);
                              mkAddrOf (var sourceti); ], !currentLoc)];
                    ChangeTo (Lval (var tmp))
                  with Failure s ->
                    ignore (warn "Found downcast with MI adjustment but failed to process it: %s\n" s);
                    DoChildren
                end else
                DoChildren
            with Not_found -> begin
                ignore (warn "Found downcast with MI adjustment but not classinfo for %a and %s\n"
                          d_type newt' srcci.cname);
                DoChildren
              end
        end
        | _ -> DoChildren
      end
    | _ -> DoChildren


  method vexpr (e: exp) =
    try self#vexprHelp e with _ -> SkipChildren

    (* PASS 4. Lvalues *)
  method vlval (lv: lval) =
    (* Do some simplification because we introduced some AddrOf when removing
     * upcasts. *)
    let postLval = function
        Mem ((AddrOf _) as e), off -> mkMem e off (* This will simplify some *)
      | lv -> lv
    in
    ChangeDoChildrenPost (lv, postLval)


    (* PASS 4. Instructions *)
  method private vinstHelp (i: instr) =
    (* compare a type to the size that was passed in;
     * possibly print warnings; if the length is a multiple of what
     * we expect, but 'nw' is new[], then yield the number of elements
     * to allocate (otherwise yield 1) *)
    let checkSize (ci:compinfo) (ca:attributes) (len:int) (l:location)
                  (nw:varinfo) : int =
    begin
      if (len < 0) then 1 else     (* didn't have len info to check *)

      let got:int = 8 * len in
      let expected:int =
        try (bitsSizeOf (TComp(ci,ca))) with SizeOfError _ -> 0 in
      if (expected <> got) then (
        if ci.cfields == [] then
          E.s (unimp "%a: Missing class definition for %s\n" d_loc l  ci.cname)
        else (
          if ((isNewArray nw.vname) && (got / expected * expected = got)) then
            (* yield the factor *)
            got / expected
          else
            (* complain *)
            E.s (unimp "%a: Unexpected size in call to NEW; expected=%d, got=%d"
                       d_loc l  expected got)
        )
      )
      else
        1    (* factor is 1, if anyone wants to know *)
    end in

    (* given an expression which was passed as the first argument to
     * either vec_new_eh or vec_delete, return an expression which gives
     * the size of a single element of the array *)
    let getElementSize (arrayPtr:exp) : exp =
    begin
      (* have to drop casts because when an array is (con/de)structed inside
       * a (con/de)structor, EDG puts in a bunch of extra casts (new9.cc) *)
      match (dropCasts arrayPtr) with
      | AddrOf(_) as addrOfArray ->
          (* when the array pointer is the address of something, this
           * is a call to new/delete[] for an already-allocated array;
           * the other code below would compute the sizeof the entire
           * array, not a single element (new8.cc) *)
          (SizeOfE (Lval (mkMem addrOfArray (Index(zero,NoOffset)))))

      | _ ->     (* "other code", new/delete[] on heap-allocated data *)
          (SizeOfE (Lval (mkMem (dropCasts arrayPtr) NoOffset)))
    end in

    (* given an integer, yield a CIL literal expression containing it *)
    let literalInt (i:int) : exp =
      Const(CInt64(Int64.of_int i, IUInt, None)) in

    (* given two expressions, yield their product, with type=unsigned *)
    let multiplication (e1:exp) (e2:exp) : exp =
      BinOp(Mult, e1, e2, TInt(IUInt, [])) in

    match i with
      (* Calls to NEW *)
      (* sm: we used to require the target variable name to be called "this",
       * but calls to 'new' outside the constructor violate that *)
      (* sm: we also used to require only one argument, but placement new
       * calls violate that *)
    | Call(Some destLval,   (* sm: generalizing from variable to lvalue *)
           Lval(Var nw, NoOffset), sizeArgExp :: argsTail, l)
        when fixDowncastsMI && isNew nw.vname
      -> begin
        (trace "cxxpp" (dprintf "%a: call to new:@!  %a\n"
                                d_loc l  dn_instr i));

        (* sm: I relaxed the pattern so it could match either a literal
         * size, or a 'sizeof'; distinguish those here.  I had hoped that
         * when the size is 'sizeof' this code wouldn't be needed at all,
         * but apparently it is, though I still don't see why *)
        (* sm: this code is getting a bit contorted, computing this special
         * 'len' code and interpreting it below.. if I understood better
         * what exactly the 'SO' processing was doing I think this code
         * could be factored better *)
        let len:int =
          match sizeArgExp with
          | Const(CInt64(len64, IUInt, _)) ->
              (Int64.to_int len64)     (* literal; extract it *)
          | SizeOf(_) ->
              -1                       (* sizeof; -1 will mean no checks later *)
          | BinOp(Mult, numElts, SizeOf(_), _) ->
              -2                       (* causes special handling in TPtr(_) case *)
          | _ ->
              -3                       (* unrecognized; will bail *)
        in
        if (len = -3) then DoChildren else   (* bail, could be in wrapper code *)

        (* Get the type of the destlv *)
        let destType:typ = (typeOfLval destLval) in
        match destType with
          TPtr(TComp(ci, ca), pa) -> begin
            (* construct the instruction to replace this one (we always
             * make a list b/c that's how the visitors work) *)
            let replacement: instr list =
              (* This must already have been changed to the SO type. Find the
               * real type *)
              try
                let classinfo = H.find classes ci.cname in
                let real =
                  match classinfo.issoof with
                    Some real -> real
                  | _ -> raise Not_found
                in
                  (trace "cxxpp" (dprintf "SO type: %s  real type: %s\n"
                                          ci.cname real.ci.cname));
                  let tThis = TPtr(TComp(real.ci, ca), pa) in
                  (ignore (checkSize real.ci ca len l nw));
                  (* Create a temporary with the real type *)
                  (* sm: why? *)
                  let realtmp = makeTempVar !currentFunction
                      ~name:"trueThis" tThis in
                  trueThis := Some realtmp;
                  [ Call(Some (Var realtmp, NoOffset),
                         Lval(Var nw, NoOffset),
                         ( SizeOfE ( Lval(mkMem (Lval(Var realtmp,
                                                      NoOffset))
                                            NoOffset)) ) :: argsTail, l);
                    Set(destLval,
                        CastE(destType, Lval (Var realtmp,
                                              NoOffset)), l)
                  ]
              with Not_found -> begin (* Not an SO *)
                let factor:int = (checkSize ci ca len l nw) in
                [
                  if (len <> -2) then
                    Call(Some destLval,
                         Lval(Var nw, NoOffset),
                         (multiplication
                           (literalInt factor)    (* testcase for factor <> 1 is new7b.cc *)
                           (SizeOfE ( Lval(mkMem (Lval(destLval))
                                                 NoOffset) ) )
                         ) :: argsTail, l)
                  else
                    (* have to repeat the size construction done below.. this function
                     * needs to be refactored to pull the new-size construction out
                     * to the top, but that's hard without then just repeating the
                     * referent type analysis.. testcase: structs/new7c.cc *)
                    match sizeArgExp with
                    | BinOp(Mult, numElts, SizeOf(_), multType) ->
                        Call(Some destLval,
                             Lval(Var nw, NoOffset),
                             (multiplication
                                numElts
                                (SizeOfE ( Lval(mkMem (Lval(destLval))
                                                      NoOffset) ))
                             ) :: argsTail, l)
                    | _ ->
                        (E.s (bug "pattern fails to match second time?"))
                ]

              end
            in

            (trace "cxxpp" (dprintf "call to new(class) replacement:@!  %a\n"
              (d_list "\n  " dn_instr) replacement));
            ChangeTo(replacement)
          end

        | TPtr(referent,_) -> begin
            (* if it isn't a pointer to a struct, then we're allocating
             * some primitive type like 'new int' or 'new char*[]'; fix
             * the call by rewriting it to use sizeof( *dest ) *)

            let replacement:instr =
              if (len <> -2) then (   (* literal size *)
                (* first, what is size of the elements being allocated? *)
                let eltSize:int = try
                  (bitsSizeOf referent) / 8
                with SizeOfError _ ->
                  (E.s (unimp "In call to new, unknown size of type %a\n"
                              d_type referent))
                in

                (* divide out that size; this gets us the # of elements
                 * allocated in the case of 'new[]', or just '1' for
                 * simple 'new' *)
                let numElts:int = len / eltSize in
                if (numElts * eltSize <> len) then
                  (E.s (unimp "In call to new, length %d not a multiple of %d\n"
                              len eltSize));

                (* now write the call, where the size is a multiplication
                 * involving 'sizeof', so it will expand properly when CCured
                 * makes some pointers wider *)
                Call(Some destLval,
                          Lval(Var nw, NoOffset),
                          (multiplication
                            (literalInt numElts)
                            (SizeOfE ( Lval(mkMem (Lval(destLval))
                                                  NoOffset)))
                          ) :: argsTail, l)
              )

              else (                  (* size computed with multiplication *)
                (* this happens whenever you ask for 'new[]' but the argument
                 * is not a literal element count; EDG's original behavior
                 * was to make the element size a literal, but I've since
                 * changed it to at least give us 'sizeof(eltType)'; testcase
                 * is structs/new12.cc *)
                match sizeArgExp with
                | BinOp(Mult, numElts, SizeOf(_), multType) ->
                    (* write the call, replacing sizeof(type) with sizeof(exp) *)
                    Call(Some destLval,
                         Lval(Var nw, NoOffset),
                         (multiplication
                            numElts
                            (SizeOfE ( Lval(mkMem (Lval(destLval))
                                                  NoOffset) ))
                         ) :: argsTail, l)
                | _ ->
                    (E.s (bug "pattern fails to match second time?"))
              )
            in

            (trace "cxxpp" (dprintf "call to new(primitive) replacement:@!  %a\n"
                                    dn_instr replacement));
            ChangeTo([replacement])
          end

        | _ ->
            E.s (unimp "Destination of NEW is not a pointer\n")
      end

    (* call to new[] *)
    (* this code has some of the extra checking mechanism from above,
     * but I don't actually use it.. *)
    | Call(Some destLval,
           Lval(Var nw, NoOffset),
           [
             arrayPtr;          (* ptr to existing array; usually NULL *)
             numElts;           (* # of elts to allocate; we ignore *)
             Const(CInt64(eltSize64, IUInt, _));   (* size of each elt. in bytes *)
             ctorPtr; dtorPtr   (* ctor/dtor ptrs; we ignore *)
           ], l) when (nw.vname = "__vec_new_eh") ->
      begin
        (trace "cxxpp" (dprintf "%a: call to new[]: %a\n"
                                d_loc l  dn_instr i));
        let len:int = (Int64.to_int eltSize64) in

        (* Get the type of the destlv *)
        let destType:typ = (typeOfLval destLval) in
        match destType with
          TPtr(TComp(ci, ca), pa) -> begin
            (ignore (checkSize ci ca len l nw));       (* check len against what we expect *)
            let replacement:instr =
              Call(Some destLval,
                   Lval(Var nw, NoOffset),
                   [
                     arrayPtr; numElts;      (* same first 2 args *)
                     (* "sizeof(*destv)" *)
                     (SizeOfE (Lval(mkMem (Lval(destLval)) NoOffset)) );
                     ctorPtr; dtorPtr        (* same last 2 args *)
                   ], l) in
            (trace "cxxpp" (dprintf "call to new[] replacement: %a\n"
                                    dn_instr replacement));
            ChangeTo([replacement])
          end

        | TPtr(TInt(_),_) -> DoChildren      (* no need to rewrite alloc'n of ints *)
        | _ -> E.s (unimp "Destination of NEW is not a pointer to struct or int\n")
      end

    (* call to new[] for stack-allocated obj; minimal checking *)
    | Call(None,      (* no destination b/c storage already allocated *)
           Lval(Var nw, NoOffset),
           [
             arrayPtr;          (* ptr to existing array *)
             numElts;           (* # of elts to allocate; we ignore *)
             Const(CInt64(eltSize64, IUInt, _));   (* literal size *)
             ctorPtr; dtorPtr   (* ctor/dtor ptrs; we ignore *)
           ], l) when (nw.vname = "__vec_new_eh") ->
      begin
        (trace "cxxpp" (dprintf "%a: call to existing-storage new[]: %a\n"
                                d_loc l  dn_instr i));
        ChangeTo([
          Call(None,
               Lval(Var nw, NoOffset),
               [
                 arrayPtr; numElts;
                 (getElementSize arrayPtr);
                 ctorPtr; dtorPtr
               ], l)
        ])
      end

    (* call to delete[]; minimal checking *)
    | Call(None,
           Lval(Var del, NoOffset),
           [ arrayPtr; numElts;
             (* we must match a literal here, to avoid rewriting the call
              * to vec_delete in the wrapper! *)
             Const(CInt64(eltSize64, IUInt, _));
             dtorPtr; deletePtr; isTwo ],
           l) when (del.vname = "__vec_delete") ->
        (trace "cxxpp" (dprintf "%a: call to delete[]: %a\n"
                                d_loc l  dn_instr i));
        ChangeTo([
          Call(None,
               Lval(Var del, NoOffset),
               [ arrayPtr; numElts;
                 (getElementSize arrayPtr);
                 dtorPtr; deletePtr; isTwo ],
               l)
        ])

    | Set(((Var _, NoOffset) as dest),
          AddrOf (Mem (Lval (Var this, NoOffset)), Field(vbase, NoOffset)),
          l)
        when this.vname = "this" && prefix "__v_" vbase.fname
      -> begin
        match !trueThis with
          None -> DoChildren (* Does not have an SO *)
        | Some tThis ->
            ChangeTo
              [ Call(Some (Var tThis, NoOffset),
                     Lval (var trustedCastFun.svar),
                     [ Lval(Var this, NoOffset) ], l);
                Set (dest,
                     AddrOf (mkMem (Lval (Var tThis, NoOffset))
                               (Field(vbase, NoOffset))), l) ]
      end


    | i ->
        let postInstr il =
          (* Now process the instructions *)
          let postProcessPass4 (i: instr) : instr =
            match i with
              (* We need to intercept casts that are implicit in the
              * return type of functions *)
            | Call (Some dest, func, args, l) when fixDowncasts -> begin
                let rt, _, _, _ = splitFunctionType (typeOf func) in
                match checkCast zero rt (typeOfLval dest) with
                  DownCast (destti, sourceti, vptr_off) when fixDowncasts ->
                    (* Make a temporary for the result of the function *)
                    let tmp = makeTempVar !currentFunction ~name:"down_cast" rt in
                    let vptr =  Lval (mkMem (Lval(var tmp)) vptr_off) in
                    (* Accumulate the original call *)
                    self#queueInstr
                       [Call(Some (var tmp), func, args, l)];
                    (* And return the call to the downCast *)
                    (Call(Some dest,
                          Lval (var downCastFun.svar),
                          [ mkCast (Lval (var tmp)) voidPtrType;
                            vptr;
                            mkAddrOf (var destti);
                            mkAddrOf (var sourceti); ], l))

                | DownCastError why ->
                    ignore (warn "Found downcast in function call but cannot process it: %s\n"
                              why);
                    i
                | _ -> i
            end
            | _ -> i
          in
          List.map postProcessPass4 il
        in
        ChangeDoChildrenPost ([i], postInstr)

  method vinst (i: instr) =
    try
      self#vinstHelp i
    with _ -> SkipChildren

     (* PASS 4. Statements *)
  method private stmtHelp (s: stmt) =
    match s.skind with
      If(BinOp(Ne, CastE(TInt _, obj),
               CastE(TInt _, CastE(TPtr(TComp(classi, _), _),
                                   ((Const _) as zr))), _),
         tblk, fblk, l) when isZero zr -> begin
           try
             (* Check the branches *)
             let (tmpvar: varinfo), (off: int) =
               match tblk.bstmts, fblk.bstmts with
                 [setoff], [ setzero ] -> begin
                   match setoff.skind, setzero.skind with
                     Instr [Set((Var tmpvar, NoOffset),
                                BinOp(MinusPI,
                                      CastE(TPtr(TInt(IChar, _), _),
                                            obj'),
                                      Const(CInt64(off, _, _)), _), _)],

                     Instr [Set((Var tmpvar',
                                 NoOffset), zr, _)]
                       when isZero zr && tmpvar' == tmpvar ->
                       tmpvar, Int64.to_int off
                   | _ -> raise (Failure "not set")
                 end
               | _ -> raise (Failure "")
             in
             (* Remember the conditional *)
             H.add downcastsMI tmpvar.vname (tmpvar, obj, off, classi);
             (* And drop the instructions *)
             s.skind <- Instr [];
             SkipChildren
           with Failure _ -> DoChildren
         end

    | _ -> DoChildren

  method vstmt (s: stmt) =
    try self#stmtHelp s with _ -> DoChildren

     (* PASS 4. Globals *)
  method vglob = function
    | GFun (fdec, l) ->
        initPass4Function fdec;
        DoChildren

    | g -> DoChildren

     (* PASS 4. Initializers *)
  method vinit (varg: varinfo) (off: offset) (i: init) =
    match i with
      (* Prevent the vtype to touch the casts to objects with SO *)
      SingleInit (CastE(TInt _,
                        AddrOf (Mem (CastE(_, zero)),
                                Field _))) when isZero zero -> SkipChildren
      (* And another form that occurs with negative sign *)
    | SingleInit (UnOp(Neg,
                        CastE(TInt _,
                              AddrOf (Mem (CastE(_, zero)),
                                      Field _)), _))
        when isZero zero -> SkipChildren
    | _ -> DoChildren

end
let pass4Visitor = new pass4VisitorClass


(***************************************************************************8
 ***************************************************************************
 **
 **              MAIN
 **
 ***************************************************************************
 ****************************************************************************)
let cxxFile (f: file) =
  initCheckVMTable ();
  initPureVirtuals ();

  (** Pass 1. Revert the globals **)
  theFile := [];
  if !Cilutil.printStages then
    ignore (E.log "CXXPP: Stage 1\n");
  (* Add the meta data *)
  createMetadataTypes ();

  (trace "sm" (dprintf "calling initPass1\n"));
  initPass1 ();
  iterGlobals f (fun g -> try pass1 g with _ -> pushGlobal g);
  f.globals <- !theFile; (* Save the file (in reverse order) *)

  (trace "sm" (dprintf "calling fillInEmptyCompinfo\n"));
  fillInEmptyCompinfo ();

  (** Pass 2. Apply the renaming of metadata *)
  if !Cilutil.printStages then
    ignore (E.log "CXXPP: Stage 2\n");
  visitCilFile pass2Visitor f;

  renameRTTI ();

  if !doDumpClasses then
    dumpClasses ();

(*
  dumpClasses ();
*)

  (** Pass 3, in reverse order. Revert the globals *)


  theFile := [];
  if !Cilutil.printStages then
    ignore (E.log "CXXPP: Stage 3\n");
  let pass3 (g: global) =
    let g' = visitCilGlobal pass3Visitor g in
    theFile := !theFileAfter @ g' @ !theFile;
    theFileAfter := []
  in
  iterGlobals f pass3;

  (* Set the globals back *)
  f.globals <- !theFile;

  (* Now PASS 4 *)
  theFile := [];
  if !Cilutil.printStages then
    ignore (E.log "CXXPP: Stage 4\n");
  let pass4 (g: global) =
    let g' = visitCilGlobal pass4Visitor g in
    theFile := g' @ !theFile
  in
  iterGlobals f pass4;

  (* Now scan the virtual tables and find the overrides *)
  trace "vtable"
    (dprintf "Adding overrides connections between virtual methods\n");
  H.iter
    (fun _ classi -> (* For each class *)
      (* If there are duplicate main table entries then match them with the
       * main one *)
      List.iter (fun dupl -> matchVTable dupl true)
                classi.duplicate_main_vtables;
      (* For each virtual table, match it with the corresponding parent *)
      List.iter (fun vti -> matchVTable vti false)  classi.vtables)
    classes;

  (* If the checking of vmLookup is enabled then add the table now *)
  if checkVMLookup then
    theFile := packCheckVMTable () :: !theFile;

  (* Now add the pure virtual bodies *)
  (trace "vtable" (dprintf "adding pure virtual function bodies\n"));
  addPureVirtualBodies ();

  (trace "vtable" (dprintf "finishing up stage 4\n"));
  f.globals <- List.rev !theFile;
  H.clear classes;
  H.clear rttiToClass;
  H.clear baseClassToClass;

  f
