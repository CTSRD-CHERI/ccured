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

(* We will accumulate the marked globals in here *)
let theFile: global list ref = ref []
    
let currentFunction: fundec ref = ref Cil.dummyFunDec

let useAutoRtti = true

(* If false generate code to ensure that the run-time checks just print an 
 * error message instead of aborting. *)
let alwaysStopOnError = ref false

let failIsTerse = ref false

let logNonPointers = ref false

(** Annotate the output for verification. *)
let doAnnotateOutput = ref false 

(* We keep track of all functions that are declared or defined *)
type funinfo = Declared of varinfo | Defined of fundec

(* All functions indexed by name *)
let allFunctions: (string, funinfo) H.t = H.create 113

(* All compinfo indexed by name *)
let allCompinfo: (string, compinfo * location) H.t = H.create 113


(* Store all the functions indexed by the name before alpha conversion *)
let allFunctionBasenames: (string, funinfo) H.t = H.create 113

(* A list of functions that were called in the file *)
let calledFunctions: (string, varinfo) H.t = H.create 113

(* Apply a function to a function declaration or definition *)
let applyToFunctionMemory: (string, (funinfo -> unit)) H.t = H.create 13    

let applyToFunctionCommon (n: string) (f: funinfo -> unit) = 
  (* Memorize this action *)
  H.add applyToFunctionMemory n f;
  (* Now apply it to already defined functions *)
  let all = H.find_all allFunctionBasenames n in
  List.iter (fun one -> f one) all


let applyToFunction (n: string) (f: varinfo -> unit) = 
  applyToFunctionCommon n 
    (function Declared fvi -> f fvi | Defined fdec -> f fdec.svar)


let applyToFunctionDef (n: string) (f: fundec -> unit) = 
  applyToFunctionCommon n 
    (function Declared fvi -> () | Defined fdec -> f fdec)



let alreadyDefinedFunction n = 
  try
    match H.find allFunctions n with 
      Defined _ -> true
    | _ -> false
  with Not_found -> false

let getFunctionTypeAttributes (e: exp) = 
  match unrollType (typeOf e) with 
    TFun(_, _, _, fa) -> fa
  | _ ->  E.s (bug "getFunctionTypeAttribute: not a function type")

let addFunctionTypeAttribute (a: attribute) (vi: varinfo)  = 
  match vi.vtype with 
    TFun(rt, args, isva, fa) -> vi.vtype <- TFun(rt, args, isva, 
                                                addAttribute a fa)
  | _ -> E.s (bug "addFunctionTypeAttribute: not a function type")

let registerFunction (fi: funinfo) = 
  let fvi = match fi with Declared fvi -> fvi | Defined fdec -> fdec.svar in
  let lookup = Alpha.getAlphaPrefix fvi.vname in
  (* ignore (E.log "Registering function %s\n" fvi.vname); *)
  (* See if it has the format attribute *)

  let fl = H.find_all applyToFunctionMemory lookup in
  List.iter (fun f -> f fi) fl;
  H.add allFunctions fvi.vname fi;
  H.add allFunctionBasenames lookup fi
    
let matchSuffix (lookingfor: string) (lookin: string) = 
  let inl = String.length lookin in
  let forl = String.length lookingfor in
  inl >= forl && String.sub lookin (inl - forl) forl = lookingfor


let allGlobals: (string, location option) H.t = H.create 113
let registerGlobalDefinition (v: varinfo) (loc:location) : unit = 
  try 
    let oldEntry = H.find allGlobals v.vname in
    if oldEntry <> None then
      ignore (warn "registerGlobalDefinition called twice on %s." v.vname);
    H.replace allGlobals v.vname (Some loc)
  with Not_found ->
    H.add allGlobals v.vname (Some loc)

let registerGlobalDeclaration (v: varinfo) : unit = 
  try ignore (H.find allGlobals v.vname)
  with Not_found ->
    H.add allGlobals v.vname None


let isImported (vn: string) = 
  try
    let defn = H.find allGlobals vn in
    defn = None (* if defn is None, then imported (no definition) *)
  with Not_found ->
    if Ccutil.hasPrefix "__globinit_" vn then
      false
    else begin
      ignore (E.warn "isImported for %s, which is not even declared\n" vn);
      true (* pretend it is imported *)
    end





let findFunc ~(name:string) ~(neededby:string) =
  try
    match H.find allFunctions name with 
      Declared vi -> vi
    | Defined fdec -> fdec.svar
  with Not_found ->
    E.s (error "Can't find declaration of %s needed by %s." 
	   name neededby)




(**** Keep track of the extends relation ship *)
type extension = 
    { ex_name: string; (* A canonical name of the form Sfoo or Tfoo *)
      mutable ex_type: exkind;
      (* The parent along with the location of the pragma that declares it. 
       * voidExtension is the root  *)
      mutable ex_parent: (extension * location) option; 
      mutable ex_children: (string, extension) H.t;
      mutable ex_nr_children: int;
      (* Store here the index into the RTTI array. 0 is reserved for scalars 
       * and 1 for void. *)
      mutable ex_index: int;
    } 

and exkind = 
    (* Pointer to ... *)
    ExType of typeinfo
  | ExComp of compinfo
  | ExVoid
  | ExAuto of typ * N.node (* An automatically generated extension for a 
                  * given type. Keep also the node pointing to that type. *)
      (* !upointType.  Scalars of other sizes are ExNonPointers *)
  | ExScalar
      (* Anything larger than a pointer. Used in tagged unions. *)
  | ExNonPointer of typ

let scalarExtension = { ex_name = "scalar"; ex_type = ExScalar;
                        ex_parent = None; ex_children = H.create 7;
                        ex_nr_children = 0;
                        ex_index = 0; }

let voidExtension = { ex_name = "void"; ex_type = ExVoid; 
                      ex_parent = None; (* will extend scalarExtension *)
                      ex_children = H.create 29;
                      ex_nr_children = 0;
                      ex_index = 1; }

let extensions: (string, extension) H.t = H.create 29

(** Remember all the typeinfo and compinfos *)
let possibleExtensible: (string, exkind) H.t = H.create 117

(*** We keep track of some autoamtically-generated extensions *)
let autoExtensions: (typsig, extension) H.t = H.create 13
let autoNonPtrExtensions: (typsig, extension) H.t = H.create 13

(** Call this function for all DEFINITIONS of GCompTag and GType to populate 
 * the extension information with the real info *)
let registerCompinfo (ci: compinfo) (l: location) = 
  H.replace allCompinfo ci.cname (ci, l);
  let n = "S" ^ ci.cname in
  try
    let ex = H.find extensions n in
    ex.ex_type <- ExComp ci
  with Not_found -> 
    H.add possibleExtensible n (ExComp ci)


let registerTypeinfo (ti: typeinfo) = 
  let n = "T" ^ ti.tname in
  try
    let ex = H.find extensions n in
    ex.ex_type <- ExType ti
  with Not_found -> 
    H.add possibleExtensible n (ExType ti)

(* Returns true if this type should use ExScalar.  Ignores signed/unsigned *)
let isPtrSizedInt t =
  isIntegralType t &&  bitsSizeOf t = bitsSizeOf !upointType

let noNewExtensions = ref false
let lastExtensionIndex = ref voidExtension.ex_index
let mkExtension ?(subtype_of_void=true) (name: string) : extension = 
  let ex = 
    try
      H.find extensions name 
    with Not_found -> begin
      if !noNewExtensions then
        E.s (bug "called mkExtension after the RTTI array was generated.");
      incr lastExtensionIndex;
      let ex = { ex_name = name; 
                 ex_type = ExVoid; (* We'll fill in later *)
                 ex_parent = None;
                 ex_children = H.create 29;
                 ex_nr_children = 0;
                 ex_index = !lastExtensionIndex; }
      in
      H.add extensions name ex;
      if subtype_of_void then begin
        (* This is a child of void for now *)
        H.add voidExtension.ex_children ex.ex_name ex;
        voidExtension.ex_nr_children <- 1 + voidExtension.ex_nr_children;
        ex.ex_parent <- Some (voidExtension, locUnknown);
      end;
      ex
    end
  in
  (* See if we have seen the type already *)
  (try
    ex.ex_type <- H.find possibleExtensible ex.ex_name;
    H.remove possibleExtensible ex.ex_name
  with Not_found -> ());
  ex


let mkAutoExtension (t: typ) (n: N.node) 
                    (newedges: N.edge list ref option)
                    (l: location) : extension = 
  let ts = typeSigWithAttrs (fun _ -> []) t in
  try
    let oldex = H.find autoExtensions ts in
    (* Now see if we must add an edge *)
    (match newedges, oldex.ex_type with 
      Some where, ExAuto (_, oldn) -> 
        let edge = N.addEdge n oldn (N.ECast N.EEK_rtti) (Some l) in
        where := edge :: !where
                           
    | _ -> ());
    oldex

  with Not_found -> begin
    (* Construct the name of the extension based on the type sig *)
    
    let ename = "AutoRTTI:" ^ Pretty.sprint 80 (d_typsig () ts) in
    let ex = mkExtension  ename in
    ex.ex_type <- ExAuto (t, n);
    H.add autoExtensions ts ex;
    ex
  end

(** Given a type find its extension information name. Return "" if the type 
  * cannot have extension information. *)
let rec extensionName 
    (auto: (N.node * N.edge list ref option * location) option) 
    (t: typ) : string * exkind = 
  match t with 
    TVoid _ -> "void", ExVoid
  | TComp (ci, _) -> "S" ^ ci.cname, ExComp ci
  | TNamed(ti, _) -> begin
      match ti.ttype with 
        TComp _ | TNamed _ -> extensionName auto ti.ttype
      | _ -> "T" ^ ti.tname, ExType ti
  end
  | _ -> begin
      match auto with 
        Some (n, newedges, l) -> 
          let ex = mkAutoExtension t n newedges l in
          ex.ex_name, ex.ex_type
      | _ -> "", ExVoid
  end

  

let typeCanHaveRtti (t: typ) : bool * string = 
  let xname, _ = extensionName None t in
  if xname = "" then 
    false, "not an extensible type"
  else if xname = "void" then 
    true, "void"
  else 
    (try
      let ex = H.find extensions xname in
      if ex.ex_nr_children = 0 then 
        false, "leaf in the class hierarchy"
      else 
        true, "ok"
    with Not_found -> 
      false, "not in the class hierarchy")

(* Add extends pragma *)
let processPragma (a: attribute) (l: location) = 
  match a with 
    Attr("ccured_extends", [AStr child; AStr parent]) -> begin
      let ch_ex = mkExtension child in
      let p_ex = mkExtension parent in
      match ch_ex.ex_parent with 
        Some (ch_p, _) when ch_p == p_ex ->  () (* Duplicate pragma *) 
      | Some (ch_p, _) when ch_p == voidExtension -> 
          (* Remove from the previous parent *)
          H.remove ch_p.ex_children ch_ex.ex_name;
          ch_p.ex_nr_children <- ch_p.ex_nr_children - 1;
          (* Add to the new parent *)
          H.add p_ex.ex_children ch_ex.ex_name ch_ex;
          p_ex.ex_nr_children <- p_ex.ex_nr_children - 1;
          ch_ex.ex_parent <- Some (p_ex, l)

      | Some (ch_p, l) -> 
          E.s (error "Type %s is already extended by %s at %a\n" 
                 child ch_p.ex_name d_loc l);
               
      | None -> 
          E.s (error "Type %s is the root of the extension hierarchy\n" 
                 child)
    end
  | Attr("ccured_extends", _) -> E.s (error "Invalid ccured_extends pragma")

  | _ -> ()

(** Find the list of children *)
let listOfChildren (ex: extension) = 
  let res = ref [] in
  H.iter (fun n c -> res := c :: !res) ex.ex_children;
  !res

(** Dump the extension hierarchy *)
let extensionHierarchyAlreadyPrinted = ref false
let dumpExtensionHierarchy () = 
  if not !extensionHierarchyAlreadyPrinted then  begin
    let rec d_subtree () (ex: extension) = 
      dprintf "%s:@!  @[%a@]@!"
        ex.ex_name (docList ~sep:line (d_subtree ())) (listOfChildren ex)
    in
    ignore (E.log "The extension hierarchy is:@! @[%a@]\n" 
              d_subtree voidExtension);
    extensionHierarchyAlreadyPrinted := true
  end


(** Make the rttiArray element type *)
let rttiElementCompinfo = 
  let ci = mkCompInfo true "RTTI_ELEMENT"
      (fun _ -> [ ("index", intType, None, [], locUnknown); 
                          (* The index of this entry, 
                           * for debugging *)
                  ("name", charPtrType, None, [], locUnknown); 
                          (* The name of the type *)
                  ("parentDelta", intType, None, [], locUnknown) 
                          (* The difference 
                           * between the index of 
                           * the parent and this 
                           * one. This is the only 
                           * entry that matters *)
                ]) [] in
  ci

let rttiElementType = TComp(rttiElementCompinfo, [])
let rttiType = TPtr(rttiElementType, [])

(** Generate the RTTI data structure *)
let rttiArray = (* Remember here the varinfo *)
  let arrayAttrs = if !msvcMode then [] else [Attr("unused", [])] in
  let t = TArray(rttiElementType, 
                 None,   (* Fill in the length later. *)
		 arrayAttrs) in
  let rttiArray = makeGlobalVar "RTTI_ARRAY" t in
  rttiArray.vstorage <- Static;
  rttiArray

(* A global representing the definition of the RTTI array
   that should be added to the file.  After curing, call generateRTTI
   to populate the initializer of this global. *)
let rttiInitializer = {init=None}
let rttiArrayDefn = GVar(rttiArray, rttiInitializer, locUnknown)

(** We will generate an array of integers, with one entry corresponding to 
  * each extensible type. That entry contains the index of the entry 
  * corresponding to the parent. The first entry is always for the void type *)
let generateRTTI () : unit = 
  (* Fill in the array length. *)
  let arrayAttrs = if !msvcMode then [] else [Attr("unused", [])] in
  let t = TArray(rttiElementType, 
                 Some (integer (1 + !lastExtensionIndex)),
		 arrayAttrs) in
  rttiArray.vtype <- t;
  (* Prohibit any changes to the length of the rtti array, in case we
     accidentally call checkRttiCast after generateRTTI. *)
  noNewExtensions := true;
  let indexFld, nameFld, parentDeltaFld = 
    match rttiElementCompinfo.cfields with 
      f1 :: f2 :: f3 :: [] -> f1, f2, f3
    | _ -> E.s (bug "Error creating the fields")
  in
  (* Create the contents, as an array *)
  let contents : (offset * init) array = 
    Array.make (1 + !lastExtensionIndex) (NoOffset, SingleInit mone) in
  H.iter 
    (fun _ ex -> 
      contents.(ex.ex_index) <- 
         (Index(integer ex.ex_index, NoOffset),
          CompoundInit(rttiElementType,
                       [ (Field(indexFld, NoOffset), 
                          SingleInit (integer ex.ex_index));
                         (Field(nameFld, NoOffset), 
                          SingleInit (mkString ex.ex_name));
                         (Field(parentDeltaFld, NoOffset),
                          SingleInit
                            ((match ex.ex_parent with 
                              None -> zero
                            | Some (p, _) -> 
                                integer (p.ex_index - ex.ex_index)))) ]))
           ) 
    extensions;
  rttiInitializer.init <- Some (CompoundInit(t, Array.to_list contents));
  ()

(** For generating annotations in verify.ml *)
let getAllExtensions () : exkind array  = 
  if not !noNewExtensions then begin
    E.s (bug "call getAllExtensions only after curing.")
  end;
  let kindarray : exkind array = 
    Array.make (1 + !lastExtensionIndex) ExScalar in
  H.iter 
    (fun _ ex -> kindarray.(ex.ex_index) <- ex.ex_type)
    extensions;
  kindarray
  

let mkRttiExp (ex: extension) = 
  if ex.ex_index < 0 then 
    E.s (bug "mkRTTI for %s\n" ex.ex_name);
  AddrOf (Var rttiArray, Index(integer ex.ex_index, NoOffset))


let exForPointerType ~(newedges: N.edge list ref option) issrc t isrtti
  (l: location) : extension = 
  let getOrMakeExtension (bt: typ) (n: N.node) : extension = 
    let arg = if useAutoRtti then Some (n, newedges, l) else None in
    let xname, xk = extensionName arg bt in
    if xname = "" then 
      E.s (errorLoc l "Cast %s type %a that cannot have RTTI (non-extensible type).\n"
             (if issrc then "to RTTI from " else "from RTTI to") 
             (printType N.ccuredInferPrinter) bt);
    try
      H.find extensions xname
    with Not_found -> begin
      (* We did not find one. Make one that extends void, but only if this 
       * one is not already RTTI *)
      if isrtti then 
        E.s (errorLoc l "Cast %s type %a that cannot have RTTI (not in the class hierarchy)\n"
               (if issrc then "to RTTI from" else "from RTTI to")
               d_type t);
      let ex = mkExtension xname in
      ex.ex_type <- xk;
      ex
    end
  in
  match unrollType t with 
    TPtr(bt, a) -> begin
      let nd = 
        if newedges = None then
          N.dummyNode
        else begin
          match N.nodeOfAttrlist a with 
            Some n -> n
          | None-> E.s (bug "checkRttiCast on pointer type without a node (%a)"
                          d_type t)
        end
      in
      getOrMakeExtension bt nd
    end
  | _ -> 
      if isPtrSizedInt t then
        scalarExtension
      else E.s (bug "checkRttiCast on non-pointer type (%a)" d_type t)



(* Check a cast in which at least one of the types is RTTI. Pass the pointer 
 * types. Returns whether the cast must be checked at run-time. This has the 
 * side-effect that it makes the extension information for both types. Return 
 * also any newly created edges for auto rtti (only if auto was true) *)
let checkRttiCast ~(newedges: N.edge list ref option) 
                   (t1: typ) (isrtti1: bool) 
                   (t2: typ) (isrtti2: bool) 
                   (l: location) : exp * exp * bool = 
  let x1 = exForPointerType ~newedges true t1 isrtti1 l in
  let x2 = exForPointerType ~newedges false t2 isrtti2 l in
  
  let rec checkExtends (child: extension) (from: extension) = 
    if child == from then true else
    match child.ex_parent with 
      None -> false
    | Some (parent, _) -> checkExtends parent from
  in
  let isdowncast = 
    if checkExtends x1 x2 then 
      false
    else if not isrtti1 then begin
      E.s (errorLoc l
             "SAFE pointer (%a) is cast to RTTI pointer (%a) that it does not extend" d_type t1 d_type t2)
    end else begin
      (* Maybe x2 extends x1 (a downcast) *)
      if checkExtends x2 x1 then 
        true
      else begin
        dumpExtensionHierarchy ();
        E.s (errorLoc l 
               "Cast from RTTI is neither an upcast nor a downcast\nFrom %a(%s)\nTo   %a(%s)\n" d_type t1 x1.ex_name d_type t2 x2.ex_name)
      end
    end
  in
  mkRttiExp x1, mkRttiExp x2, isdowncast


let getVoidRtti () = 
  mkRttiExp voidExtension

let getScalarRtti () = 
  mkRttiExp scalarExtension

(** Generate all extends relationships not involving void *)
let allExtendsRelationships () : (typ * typ * location) list = 
 let res = ref [] in
 let mkType = function
    ExType ti -> TNamed (ti, [])
  | ExComp ci -> TComp(ci, [])
  | ExVoid -> voidType
  | ExAuto (t, _) -> t
  | ExScalar -> E.s (E.bug "allExtendsRelationShips: scalar")
  | ExNonPointer _ -> E.s (E.bug "allExtendsRelationShips: non-pointer")
 in
 H.iter (fun _ ex -> 
     match ex.ex_parent with 
       Some (p, l) when p.ex_index > voidExtension.ex_index -> 
         res := (mkType ex.ex_type, mkType p.ex_type, l) :: !res

     | _ -> ()) extensions;
 !res


(** Register a type that is used in a tagged union, and that
  therefore needs an rtti tag even though it may not be a pointer.
  This method does not draw edges, so do that elsewhere.*)
let registerRttiType (t: typ) : unit = 
  if isPointerType t || isPtrSizedInt t then begin
    let newedges = Some (ref []) in
    ignore(exForPointerType ~newedges true t false !currentLoc)
  end
  else begin
    (* Non-pointer Extensions are used in tagged unions.
       We don't need edges, since there are no pointers here and we don't cast
       between two different non-pointer fields. *)
    (match unrollType t with
       TPtr _ | TFun _ | TNamed _ -> 
         E.s (bug "bad type passed to registerRttiType.")
     | _ -> ());
    let ts = typeSigWithAttrs (fun _ -> []) t in
    try
      ignore (H.find autoNonPtrExtensions ts)
    with Not_found -> begin
      let ename = "NonPointerRTTI:" ^ Pretty.sprint 80 (d_typsig () ts) in
      (* ignore (E.log "creating an extension for \"%s\"\n" ename); *)
      let ex = mkExtension ~subtype_of_void:false ename in
      ex.ex_type <- ExNonPointer t;
      H.add autoNonPtrExtensions ts ex;
    end
  end



let getRttiForType (t: typ) : exp =
  let ex =
    if isPointerType t || isPtrSizedInt t then begin
      (* This may create a new ExAuto extension, if the base type of
         t was changed during curing.  But we don't add edges. *)
      exForPointerType ~newedges:None true t false !currentLoc
    end else begin (* ExNonPointer *)
      try 
        let ts = typeSigWithAttrs (fun _ -> []) t in
        H.find autoNonPtrExtensions ts
      with Not_found ->
        E.s (bug "type %a not registered." d_type t)
    end
  in
  mkRttiExp ex


let shallowMangling = ref false


let init () = 
  H.clear allFunctions;
  H.clear allCompinfo;
  H.clear allFunctionBasenames;
  H.clear applyToFunctionMemory;
  H.clear calledFunctions;
  H.clear extensions; 

  (* void* is a subtype of int *)
  assert (scalarExtension.ex_nr_children == 0);
  H.add scalarExtension.ex_children voidExtension.ex_name voidExtension;
  scalarExtension.ex_nr_children <- 1;
  voidExtension.ex_parent <- Some (scalarExtension, locUnknown);
  
  H.add extensions voidExtension.ex_name voidExtension;
  H.add extensions scalarExtension.ex_name scalarExtension;
  H.clear possibleExtensible;
  (* H.clear allGlobals; *)
  lastExtensionIndex := voidExtension.ex_index;
  extensionHierarchyAlreadyPrinted := false;
  theFile := []

