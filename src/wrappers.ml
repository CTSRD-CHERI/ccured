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

let debugWrappers = false

(* Check if a type has pointers *)
let hasPointers (t: typ) =
  existsType
    (function TPtr _ -> ExistsTrue | _ -> ExistsMaybe)
    t


(* maps functions to wrappers *)
let ccuredWrappedBy: (string, string) H.t = H.create 15

(* a list of wrappers *)
let ccuredWrappers: (string, unit) H.t = H.create 15


let theFile: global list ref = ref []

type copyDirection = ToCompat | FromCompat
let dirToString dir =
  match dir with
    ToCompat -> "to compat"
  | FromCompat -> "from compat"


let processPragma = function
  | Attr("ccuredwrapper", lst) -> begin
      match lst with
	AStr wrappername :: rest -> begin
          (* Now process the rest *)
          let wrapped = ref "" in
          List.iter
            (function
                ACons("of", [AStr x]) -> wrapped := x
              | _ -> ignore (warn "Invalid #pragma ccuredwrapper"))
            rest;
          if !wrapped = "" then
            E.s (error "Missing \"of\" argument in #pragma ccuredwrapper");
          if debugWrappers then
            ignore (E.log "Will use wrapper %s for %s\n"
                      wrappername !wrapped);

          H.add ccuredWrappers wrappername ();
	  try
            (* Check whether the function already has a wrapper. *)
	    let previousWrapper = H.find ccuredWrappedBy !wrapped in
	    if previousWrapper <> wrappername then
              ignore (E.unimp "Function %s has more than one wrapper"
                        !wrapped )
            (*if the names are the same, it's probably just a repeated
              .h file. *)
	  with Not_found ->
            (* Good, there were no other wrappers for this function. *)
	    H.add ccuredWrappedBy !wrapped wrappername;

        end
      | _ ->
          ignore (warn "Invalid #pragma ccuredwrapper")
  end

  | _ -> ()


(* Find the wrapper of a function. Might raise Not_found.
   matth: TODO: strip name. *)
let findWrapperOf (s: string) =
  let wrappername = H.find ccuredWrappedBy s in
  try
    match H.find MU.allFunctions wrappername with
      MU.Defined fdef -> fdef.svar
    | MU.Declared fdec -> fdec
  with Not_found ->
    E.s (error "Cannot find the definition of wrapper %s of %s.\n"
           wrappername s)

let hasAWrapper (s:string) =
  H.mem ccuredWrappedBy s

let isAWrapper (s:string) =
  H.mem ccuredWrappers s


let initFile () =
  H.clear ccuredWrappedBy;
  H.clear ccuredWrappers

(******** Code for adding constraints to the arguments of helpers ******)

(*Helpers for addConstraints, from markptr *)

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

(* These assume that the types have non-dummy nodes. *)
let setPosArith t why = begin N.setFlag (nodeOfType t) N.pkPosArith why end
let setReachString t why =
  if !N.useStrings then N.setFlag (nodeOfType t) N.pkString why

let setArith t why = begin N.setFlag (nodeOfType t) N.pkArith why end


(* Add an ESameType edge between the specified nodes *)
let forceSameType (t1: typ) (t2:typ) func: unit =
  let n1 = nodeOfType t1 in
  let n2 = nodeOfType t2 in
    if n1 == N.dummyNode then
      E.s (bug "Couldn't get node for %a in %s" d_type t1 func.vname);
    if n2 == N.dummyNode then
      E.s (bug "Couldn't get node for %a in %s" d_type t2 func.vname);
    ignore (N.addEdge n1 n2 N.ESameType None)

(* Look for the declarations of the wrapper helper functions and set
   constraints on their formals.  This should be done after polymorphic copies
   are made. *)
let addFormalConstraints (func:varinfo) =
  let rt, formals = match func.vtype with
    TFun (rt', formals', _, _) -> rt', Cil.argsToList formals'
  | _ -> E.s (bug "addFormalConstraints should only be called on functions.")
  in
  match Poly.stripPoly func.vname with
    "__ptrof" | "__ptrof_nocheck" ->  begin
      (* formals is a list of (name, type, attributes) triples. *)
      match formals with
          [(_, a, _)] -> forceSameType a rt func
	| _ -> E.s (bug "Wrong number of formals in %s." func.vname);
    end
  | "__ptrof_size" -> begin
      match formals with
        [(_, a, _); (_, len, _)] ->
	  forceSameType a rt func;
          setPosArith a (N.ProgramSyntax(!currentLoc));
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
  end
  | "__endof" -> begin
      match formals with
        [(_, a, _)] ->
	  forceSameType a rt func;
          setPosArith a (N.ProgramSyntax(!currentLoc));
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
    end
  | "__startof" -> begin
      match formals with
        [(_, a, _)] ->
	  forceSameType a rt func;
          setArith a (N.ProgramSyntax(!currentLoc));
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
    end
  | "__strlen" | "__verify_nul" | "__stringof" | "__stringof_ornull" -> begin
      match formals with
        [(_, a, _)] ->
          if (nodeOfType a) == N.dummyNode then
            E.s (bug "Couldn't get node for %a in %s" d_type a func.vname);
          if not !N.useStrings then
            setPosArith a (N.ProgramSyntax(!currentLoc));
          setReachString a (N.ProgramSyntax(!currentLoc));
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
  end
  | "__strlen_n" -> begin
      match formals with
        [(_, a, _); (_, len, _)] ->
          let n = nodeOfType a in
          if n == N.dummyNode then
            E.s (bug "Couldn't get node for %a in %s" d_type a func.vname);
          setPosArith a (N.ProgramSyntax(!currentLoc));
          setReachString a (N.ProgramSyntax(!currentLoc));
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
  end
  | "__mkptr"
  | "__mkptr_int" -> begin
      match formals with
        [(_, a, _); (_, b, _)] ->
	    (* We must be able to cast b to the return value *)
          let restn = nodeOfType rt in
          let btn = nodeOfType b in
          if btn == N.dummyNode then
            E.s (bug "Couldn't get node for %a in %s" d_type b func.vname);
          (* This also handles compatibility of the base types, so we don't
	   * need a separate ESameType edge. *)
	  ignore (N.addEdge btn restn (N.ECast N.EEK_mkptr) None)
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
  end
  | "__align_seq" -> begin
      match formals with
        [(_, a, _); (_, _, _)] ->
	    (* We must be able to cast b to the return value *)
          let restn = nodeOfType rt in
          let atn = nodeOfType a in
          if atn == N.dummyNode then
            E.s (bug "Couldn't get node for %a in %s" d_type a func.vname);
	  ignore (N.addEdge atn restn (N.ECast N.EEK_mkptr) None)
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
  end
  | "__mkptr_size" -> begin
      match formals with
        [(_, a, _); (_, len, _)] -> forceSameType a rt func
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
      (* The return value must not be wild.  How do we enforce this? Right now,
       * we wait until link-time, when the error message is unfriendly.*)
    end
  | "__mkptr_string" -> ()
      (* The return value must not be wild.  How do we enforce this? Right now,
       * we wait until link-time, when the error message is unfriendly.*)
  | "__write_at_least"
  | "__read_at_least" -> begin
      match formals with
        [(_, a, _); (_, len, _)] ->
          let n = nodeOfType a in
          if n == N.dummyNode then
            E.s (bug "Couldn't get node for %a in %s" d_type a func.vname);
          setPosArith a (N.ProgramSyntax(!currentLoc));
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
  end
  | "__copytags" -> begin
      match formals with (* __copytags(dest, src, len) *)
        [(_, a, _); (_, b, _); (_, len, _)] ->
	  let atn = nodeOfType a in
          let btn = nodeOfType b in
          if atn == N.dummyNode then
            E.s (bug "Couldn't get node for %a in %s" d_type a func.vname);
          if btn == N.dummyNode then
            E.s (bug "Couldn't get node for %a in %s" d_type b func.vname);
          setPosArith a (N.ProgramSyntax(!currentLoc));
          setPosArith b (N.ProgramSyntax(!currentLoc));
          (* We also want to ensure that they are both WILD at the same
           * time, so we use an ECast edge here.  This also handles
	   * compatibility of the base types, so we don't need a separate
	   * ESameType edge. *)
          ignore (N.addEdge btn atn (N.ECast N.EEK_copytags) None);
      | _ -> E.s (bug "Wrong number of formals in %s." func.vname);
  end

  | _ -> () (*func was not one of the functions we're watching for. *)


(***************************************************************************
 * Code for fixing argv and envp in main(). We may evenutally unify        *
 * this with the deepcopy wrappers below.                                  *)

let stringType =
  TPtr(charType, [Attr ("rostring", [])])
let safeCharPPtype =
  TPtr(stringType, [Attr ("safe", []); Attr ("main_input", [])])
let safeVoidPtrType =
  TPtr(voidType, [Attr ("safe", [])])

(* Creates a prototype if it doesn't already exist in MU.allFunctions,
   and adds it to the list of globals. *)
let findOrCreateFunc (makepoly: bool)
             (funcName:string)
             (rt:typ) (args: (string*typ) list)
             (theFile: global list ref) =
  let vi =
    try
      match H.find MU.allFunctions funcName with
	MU.Declared vi -> vi
      | MU.Defined fdec -> fdec.svar
    with Not_found ->
      if !E.verboseFlag then ignore (E.log
	 "   Couldn't find a declaration of %s; creating one.\n" funcName);
      let fdec = emptyFunction funcName in
      fdec.svar.vtype <- TFun(rt, Some [], false, []);
      List.iter (fun (name, t) -> ignore (makeFormalVar fdec name t)) args;
      theFile := GVarDecl(fdec.svar, !currentLoc)::!theFile;
      MU.registerFunction (MU.Declared fdec.svar);
      fdec.svar
  in
  (* Make it polymorphic: *)
  if makepoly then begin
    let polyAttr = Attr("ccuredpoly", [AStr funcName]) in
    Poly.processPragma polyAttr;
    theFile := GPragma(polyAttr, !currentLoc)::!theFile;
  end;
  vi

(*************************************************************
 **
 **             MAIN
 **
 **
 *************************************************************)
(* Generate here code to copy the ARGV array, allocating everything. This is
 * because later the code might want to store pointer to the arguments in
 * global variables. *)
let generateCopyArgv
    (main: fundec)
    (safe_argv: varinfo)
    (fat_argv: varinfo)
    (acc: stmt list) : stmt list =
  if not !N.use_wild_solver then begin
    Formatcil.cStmts
    "{
       // See if we need to make copies
       int no_mangling = 0;
       if(safe_argv) {
	 no_mangling = __ccured_has_empty_mangling(sizeof(* fat_argv));
       } else {
	   no_mangling = 1;
       }
       // Count how many strings we have
       int num_strings = 0;
       char **p_argv = safe_argv;
       while(* p_argv) {
         num_strings = num_strings + 1;
         // Do arithmetic without appearing to do so
         p_argv = __trusted_cast((void*)((long)p_argv + sizeof(* safe_argv)));
       }
       if(no_mangling) {
	 char** tmp_argv = __trusted_deepcast(safe_argv);
         fat_argv = __mkptr_size(tmp_argv, (1+num_strings)*sizeof(* fat_argv));
       } else {
         // Compute the size (with space for the NULL)
         unsigned int argvsize = (1 + num_strings) * sizeof(* fat_argv);

         // Allocate the new array
         fat_argv = wrapperAlloc(argvsize);
         // Now start assigning the strings (backwards)
         while(num_strings >= 0) {
            *(fat_argv + num_strings) = __mkptr_string(* p_argv);
            p_argv = __trusted_cast((void*)((long)p_argv - sizeof(* safe_argv)));
            num_strings = num_strings - 1;
         }
       }
     }
     %S:acc"
        (fun n t -> makeTempVar main ~name:n t)
        !currentLoc
         [ ("safe_argv", Fv safe_argv);
           ("fat_argv", Fv fat_argv);
           ("wrapperAlloc", Fv (MU.findFunc "wrapperAlloc"
                                  "Wrappers.generateCopyArgv"));
           ("__mkptr_string", Fv (MU.findFunc "__mkptr_string"
                                   "Wrappers.generateCopyArgv"));
           ("__mkptr_size", Fv (MU.findFunc "__mkptr_size"
                                   "Wrappers.generateCopyArgv"));
           ("__trusted_deepcast", Fv (MU.findFunc "__trusted_deepcast"
                                   "Wrappers.generateCopyArgv"));
           ("__ccured_has_empty_mangling",
            Fv (MU.findFunc "__ccured_has_empty_mangling"
                  "Wrappers.generateCopyArgv"));
           ("__trusted_cast", Fv (MU.findFunc "__trusted_cast"
                                  "Wrappers.generateCopyArgv"));
           ("acc", FS acc)
         ]
  end else begin
(* For the all-WILD solver. (Skip the no_mangling test.) *)
    Formatcil.cStmts
      "{
	 // Count how many strings we have
         int num_strings = 0;
         char **p_argv = safe_argv;
         while(* p_argv) {
           num_strings = num_strings + 1;
           // Do arithmetic without appearing to do so
           p_argv = __trusted_cast((void*)((long)p_argv + sizeof(* safe_argv)));
         }
         // Compute the size (with space for the NULL)
         unsigned int argvsize = (1 + num_strings) * sizeof(* fat_argv);

         // Allocate the strings
         fat_argv = wrapperAlloc(argvsize);
         // Now start assigning the strings (backwards)
         while(num_strings >= 0) {
            *(fat_argv + num_strings) = __mkptr_string(* p_argv);
            p_argv = __trusted_cast((void*)((long)p_argv - sizeof(* safe_argv)));
            num_strings = num_strings - 1;
         }
       }
       %S:acc"
        (fun n t -> makeTempVar main ~name:n t)
        !currentLoc
         [ ("safe_argv", Fv safe_argv);
           ("fat_argv", Fv fat_argv);
           ("wrapperAlloc", Fv (MU.findFunc "wrapperAlloc"
                                  "Wrappers.generateCopyArgv"));
           ("__mkptr_string", Fv (MU.findFunc "__mkptr_string"
                                   "Wrappers.generateCopyArgv"));
           ("__trusted_cast", Fv (MU.findFunc "__trusted_cast"
                                  "Wrappers.generateCopyArgv"));
           ("acc", FS acc)
         ]
  end

let isCharPP argType =
  (* (isCharPP argType) is true iff argType = char**.  *)
  match unrollTypeDeep argType with
    TPtr(TPtr(TInt(IChar, _), _), _) -> true
  | _ -> false

(* Add code to the beginning of the main function:
 *   (1) Call ccuredInit()
 *   (2) Make argv into a fat pointer, if needed.
 *   (3) Make envp into a fat pointer, if needed.
 * Unlike the code added by globInit, this will be cured.
 * May add function declarations and definitons to theFile. *)
let fixupMain mainDec (theFile: global list ref) : unit =
  if !E.verboseFlag then
    ignore (E.log "Adding initialization code to %s.\n" mainDec.svar.vname);
  let initCalls : stmt list ref = ref [] in

  (match mainDec.sformals with
    [] -> () (* Nothing to do here *)
  | [argc; argv] when isCharPP argv.vtype->
      if !E.verboseFlag then
        ignore (E.log "  Fattening %s\n" argv.vname);
      (*  Step (1) Make the old argv a local variable. (argv may become fat) *)
      mainDec.slocals <- argv::mainDec.slocals;
      (*  Step (2) Replace it with a new formal, which will always be thin. *)
      let argv_input = makeLocalVar mainDec
	  ~insert:false
	  ("__"^argv.vname^"_input")
          safeCharPPtype
      in
      setFormals mainDec [argc; argv_input];
      (*  Step 3) copy the data from the input array to the array
       *    that's actually used. *)
      initCalls :=
         generateCopyArgv mainDec argv_input argv !initCalls;

  | [argc; argv; envp] when isCharPP argv.vtype && isCharPP envp.vtype->
      if !E.verboseFlag then
        ignore (E.log "  Fattening %s and %s.\n" argv.vname envp.vname);
      (*  Step (A) Handle argv, as above. *)
      mainDec.slocals <- argv::mainDec.slocals;
      let argv_input = makeLocalVar mainDec
	  ~insert:false
	  ("__"^argv.vname^"_input")
	  safeCharPPtype
      in
      initCalls :=
         generateCopyArgv mainDec argv_input argv !initCalls;
      (*  Step (B) Handle envp the same way. *)
      mainDec.slocals <- envp::mainDec.slocals;
      let envp_input = makeLocalVar mainDec
	  ~insert:false
	  ("__"^envp.vname^"_input")
 	  safeCharPPtype
      in
      setFormals mainDec [argc; argv_input; envp_input];
      initCalls :=
         generateCopyArgv mainDec envp_input envp !initCalls;
  | _ -> ignore (warn "I wasn't expecting entrypoint '%s' to have signature:\n      %a\n   Therefore, I don't know how to create wide pointers for\n   its arguments.\n"
		   mainDec.svar.vname
		   d_plaintype (unrollTypeDeep mainDec.svar.vtype)));

  (* Every main gets a call to ccuredInit() *)
  if !E.verboseFlag then
    ignore (E.log "  Calling ccuredInit()\n");
  let ccuredInitFun = MU.findFunc "__ccuredInit" "Wrappers.main" in

  (* Make a global variable that controls whether we selected warnOnFail *)
  let alwaysStopOnErrorVar =
    makeGlobalVar "__ccuredAlwaysStopOnError" intType in
  (* And make a global variable that controls the strings *)
  let useStringsVar = makeGlobalVar "__ccuredUseStrings" intType in
  (* And make a global that controls whether we are logging non-pointers *)
  let logNonPointersVar = makeGlobalVar "__ccuredLogNonPointers" intType in
  initCalls :=
     (* Set the warnOnFail variable *)
     mkStmt
       (Instr
          [ Set(var alwaysStopOnErrorVar,
                (if !MU.alwaysStopOnError then one else zero), !currentLoc);
            Set(var useStringsVar,
                (if !N.useStrings then one else zero), !currentLoc);
            Set(var logNonPointersVar,
                (if !MU.logNonPointers then one else zero), !currentLoc);
            Call(None,
                 Lval(var ccuredInitFun),
                 [], !currentLoc)
          ])
     :: !initCalls;
  (* Add the initialization calls to the main block. *)
  mainDec.sbody.bstmts <-
    compactStmts ((List.rev !initCalls) @ mainDec.sbody.bstmts)



(***************** Compatible structs and typedef *******************)
(* We do not want to emit the definition of a compat structure before the
 * definition of the original structure. This is because some of the fields
 * in the new structure might end up using type and comp names from the
 * original structure, and we want to make sure that all of those are
 * defined. We keep here the comps whose definition we have see already. *)
let alreadyDefinedComp: (string, unit) H.t = H.create 17


(* When we generate a compatible copy of a type and we encounter compinfo and
 * typeinfo we either must insert a DEFINITION of the compatible version
 * before the current global (if we ar enot behind a pointer, in which case
 * "define" is true), or we add them to the "pendingCompat" table (indexed by
 * the original name) *)
let pendingCompat: (string, compinfo) H.t = H.create 13

(* Keep here the newly made compinfo (they could actually be the old ones if
 * they do not need copying) *)
let compatOfStruct: (string, compinfo) H.t = H.create 13
let compatOfTypedef: (string, typeinfo) H.t = H.create 13


let initCompat () =
  H.clear compatOfStruct;
  H.clear compatOfTypedef;
  H.clear pendingCompat;
  H.clear alreadyDefinedComp


let isCompatibleStructVersion (ci: compinfo) : bool =
  let lc = String.length "_COMPAT" in
  (* Strip the _COMPAT at the end of the name *)
  let cnl = String.length ci.cname in
  cnl > lc &&
  "_COMPAT" = String.sub ci.cname (cnl - lc) lc &&
  H.mem compatOfStruct (String.sub ci.cname 0 (cnl - lc))



(** Create a compatible version of a type. May add things to the
  * compatOfStruct and compatOfTypedef and may also add definitions to the
  * pendingCompat and to theFile (only if "define" is true). Returns the same
  * identical type if it does not change. Do not invoke this function
  * directly. Invoke getCompatTypeTop instead. *)
let rec getCompatType (define: bool) (t: typ) : typ =
  match t with
    TInt _ | TEnum _ | TBuiltin_va_list _ | TFloat _ | TVoid _ -> t
  | TComp(ci, a) -> begin
      (* See if we have a copy of this one *)
      let newci =
        try
          let newci = H.find compatOfStruct ci.cname in
          (* See if it is pending and we must define *)
          if define && H.mem pendingCompat ci.cname then begin
            H.remove pendingCompat ci.cname;
            if debugWrappers then
              ignore (E.log "emit pending def of %s\n" newci.cname);
            defineCompatCompinfo newci
          end;
          newci
        with Not_found -> begin
          (* See if we need to make a new one. If there are no pointers then
           * the compatible version is the same as the usual one! *)
          if hasPointers t then begin
            (* Make a superficial copy for now *)
            let newci = copyCompInfo ci (ci.cname ^ "_COMPAT") in
            (* Add it to the table, in preparation for recursion *)
            H.add compatOfStruct ci.cname newci;
            H.add compatOfStruct newci.cname newci;
            (if define then begin
              if debugWrappers then
                ignore (E.log "emit definition of %s\n" newci.cname);
              defineCompatCompinfo newci
            end else begin (* Ok, no definition, but add a declaration *)
              if debugWrappers then
                ignore (E.log "remember pending def of %s\n" newci.cname);
              theFile := GCompTagDecl(newci, !currentLoc) :: !theFile;
              H.add pendingCompat ci.cname newci;
            end);
            newci
          end else begin
            H.add compatOfStruct ci.cname ci;
            ci
          end
        end
      in
      if newci != ci then TComp(newci, dropAttribute "compat" a) else t
  end
  | TNamed(ti, a) -> begin
      (* See if we have made one already *)
      let newti =
        try H.find compatOfTypedef ti.tname
        with Not_found -> begin
          if hasPointers t then begin
            (* Make a copy of it *)
            let bt' = getCompatType define ti.ttype in
            let newti = {ti with tname = ti.tname ^ "_COMPAT";
                                 ttype = bt' } in
            H.add compatOfTypedef ti.tname newti;
            H.add compatOfTypedef newti.tname newti;
            theFile := GType(newti, !currentLoc) :: !theFile;
            newti
          end else begin
            H.add compatOfTypedef ti.tname ti;
            ti
          end
        end
      in
      if newti != ti then TNamed(newti, a) else t
  end
  | TPtr(bt, a) ->
      (* Since this is behind a pointer, we do not need to place a definition
       * before this global *)
      let bt' = getCompatType false bt in
      if bt' != bt then TPtr(bt', a) else t

  | TArray (bt, leno, a) ->
      let bt' = getCompatType define bt in
      if bt != bt' then TArray(bt', leno, a) else t

  | TFun (rt, argso, isva, a) ->
      let rt' = getCompatType define rt in
      let argso' =
        match argso with
          Some args ->
            let args' =
              mapNoCopy
                (fun ((an, at, aa) as a) ->
                  let at' = getCompatType define at in
                  if at' != at then (an, at', aa) else a)
                args
            in
            if args' != args then Some args' else argso
        | None -> argso
      in
      if rt' != rt || argso' != argso then TFun(rt', argso', isva, a) else t

and defineCompatCompinfo (newci: compinfo) : unit =
  (* Must change the fields and then add the definition to the file *)
  List.iter (fun f -> f.ftype <- getCompatType true f.ftype) newci.cfields;
  theFile := GCompTag(newci, !currentLoc) :: !theFile

(* This is a function that can be used to dump some of the pending stuff *)
let tryToEmitPendingComp () =
  (* Make the pending in a list *)
  let toDefine = ref [] in
  H.iter
    (fun n x ->
      if H.mem alreadyDefinedComp n then
        toDefine := (n, x) :: !toDefine)
    pendingCompat;
  List.iter
    (fun (n, x) ->
      H.remove pendingCompat n;
      if debugWrappers then
        ignore (E.log "emit pending def of %s (after getCompatTypeTop)\n"
                  x.cname);
      defineCompatCompinfo  x)
    !toDefine

(* This is the top-level invocation of the getCompat *)
let getCompatTypeTop (define: bool) (t: typ) : typ =
  let t' = getCompatType define t in
  tryToEmitPendingComp ();
  t'

(* Try to define some more of the pending compats, but only those for which
 * we already have the definition of the struct *)

(* And a visitor that handles the __COMPAT attributes for structures *)
class handleCompatVisitor
        (inWrapperFunction: bool)               : cilVisitor
    = object (self)
  inherit nopCilVisitor

  (* This is a deep-copy of a type. Find again the __COMPAT attributes and
   * change the types *)
  method vtype (t: typ) : typ visitAction =
    match t with
      TComp(_, a) when hasAttribute "compat" a ->
        ChangeTo (getCompatTypeTop true t)

    | _ -> DoChildren


  (* We must also make some changes in function calls. If we are inside a
   * wrapper function and we see a call to the original function, it is most
   * likely that cabs2cil has inserted casts from the COMPAT type of the
   * actual arguments to the regular type of the formals. We have now changed
   * the type of the formals an we must get rid of that cast as well *)
  method vinst (i: instr) : instr list visitAction =
    match i with
      Call(opt, Lval(Var vf, NoOffset), params, loc)
        when inWrapperFunction -> begin
          (* Compute new params *)
          let params' : exp list =
            let formalTypes =
              match unrollType vf.vtype with
                TFun(rt, ftypes, _, _) -> argsToList ftypes
              | _ -> E.s (bug "type of function %s is not a function"
                            vf.vname)
            in
            (* Compare two types and find out whether one is a
             * "compatibilized" version of another *)
            let rec isCompatibilizedOf (t1: typ) (t2: typ) =
              (* Convert a typesig to the COMPAT version *)
              let rec toCompat = function
                  TSArray(ts, eo, a) -> TSArray(toCompat ts, eo, a)
                | TSPtr (ts, a) -> TSPtr(toCompat ts, a)
                | TSComp (iss, n, a) -> TSComp(iss, n ^ "_COMPAT", a)
                | TSFun (ts, args, isva, a) ->
                    TSFun(toCompat ts, List.map toCompat args, isva, a)
                | ts -> ts
              in
              (* Compute the signatures without attributes *)
              let ts1 = typeSigWithAttrs (fun _ -> []) t1 in
              let ts2 = typeSigWithAttrs (fun _ -> []) t2 in
              let ts2' = toCompat ts2 in
              let res = ts1 = ts2' in
              if false then
                ignore (warn "isCompatibilized@!\tt1=%a@!\tt2=%a@!\tts1=%a@!\tts2=%a@!\tts2'=%a\n"
                          d_type t1 d_type t2 d_typsig ts1
                          d_typsig ts2 d_typsig ts2');
              res
            in
            let rec loop (params: exp list)
                (formalTypes: (string * typ * attributes) list)
                : exp list =
              match params, formalTypes with
                [], _ -> []
              | _, [] -> params
              | p :: params', (_, ft, _) :: formalTypes' ->
                  let params'' = loop params' formalTypes' in
                  let p'' =
                    let rec dropCasts = function
                        CastE(ct, p'') as p ->
                          if isCompatibilizedOf ft ct then
                            mkCast (dropCasts p'') ft
                          else
                            p
                      | p -> p
                    in
                    dropCasts p
                  in
                  p'' :: params''
            in
            loop params formalTypes
          in
	  ChangeDoChildrenPost
            ([Call(opt, Lval(Var vf, NoOffset), params', loc)],
             (fun x -> x))
	end
    | _ -> DoChildren

end

(* Now change the compatible structs *)
let handleCompatibleGlobal (g: global) =
  match g with
    GFun (fdec, l) ->
      currentLoc := l;
      (* While we are at it handle the main function as well *)
      if fdec.svar.vname = !Globinit.mainname
	  && fdec.svar.vstorage <> Static then
	begin
	  (* matth: add initialization code such as copying argv to a
	  fat array *)
	  fixupMain fdec theFile
	end;
      (* Now visit the body of the function *)
      ignore
        (visitCilGlobal
           (new handleCompatVisitor (isAWrapper fdec.svar.vname))
           g);
      theFile := g :: !theFile

  | GVarDecl (v, l) when hasAWrapper v.vname ->
      currentLoc := l;
      (* Must make its types compatible *)
      v.vtype <- getCompatTypeTop true v.vtype;
      theFile := g :: !theFile

  | GCompTag (ci, l) ->
      currentLoc := l;
      ignore (visitCilGlobal (new handleCompatVisitor false) g);
      theFile := g :: !theFile;
      H.add alreadyDefinedComp ci.cname ();
      (* See if it has a pending compat *)
      (try
        let newci = H.find pendingCompat ci.cname in
        (* Go ahead and emit it *)
        H.remove pendingCompat ci.cname;
        if debugWrappers then
          ignore (E.log "emit pending def of %s (after GCompTag)\n"
                    newci.cname);
        defineCompatCompinfo newci
      with Not_found -> ())

  | GType (ti, l) ->
      currentLoc := l;
      ignore (visitCilGlobal (new handleCompatVisitor false) g);
      theFile := g :: !theFile

  | g ->
      let newglobs = visitCilGlobal (new handleCompatVisitor false) g in
      theFile :=  newglobs @ !theFile


(************************ Deep copying **************************)


(** Find all field names that have at least one assignment to them *)
class findAssignmentsClass (currentFunc: string)
                           (destvar: varinfo)
                           (hash: (string, unit) H.t) = object
  inherit nopCilVisitor

  method vinst (i: instr) =
    (match i with
      (* Make sure that we do not assign to destvar itself *)
    | Set ((Var destvar', _), _, _)
    | Call (Some (Var destvar', _), _, _, _) when destvar' == destvar ->
        E.s (error "You should not assign directly to %s in the body of deepcopy wrapper %s" destvar.vname currentFunc)
    | Set ((Mem(Lval(Var destvar', _)), Field(f, _)), _, _)
    | Call (Some (Mem(Lval(Var destvar', _)), Field(f, _)), _, _, _)
        when destvar' == destvar ->
          H.add hash f.fname ()
    | _ -> ());
    SkipChildren

  method vexpr _ = SkipChildren
  method vtype _ = SkipChildren

end

(***************************************************************************)
(**** Code for generating the bodies of __deepcopy_* functions:         ****)

let copyPointer (thisFunc: fundec)
                (fieldname: string)
                (direction: copyDirection)
                (dest: lval)
                (src: lval) : stmt list =
  if direction = ToCompat then
    Formatcil.cStmts
    "src1 = __ptrof_nocheck(%l:src); // Make it SAFE
     if(! src1) {
       %l:dest = 0;
     } else {
       /* If the types have not changed, just copy them over */
       int dest_mangling = __ccured_has_empty_mangling(sizeof(* src1));
       if(dest_mangling) {
         /* __trusted_cast is used to prevent CCured from connecting the
            types. Still, it is Ok because both are SAFE */
         %l:dest = __trusted_cast(src1);
       } else {
         abort_deepcopy(%g:fieldname);
       }
     } "
        (fun n t -> makeTempVar thisFunc ~name:n t)
         !currentLoc
         [ ("src", Fl src);
           ("dest", Fl dest);
           ("__trusted_cast",
            Fv (MU.findFunc "__trusted_cast" "Wrappers.copyPointer"));
           ("__ptrof_nocheck",
            Fv (MU.findFunc "__ptrof_nocheck" "Wrappers.copyField"));
           ("__ccured_has_empty_mangling",
            Fv (MU.findFunc "__ccured_has_empty_mangling"
                  "Wrappers.copyField"));
           ("src1", Fv (makeTempVar thisFunc (typeOfLval src)));
           ("abort_deepcopy",
            Fv (MU.findFunc "abort_deepcopy" "Wrappers.copyPointer"));
           ("fieldname", Fg ("Abort deepcopy_to_compat for " ^ fieldname));
         ]
  else (* This is FromCompat *)
    Formatcil.cStmts
    "if(! %l:src) {
       %l:dest = 0;
     } else {
       /* If the types have not changed, just copy them over */
       int src_mangling = __ccured_has_empty_mangling(sizeof(* %l:dest));
       if(src_mangling) {
        /* We must not connect dest and src. Yet this code is
           run only if they have the same kind (SAFE, since src is SAFE).
           So, we use __mkptr */
           %l:dest = __mkptr(%l:src, %l:dest);
       }  else {
          abort_deepcopy(%g:fieldname);
       }
     } "
        (fun n t -> makeTempVar thisFunc ~name:n t)
         !currentLoc
         [ ("src", Fl src);
           ("dest", Fl dest);
           ("__mkptr",
            Fv (MU.findFunc "__mkptr" "Wrappers.copyPointer"));
           ("abort_deepcopy",
            Fv (MU.findFunc "abort_deepcopy" "Wrappers.copyPointer"));
           ("__ccured_has_empty_mangling",
            Fv (MU.findFunc "__ccured_has_empty_mangling"
                  "Wrappers.copyField"));
           ("fieldname", Fg ("Abort deepcopy_from_compat for " ^ fieldname));
         ]


(* Create (of fill in) the copy of a deepcopy function. Return None if we
 * just filled in an existing body *)
let createDeepCopyBody
   (structName: string)
   (funcDecl: varinfo)
   (direction: copyDirection) : fundec option  =
  if debugWrappers then
    ignore (E.log "Creating deepcopy body for %s.\n" funcDecl.vname);
  let name = Poly.stripPoly funcDecl.vname in
  (* Now check the type of the function *)
  let destci, srcci, destt, srct =
    match funcDecl.vtype with
      TFun(TVoid _,
           Some [ (_, (TPtr(TComp(destci, desta), _) as destt), _);
                  (_, (TPtr(TComp(srcci, srca), _) as srct), _) ], _, _)
      ->
        if destci != srcci || destci.cname <> structName then
          E.s (error "The argument types of %s are wrong. Both should be pointers to struct %s" funcDecl.vname structName);
        (* Now check that the attributes are right *)
        if
          not (if direction = FromCompat then
            hasAttribute "compat" srca && not (hasAttribute "compat" desta)
          else
            hasAttribute "compat" desta && not (hasAttribute "compat" srca))
        then
          E.s (error "The __COMPAT attributes in the argument types of %s are wrong"
                 funcDecl.vname);
        destci, srcci, destt, srct

    | _ ->
        E.s (error "The type of %s is incorrectly formed." funcDecl.vname)
  in
  (* See if we have a definition for this function already. If we we reuse it
   * and maybe we fill in some more code *)
  let func, isNew =
    try
      match H.find MU.allFunctions funcDecl.vname with
      | MU.Defined fdec ->
          if debugWrappers then
            ignore (E.log "Found definition of %s\n" funcDecl.vname);
          fdec, false
      | MU.Declared fd ->
          if debugWrappers then
            ignore (E.log "Found declaration of %s\n" funcDecl.vname);
          let func = emptyFunction funcDecl.vname in
          let destIn = makeFormalVar func
              (if direction = ToCompat then "compat" else "fat")
              destt in
          let src    = makeFormalVar func
              (if direction = ToCompat then "fat" else "compat")
              srct in
          func.svar <- fd;
          func, true
    with Not_found ->
      E.s (bug "Wrappers:%s is not known" funcDecl.vname)
  in

  (* Now lookup the destination variable in the formals *)
  let (destvar, srcvar) =
    match func.sformals with
      d :: s :: [] -> d, s
    | _ -> E.s (bug "wrappers: bad function type")
  in
  (* Now we scan the body and we collect all field names that have at least
   * one assignment to them *)
  let alreadyAssignedHash: (string, unit) H.t = H.create 13 in
  let oldLoc = !currentLoc in
  let findAssignments =
    new findAssignmentsClass funcDecl.vname destvar alreadyAssignedHash in
  ignore (visitCilBlock findAssignments func.sbody);
  (* Reset the location after visiting *)
  currentLoc := oldLoc;

  (* Now we scan all the fields and for those that are not in the list that we
   * collected, we add code for copying them ourselves *)

  (* Now copy the fields *)
  let copyFields : stmt list =
    (* We keep a stack of iterators *)
    let iterStack: varinfo list ref = ref [] in
    let getIterVar () =
      match !iterStack with
        [] ->
          let i = makeTempVar func intType in
          i
      | i :: rest ->
          iterStack := rest; i
    in
    let releaseIterVar (i: varinfo) : unit =
      iterStack := i :: !iterStack
    in

    (* Copy one field *)
    let copyField destfi srcfi (acc: stmt list) =
      if not (H.mem alreadyAssignedHash destfi.fname) then begin
        if debugWrappers then
          ignore (E.log "adding code to copy field %s in %s\n"
                    destfi.fname funcDecl.vname);
        (* We have a recursive function that copies the entire type *)
        let rec autoCopy (acc: stmt list)
                         (dest: lval)
                         (src: lval) : stmt list =
          let t = unrollType (typeOfLval dest) in
          (* If this offset does not have pointers, then it must have the
           * same type in both the compatible and the regular struct; we just
           * copy it. Also we do not copy array types because they appear as
           * pointers! *)
          if not (hasPointers t) && not (isArrayType t) then
	    mkStmtOneInstr (Set (dest, Lval src, !currentLoc)) :: acc
          else begin
            (* What we do now depends on the type of the field. *)
            match unrollType t with
              TPtr (bt, _) ->
                copyPointer func
                  (structName ^ "." ^ destfi.fname)
                  direction
                  dest src @ acc

            | TComp (new_destci, _) -> begin
                (* Get the corresponding compinfo for the source *)
                let new_srcci =
                  match unrollType (typeOfLval src) with
                    TComp (new_srcci, _) -> new_srcci
                  | _ -> E.s (E.bug "Wrappers:source is not a compinfo")
                in
                (* Find the original name *)
                let sname =
                  if direction = FromCompat then
                    new_destci.cname else new_srcci.cname in

                (* For a structure, we first check if we have declared a
                 * deepcopy function. If yes, then we call that one *)
                let rec_copy : varinfo option =
                  try
                    match H.find MU.allFunctions
                        ("__deepcopy_" ^ sname ^ "_" ^
                         (if direction = FromCompat then "from" else "to")
                         ^ "_compat")
                    with
                    | MU.Declared v -> Some v
                    | MU.Defined f -> Some f.svar
                  with Not_found -> None
                in
                match rec_copy with
                | None -> (* We iterate over the fields *)
                    List.fold_right2
                      (fun destfi srcfi acc ->
                        autoCopy
                          acc
                          (addOffsetLval (Field(destfi, NoOffset)) dest)
                          (addOffsetLval (Field(srcfi, NoOffset)) src))
                      new_destci.cfields
                      new_srcci.cfields
                      acc

                | Some f -> (* just invoke this function *)
                    mkStmtOneInstr (Call (None, Lval (var f),
                                          [ AddrOf dest;
                                            AddrOf src ], !currentLoc)) :: acc
            end

            | TArray (bt, leno, _) ->
                (* For an array (which contains pointers) we iterate through
                 * all the elements and copy each one by one *)
                let nElems =
                  try lenOfArray leno with LenOfArray ->
                    E.s (error "Cannot generate copy code for array (in field %s) of non-constant length" destfi.fname)
                in
                (* Grab an iteration variable *)
                let i = getIterVar () in
                let res =
                  mkForIncr ~iter:i
                    ~first:zero
                    ~stopat:(integer nElems)
                    ~incr:one
                    ~body:
                    (let idx = Index(Lval (var i), NoOffset) in
                     autoCopy
                        []
                        (addOffsetLval idx dest)
                        (addOffsetLval idx src))
                in
                releaseIterVar i;
                res @ acc

            | TFun _ -> E.s (E.unimp "Wrappers: function type")

            | _ -> E.s (E.unimp "wrappers: copyFields")
          end
        in
        autoCopy
              acc
             (Mem (Lval (var destvar)), Field(destfi, NoOffset))
             (Mem (Lval (var srcvar)), Field(srcfi, NoOffset))
      end else
        acc
    in
    List.fold_right2
      copyField
      destci.cfields
      srcci.cfields
      []
  in
  func.sbody.bstmts <- copyFields @ func.sbody.bstmts;
  if isNew then Some func else None



(* Precompile the regexp *)
let deepCopyRegexp = Str.regexp "__deepcopy_\\(.+\\)_\\(to\\|from\\)_compat"


(** Make a pass over the file and replace the wrapped functions with their
 * wrappers. Also, fill in the bodies of the deep wrappers *)

let currentFunctionName = ref ""
(* First a visitor that replaces the calls with wrappers *)
class replaceWrapperVisitor
    (inWrapperFunction: bool) : cilVisitor = object
  inherit nopCilVisitor

  method vinst (i: instr) : instr list visitAction =
    match i with
      Call(opt, Lval(Var vf, NoOffset), params, loc)
        when not inWrapperFunction
      ->
        begin
          (* We are not in a wrapper *)
          try
	    let wrapper = findWrapperOf vf.vname in
            if debugWrappers then
              ignore (E.log "changing call to %s to %s in %s.\n" vf.vname
                        wrapper.vname !currentFunctionName);
	    ChangeDoChildrenPost
              ([Call(opt, Lval(Var wrapper, NoOffset), params, loc)],
               (fun x -> x))
          with Not_found ->
	    DoChildren
        end

    | _ -> DoChildren

            (* Intercept taking the address of a function *)
  method vexpr e =
    match e with
      AddrOf (Var vf, NoOffset) when isFunctionType vf.vtype -> begin
        try
	  let wrapper = findWrapperOf vf.vname in
          if debugWrappers then
            ignore (E.log "changing &%s to &%s in %s.\n" vf.vname
                      wrapper.vname !currentFunctionName);
	  ChangeTo (AddrOf (Var wrapper, NoOffset))
        with Not_found -> begin
	  SkipChildren
        end
      end

    | _ -> DoChildren

  method vblock b =
    if hasAttribute "nocure" b.battrs then
      SkipChildren
    else begin
      if hasAttribute "nobox" b.battrs then
        E.s (error "nobox attribute on blocks is obsolete. Use nocure");
      DoChildren
    end
end


(** Replace all the wrapped calls with the wrappers. The resulting file is in
 * reverse order !!! *)

let replaceWrappers (fl: file) : unit =
  (* First, we must fill in the bodies of deepcopy functions. Go and search
   * for their definitions *)
  let newDeepCopyBodies : global list ref = ref [] in
  iterGlobals fl
    (fun g ->
      (* Look at definitions and declarations also. *)
      match g with
        GVarDecl (v, l) | GFun ({svar = v}, l) ->
          currentLoc := l;
          let name = Poly.stripPoly v.vname in
          if Str.string_match deepCopyRegexp name 0 then begin
            let sname = Str.matched_group 1 name in
            let direction =
              if (Str.matched_group 2 name) = "to" then
                ToCompat else FromCompat
            in
            if sname <> "stringarray" then begin
              match createDeepCopyBody sname v direction with
                Some fdec -> (* A new body *)
                  newDeepCopyBodies := GFun(fdec, l) :: !newDeepCopyBodies
              | None -> () (* We just filled an existing body *)
            end
          end
      | _ -> ());

  (* Now, we must process the __COMPAT attribute on structure names.
   * Also, each wrapped function must have its types turned to use only
   * __COMPAT structures *)
  initCompat ();

  (* We scan first the globals to find out which types will need compat *)
(*
  iterGlobals fl markCompatibleInGlobal;
  List.iter markCompatibleInGlobal !newDeepCopyBodies;
*)
  (* Now we scan again and we replace the types with compatible ones *)
  theFile := [];
  iterGlobals fl handleCompatibleGlobal;
  List.iter handleCompatibleGlobal !newDeepCopyBodies;

  (* Now "theFile" is in REVERSE !!!! *)
  fl.globals <- !theFile;
  (* Just check that we have not left anything behind *)
  (let pending = ref [] in
   H.iter (fun _ x -> pending := x :: !pending) pendingCompat;
   if !pending <> [] then begin
     E.s (E.bug "Wrappers: the following structs are pending: %a\n"
            (docList (fun x -> text x.cname)) !pending);
   end);
  initCompat ();

  (* Now we must replace the calls with the appropriate wrappers *)
  theFile := [];
  let doReplaceWrappers (g: global): unit =
    let doit, name, inWrapper =
      match g with
        GFun (fdec, _) -> true, fdec.svar.vname, isAWrapper fdec.svar.vname
      | GVar (v, _, _) -> true, v.vname, false
      | _ -> false, "", false
    in
    if doit then begin
      currentFunctionName := name;
      let glist = visitCilGlobal (new replaceWrapperVisitor inWrapper) g in
      List.iter (fun g -> theFile := g :: !theFile) glist
    end else
      theFile := g :: !theFile
  in
  iterGlobals fl doReplaceWrappers;
  fl.globals <- !theFile;
  theFile := [];
  ()
