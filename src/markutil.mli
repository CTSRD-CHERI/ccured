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

(** Call before processing a file *)
val init: unit -> unit

(** Accumulate here the marked file *)
val theFile: Cil.global list ref

(** A pointer to the current function *)
val currentFunction: Cil.fundec ref

(* Keep track of functions that are declared and defined *)
type funinfo = Declared of Cil.varinfo | Defined of Cil.fundec

val allFunctions: (string, funinfo) Hashtbl.t
val allCompinfo: (string, Cil.compinfo * Cil.location) Hashtbl.t

(** For each global, the location where it was defined,
  or None if it has not been defined. *)
val allGlobals: (string, Cil.location option) Hashtbl.t

val findFunc: name:string -> neededby:string -> Cil.varinfo

(** Called functions *)
val calledFunctions: (string, Cil.varinfo) Hashtbl.t

(** Register a function *)
val registerFunction: funinfo -> unit

(** Register a global variable definition. *)
val registerGlobalDefinition: Cil.varinfo -> Cil.location -> unit

(** Register a global variable declaration. *)
val registerGlobalDeclaration: Cil.varinfo -> unit

(** See if a function is already defined *)
val alreadyDefinedFunction: string -> bool


(** Apply a function to a function of a given name. If the function was not
 * registered already we will apply the function when we will register it *)
val applyToFunction: string -> (Cil.varinfo -> unit) -> unit

(** Like the above but apply only to definitions. *)
val applyToFunctionDef: string -> (Cil.fundec -> unit) -> unit


(** Use to get the function type attributes for an expression *)
val getFunctionTypeAttributes: Cil.exp -> Cil.attributes


(** Use to add attributes to a function variable *)
val addFunctionTypeAttribute: Cil.attribute -> Cil.varinfo -> unit


(** Check if a global variable is imported, declared but not defined. *)
val isImported: string -> bool

(* Check if a type can have RTTI. This means that it is void or appeared in a
 * ccured_extends pragma. In any case it has to be a typdef or a structure
 * type. It also returns a reason, which is interesting if the result is
 * "false".  *)
val typeCanHaveRtti: Cil.typ -> bool * string


(* Check a cast in which at least one of the types is RTTI. Pass an
 * indication whether automatic inference of RTTI is desired (and if so say
 * where should the newly created edges be added). Use this option only
 * before solving. Pass the pointer types. Returns whether the cast must be
 * checked at run-time. *)
val checkRttiCast: newedges:(Ptrnode.edge list ref option) ->
                   Cil.typ -> bool ->
                   Cil.typ -> bool -> Cil.location ->
                   Cil.exp * Cil.exp * bool


(** The type of a RTTI *)
val rttiType: Cil.typ

(** Get the RTTI of void. *)
val getVoidRtti: unit -> Cil.exp

(** Get the RTTI of scalar *)
val getScalarRtti: unit -> Cil.exp

(** Register a type that is used in a tagged union, and that
  therefore needs an rtti tag even though it may not be a pointer.
  This method does not draw edges, so do that elsewhere.*)
val registerRttiType: Cil.typ -> unit

(** Get RTTI tag for a type that was previously registered with
    checkRttiCast or registerRttiType *)
val getRttiForType: Cil.typ -> Cil.exp

(** Call this function for all DEFINITIONS of GCompTag and GType to populate
 * the extension information with the real info *)
val registerCompinfo: Cil.compinfo -> Cil.location -> unit

val registerTypeinfo: Cil.typeinfo -> unit

(* Add extends pragma *)
val processPragma: Cil.attribute -> Cil.location -> unit

(** a GVar declaration of the RTTI data structure.  After curing,
  call generateRTTI, below, to populate the length and initializer of this
  definition. *)
val rttiArrayDefn: Cil.global

(** Generate the RTTI data structure *)
val generateRTTI: unit -> unit


(** Generate all extends relationships not involving void *)
val allExtendsRelationships: unit -> (Cil.typ * Cil.typ * Cil.location) list

(** Dump the extension hierarchy *)
val dumpExtensionHierarchy: unit -> unit


(** Whether to use shallow mangling of names *)
val shallowMangling: bool ref

(* If false generate code to ensure that the run-time checks just print an
 * error message instead of aborting. *)
val alwaysStopOnError: bool ref

(* If false then ensure that run-time checks print more info *)
val failIsTerse: bool ref

(** if set will generate code to track at run-time where the non-pointers
 * originate *)
val logNonPointers: bool ref



(** For generating annotations in verify.ml *)
type exkind =
    (* Pointer to ... *)
    ExType of Cil.typeinfo
  | ExComp of Cil.compinfo
  | ExVoid
  | ExAuto of Cil.typ * Ptrnode.node
      (* !upointType.  Scalars of other sizes are ExNonPointers *)
  | ExScalar
      (* Anything larger than a pointer. Used in tagged unions. *)
  | ExNonPointer of Cil.typ
val getAllExtensions: unit -> exkind array

(** Annotate the output for verification. *)
val doAnnotateOutput: bool ref
