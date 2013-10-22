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

val debugWrappers: bool

(** Called to initialize the processing of one file *)
val initFile: unit -> unit


(** Called to process pragmas before any other globals *)
val processPragma: Cil.attribute -> unit


(** This is the function that does the work of the Wrappers module *)
val replaceWrappers: Cil.file -> unit


(** Takes the name of a function and returns that function's
    wrapper (Or throws Not_found). *)
val findWrapperOf: string -> Cil.varinfo

(** e.g. #pragma ccuredwrapperof("foo_wrapper", "foo")
 ** means that "foo" has a wrapper and "foo_wrapper" is a wrapper. *)
val hasAWrapper: string -> bool
val isAWrapper: string -> bool

(** Improved version of addConstraints.  Adds constraints to directly to the
 ** formal args of e.g. __endof, __mkptr, etc.
 ** No-op for all functions besides the wrapper helpers. *)
val addFormalConstraints: Cil.varinfo -> unit



(* Creates a prototype if it doesn't already exist in MU.allFunctions,
   and adds it to the list of globals.  It's exposed here becuase
   markptr also needs this function. (It can't go in markutil because
   it may call Poly.processPragma.) *)
val findOrCreateFunc: bool -> string -> Cil.typ -> (string*Cil.typ) list
    -> Cil.global list ref -> Cil.varinfo



(* Check if a struct is supposed to be a compatible one *)
val isCompatibleStructVersion: Cil.compinfo -> bool
