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


(** Split a name into a polymorphic prefix and a base name. The polymorphic
 * prefix is the empty string if this is not a polymorphic name *)
val splitPolyName: string -> string * string

(** Strip the polymorphic prefix on names *)
val stripPoly: string -> string


(** See if a name has a polymorphic prefix *)
val isPolyName: string -> bool

(** Called before any globals are initialized *)
val initFile: unit -> unit

(** Called to process a pragma before any other global is processed *)
val processPragma: Cil.attribute -> unit

(** Called to instantiate a polymorphic function. Returns a modifed varinfo
 * and an indication whether this was actually a polimorphic function. *)
val instantiatePolyFunc: Cil.varinfo -> Cil.varinfo * bool


(** Check to see if a function is polymorphic *)
val isPolyFunc: Cil.varinfo -> bool

(** Check to see if a structure is polymorphic *)
val isPolyComp: Cil.compinfo -> bool

(** Called for each function definition *)
val rememberFunctionDefinition: Cil.fundec -> Cil.global


(** Called to finish the instantiations. Pass a function for processing the
 * newly created functions.  *)
val finishInstantiations: (Cil.fundec -> unit) -> unit


(** Called to create an instance of a compinfo *)
val instantiatePolyComp: Cil.compinfo -> (Cil.compinfo -> unit) -> Cil.compinfo


(** Call to get the representative of a class of polymoprhic functions. *)
val getPolyFuncRepresentative: Cil.varinfo -> Cil.varinfo

val getPolyCompRepresentative: Cil.compinfo -> Cil.compinfo
