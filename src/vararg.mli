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


(** Called to initialize a new file. *)
val initFile: unit -> unit

(** Called to add to the file definitions for the automatically generated
 * descriptors *)
val addToFileAutoDescr: unit -> unit

(** Markptr will store here the pointer necessary for processing a new field.
 * We will invoke this function *)
val pMarkField: (Cil.fieldinfo -> unit) ref

(** Assume all non-annotated vararg functions behave like printf *)
val assumePrintf: bool ref

(** Called on all pragmas before any other processing *)
val processPragma: Cil.attribute -> unit


(* Turn the gcc format attribute into our own notation.  Returns a type
   that may have a new attribute but which is otherwise the same. *)
val processFormatAttribute: Cil.typ -> Cil.typ


(** Called at the time of a call to process the arguments. Returns a list of
 * instructions to be added before the call and the modified arguments. Might
 * also add global declarations to MU.theFile. *)
val prepareVarargArguments:
    mkTempVar:(Cil.typ -> Cil.varinfo) ->
    func: Cil.exp ->
    nrformals: int ->
    args: Cil.exp list -> Cil.instr list * Cil.exp list



(** Called to process the body of a variable argument function *)
val processVarargBody: Cil.fundec -> unit
