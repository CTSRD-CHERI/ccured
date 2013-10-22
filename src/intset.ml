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
(* implementation of int sets as bit vectors *)
type set = int array

let bitsPerInt =
  let rec loop n = if 1 lsl n = 0 then n else loop (n+1) in
  loop 1

(* index and mask of an int *)
let index i = (i/bitsPerInt, 1 lsl (i mod bitsPerInt))

let empty () = Array.create 0 0

let singleton e =
  let (i,m) = index e in let a = Array.create (i+1) 0 in Array.set a i m; a

let equal s t =
  let test (a0, a0len, a1, a1len) i =
    let rec loop i =
      if i<a0len then
	Array.get a0 i = Array.get a1 i && loop (i+1)
      else if i<a1len then
	Array.get a1 i = 0 && loop (i+1)
      else true in
    loop i in
  s=t ||
  let sLen = Array.length s in
  let tLen = Array.length t in
  (sLen<tLen && test (s, sLen, t, tLen) 0) ||
  (tLen<sLen && test (t, tLen, s, sLen) 0)

(* copy s, ensuring it is large enough to store x *)
let dextend s x =
  let (i,m) = index x in
  if i < Array.length s then
    Array.copy s
  else
    let a = Array.create (i+1) 0 in
    Array.blit s 0 a 0 (Array.length s);
    a

(* destructively insert *)
let dinsert s x =
  let (i,m) = index x in
  if i<Array.length s then
    Array.set s i (m lor Array.get s i)
  else raise (Invalid_argument "Intset.dinsert insert out of range")
(*  let a = Array.create (i+1) 0 in
    Array.blit s 0 a 0 (Array.length s);
    Array.set a i m;
    a *)

let insert s x =
  let (i,m) = index x in
  if i<Array.length s then
    let s' = Array.copy s in (Array.set s' i (m lor Array.get s' i); s')
  else let a = Array.create (i+1) 0 in
       Array.blit s 0 a 0 (Array.length s);
       Array.set a i m;
       a

let rec union2 (s, t) =
  let sLen = Array.length s in
  let tLen = Array.length t in
  Array.init (max sLen tLen)
    (fun i ->
      (if i<sLen then Array.get s i else 0) lor
      (if i<tLen then Array.get t i else 0))

let rec union = function
    [] -> empty ()
  | [set] -> set
  | (s0::s1::rest) -> union (union2 (s0, s1)::rest)

let intersect2 (s, t) =
  let sLen = Array.length s in
  let tLen = Array.length t in
  Array.init (max sLen tLen)
    (fun i ->
      (if i<sLen then Array.get s i else 0) land
      (if i<tLen then Array.get t i else 0))

let rec intersect univ = function
    [] -> univ
  | [set] -> set
  | (s0::s1::rest) -> intersect univ (intersect2 (s0, s1)::rest)

(* destructive remove - may clobber s *)
let dremove s a =
  let (i,m) = index a in
  Array.set s i ((Array.get s i) land (lnot m))

let remove s a =
  let (i,m) = index a in
  let s' = Array.copy s in
  Array.set s' i ((Array.get s' i) land (lnot m)); s'

let iter f s =
  let rec loop = function
      (_, 0) -> ()
    | (i, m) -> (if m land 1 = 1 then f i); loop (i+1, m lsr 1) in
  let iterer i m = loop (i*bitsPerInt, m) in
  Array.iteri iterer s


let toList s =
    let l = ref [] in
    let f i = l := i :: !l in
    iter f s; !l

let rec fromList = function
    [] -> empty ()
  | i::rest -> insert (fromList rest) i

let contains s x =
  let (i,m) = index x in
  if i<Array.length s then (m land Array.get s i) <> 0 else false

let difference (s, t) =
  let tlen = Array.length t in
  Array.init
    (Array.length s)
    (fun i ->
      if i>=tlen then
	Array.get s i
      else
	(Array.get s i) land (lnot (Array.get t i)))

let fold f s = List.fold_right f (toList s)

let shrink s i =
  if Array.length s > i then
    let a = Array.create i 0 in
    Array.blit s 0 a 0 i; a
  else s
