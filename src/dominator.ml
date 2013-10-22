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
type flowgraph = { size: int;
			 entry: int;
			 succ: int list array;
			 pred: int list array}

(*
  References to "Muchnick" below indicate the book
  Advanced Compiler Design and Implementations.

  Many of the algorithms in this file are needlessly inefficient.  They
  may very well need to be updated!

  Currently, returns iterated dominator frontier (DF+) and immediate
  dominators.
*)

(*
  Definitions:

  [Muchnick section 7.3]

  "d dom i" iff
     every execution path from entry to i includes d.

  "a idom b" iff
     a dom b and no other node, c, satisfies a dom c and c dom b

  "d sdom i" iff
     d dom i and d<>i

  "p pdom i iff"
     every execution path from i to exit includes i

  [Muchnick section 8.11]

  Dominance frontier for a variable:
    DF(x) = {y | (exists z in Pred(y) s.t. x dom z) and not x sdom y}

  Dominance frontier for a set of (flowgraph) nodes:
    DF(S) = union {DF(x) | x in S}
*)

module Set = Intset

type dominatorinfo =
    {dfplus: (*Flowgraph.node*) Set.set -> (*Flowgraph.node*) Set.set;
     idom: int -> (*Flowgraph.node*) (*Set.set*) int;
     idomOf: int -> (*Flowgraph.node*) Set.set;
     postorder: int list}

(* Muchnick's Dom_Comp, fig 7.14 *)
(* This should not be needed once Domin_Fast is implemented. *)
(* this is a serious bottleneck !!! *)
let domComp flowgraph =
  let nodes =
    Set.fromList (Array.to_list (Array.init flowgraph.size (fun i -> i))) in
  let withoutRoot = Set.remove nodes flowgraph.entry in
  let domin = Array.make flowgraph.size nodes in
  Array.set domin flowgraph.entry (Set.singleton flowgraph.entry);
  (* loop, narrowing in on the correct table *)
  let changed = ref true in
  let doNode n =
    let t =
      Set.intersect nodes
	(List.map (Array.get domin) (Array.get flowgraph.pred n)) in
    let d = Set.union2 (t, Set.singleton n) in
    if d<>Array.get domin n then (changed := true; Array.set domin n d) in
  while !changed do
    changed := false;
    Set.iter doNode withoutRoot;
  done;
  Array.get domin

(* Muchnick's Idom_comp, 7.15 *)
(* Nodes should be processed in depth-first order [Muchnick p. 183] *)
(* this is a serious bottlenek !!! *)
let idomComp flowgraph domin =
  let nodes =
    Set.fromList (Array.to_list (Array.init flowgraph.size (fun i -> i))) in
  let withoutRoot = Set.remove nodes flowgraph.entry in
  let tmp = Array.init flowgraph.size (fun n -> Set.remove (domin n) n) in
  let innerLoop n =
    let innermostLoop s =
      let adjustTmp t =
	if Set.contains (domin s) t then
	  Set.dremove (Array.get tmp n) t in
      if Set.contains (Array.get tmp n) s then
	Set.iter adjustTmp (Set.remove (Array.get tmp n) s) in
    Set.iter innermostLoop (Array.get tmp n) in
  Set.iter innerLoop withoutRoot;
  let idom = Array.make flowgraph.size (Set.empty ()) in
  for i=0 to flowgraph.size-1 do
    match Set.toList (Array.get tmp i) with
      (* unreachable nodes will yield large sets here - oh well *)
      j::_ -> Array.set idom j (Set.insert (Array.get idom j) i)
    | [] -> ()
  done;
  (Array.get tmp, Array.get idom)

(* Muchnick's Domin_Fast, 7.16 *)
let dominFast flowgraph =
  let n0 = flowgraph.size in (* a new node (not in the flowgraph) *)
  let nnodes   = flowgraph.size+1 in

  let succ = flowgraph.succ in
  let pred = flowgraph.pred in

  let ndfs     = Array.create nnodes 0 in
  let parent   = Array.create nnodes 0 in
  let sdno     = Array.create nnodes 0 in
  let idom     = Array.create nnodes 0 in
  let bucket   =
    Array.init nnodes (fun _ -> Set.dextend (Set.empty ()) nnodes) in
  let ancestor = Array.create nnodes 0 in
  let label    = Array.create nnodes 0 in
  let child    = Array.create nnodes 0 in
  let size     = Array.create nnodes 0 in

  let n = ref 0 in
  let rec depthFirstSearchDom v =
    n := !n + 1;
    sdno.(v) <- !n;
    ndfs.(!n) <- v; label.(v) <- v;
    ancestor.(v) <- n0; child.(v) <- n0;
    size.(v) <- 1;
    List.iter (fun w ->
      if sdno.(w) = 0 then (parent.(w) <- v; depthFirstSearchDom w;))
      succ.(v);
  in

  let rec compress v =
    if ancestor.(ancestor.(v)) <> n0 then
      begin
	compress ancestor.(v);
	if sdno.(label.(ancestor.(v))) < sdno.(label.(v)) then
	  label.(v) <- label.(ancestor.(v));
	ancestor.(v) <- ancestor.(ancestor.(v))
      end
  in

  let rec eval v =
    if ancestor.(v) = n0 then
      label.(v)
    else begin
      compress v;
      if sdno.(label.(ancestor.(v))) >= sdno.(label.(v)) then
	label.(v)
      else label.(ancestor.(v))
    end
  in

  let link v w =
    let s = ref w in
    while sdno.(label.(w)) < sdno.(label.(child.(!s))) do
      if size.(!s) + size.(child.(child.(!s))) >= 2 * size.(child.(!s)) then
	(ancestor.(child.(!s)) <- !s;
	 child.(!s) <- child.(child.(!s)))
      else
	(size.(child.(!s)) <- size.(!s);
	 ancestor.(!s) <- child.(!s); s := child.(!s));
    done;
    label.(!s) <- label.(w);
    size.(v) <- size.(v) + size.(w);
    if size.(v) < 2 * size.(w) then begin
      let tmp = !s in
      s :=  child.(v);
      child.(v) <- tmp;
    end;
    while !s <> n0 do
      ancestor.(!s) <- v;
      s := child.(!s);
    done;
  in

  depthFirstSearchDom flowgraph.entry;
  let i = ref !n in
  while !i>=2 do
    let w = ndfs.(!i) in
    List.iter (fun v ->
      let u = eval v in
      if sdno.(u) < sdno.(w) then sdno.(w) <- sdno.(u);)
      pred.(w);
    Set.dinsert bucket.(ndfs.(sdno.(w))) w;
    link parent.(w) w;
    while not (Set.equal bucket.(parent.(w)) (Set.empty())) do
      let v =
	match Set.toList (bucket.(parent.(w))) with
	  x::_ -> x
	| [] -> failwith "dominFast" in
      Set.dremove bucket.(parent.(w)) v;
      let u = eval(v) in
      idom.(v) <- if sdno.(u) < sdno.(v) then u else parent.(w);
    done;

    i := !i - 1;
  done;

  for i=2 to !n do
    let w = ndfs.(i) in
    if idom.(w) <> ndfs.(sdno.(w)) then idom.(w) <- idom.(idom.(w));
  done;

  let idomOf = Array.create flowgraph.size (Set.empty ()) in
  for i=0 to flowgraph.size-1 do
    if i <> flowgraph.entry then begin
      let k = idom.(i) in
      idomOf.(k) <- Set.insert idomOf.(k) i;
    end;
  done;

(*
  (Array.get idomOf,
   fun i -> if i = flowgraph.entry then
     Set.empty ()
   else Set.singleton (Array.get idom i))
*)
  (Array.get idomOf,
   fun i -> if i = flowgraph.entry then
     0
   else Array.get idom i)

(* inefficient computation of postorder ordering of idom tree *)
let postorderSlow flowgraph idom =
  let rec scan n = List.concat (List.map scan (Set.toList (idom n)) @ [[n]]) in
  scan flowgraph.entry

(* better computation of postorder ordering of idom tree *)
let postorderFast flowgraph idom =
  let idomList n = Set.toList (idom n) in
  let rec scan = function
      ([], acc) -> acc
    | (hd::tl, acc) -> scan (tl, scan (idomList hd, hd::acc))
  in
  scan (idomList flowgraph.entry, [flowgraph.entry])

let postorder f i =
  print_string "Computing postorder (comparing fast and slow versions)!\n";
  let ps = postorderSlow f i in
  let pf = postorderFast f i in
  let name n = Printf.sprintf "node_%d" n in
  print_string ("(slow) " ^ String.concat " " (List.map name ps) ^ "\n");
  print_string ("(fast) " ^ String.concat " " (List.map name pf) ^ "\n");
  if ps = pf then pf else failwith "postorder failed!"

(* Muchnick's Dom_Front, Fig 8.20
   computes dominance frontier function for flowgraph nodes *)
let domFront flowgraph idomOf postord =
  let df = Array.make flowgraph.size (Set.empty ()) in
  let outerloop p_i =
    let update y =
      if not (Set.contains (idomOf p_i) y) then
	Array.set df p_i (Set.insert (Array.get df p_i) y) in
    (* compute local component *)
    Set.iter update (Set.fromList (Array.get flowgraph.succ p_i));
    (* add on up component *)
    let loop z = Set.iter update (Array.get df z) in
    Set.iter loop (idomOf p_i) in
  List.iter outerloop postord;
  Array.get df

(* Muchnick's DF_Set, Fig 8.20 *)
let dfSet domfront s = Set.union (List.map domfront (Set.toList s))

(* Muchnick's DF_Plus, Fig 8.20 *)
let dfPlus domfront s =
    let rec loop dfp =
      let d = dfSet domfront (Set.union2 (s, dfp)) in
      if Set.equal d dfp then dfp else loop d in
    loop (dfSet domfront s)

let analyze flowgraph =
(*
  let domin = domComp flowgraph in
  let (idomOf, idom) = idomComp flowgraph domin in
*)
(*  let (idom, idomOf) = dominFast flowgraph in*)
  let (idomOf, idom) = dominFast flowgraph in

  let postord = postorderFast flowgraph idomOf in
  let domfront = domFront flowgraph idomOf postord in
  {dfplus=dfPlus domfront; idom=idom; idomOf=idomOf; postorder=postord}

open Cil
open Pretty
class gatherSuccPredClass succ pred son lva = object
	inherit nopCilVisitor
	method vstmt v =
		succ.(v.sid) <- List.map (fun s -> s.sid) v.succs ;
		pred.(v.sid) <- List.map (fun s -> s.sid) v.preds ;
		son.(v.sid) <- ref v ;
		DoChildren
end

let computeDominance f =
(* spr: temporarily commented out because I don't know what it does *)
(*	let size = match f.smaxstmtid with
		Some(i) -> i
	| None -> failwith "computeDominanceFrontier: smaxstmtid = None"
	in
*)
(* spr: temporarily replacing the above code with the following line: *)
  let size = 10 in

(*	Printf.printf "%s size = %d\n" f.svar.vname size ; *)
	let succ = Array.make size [] in
	let pred = Array.make size [] in
	let stmt_of_node = Array.make size (ref dummyStmt) in
	let lvalue_of_loop = Array.make size [] in
	let gatherSuccPred = (new gatherSuccPredClass succ pred stmt_of_node
		lvalue_of_loop) in
	ignore (visitCilBlock gatherSuccPred f.sbody) ;
  let flowgraph = {
		entry = 0;
		size =  size;
		succ = succ;
		pred = pred; }
	in
  let di = analyze (flowgraph) in
(*
	let result = Array.make size [] in
	for i = 0 to (size-1) do
		let dom = di.idom i in
		let l = Set.toList dom in
		ignore ( Pretty.printf "Node[%d] idom: %a\n"
			i (docList (chr ',' ++ break) (fun x -> dprintf "%d" x)) l)  ;
	done ;
	for i = 0 to (size-1) do
		let this_set = Set.singleton i in
		let dfplus = di.dfplus this_set in
		let l = Set.toList dfplus in
		result.(i) <- l ;
		let changed_by_this_stmt = match (!(stmt_of_node.(i))).skind with
			Instr(il) -> List.fold_left (fun acc elt -> match elt with
				Set(lv,_,_) -> lv :: acc
			| Call(Some(lv),_,_,_) -> lv :: acc
			| Call(_) -> acc
			| Asm(_,_,(sll),_,_,_) -> (List.map (fun (s,lv) -> lv) sll) @ acc
			) [] il
		| _ -> []
		in
		List.iter (fun elt ->
			lvalue_of_loop.(elt) <- changed_by_this_stmt @
				lvalue_of_loop.(elt)
		) l ;
		Pretty.printf "Node[%d] dfplus: %a\n"
			i (docList (chr ',' ++ break) (fun x -> dprintf "%d" x)) l
	done ;
*)
	di.idom (* result, stmt_of_node, lvalue_of_loop *)
