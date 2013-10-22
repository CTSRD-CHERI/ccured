(*
 * Copyright (c) 2002-2003,
 *  Simon Goldsmith     <sfg@cs.berkeley.edu>
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


(*
 * this analysis eliminates array bound checks when it can prove that
 * they will always succeed
 *
 * todo: write graph slicer (for dot files -- only reachable or reaching nodes)
 * SIZE constraints on fn parameters
 * deal with values behind pointers and in structures (invalidate a lot!)
 * SIZE constraints on structure fields
 *
 *)

open Pretty
open Cil
module E = Errormsg
module H = Hashtbl
module P = Ptranal

(* flags *)
let elimabc = ref true (* whether to do this stage at all *)
let removeAllMatchedChecks = ref false (* for performance uppper bounds *)
let magicflag = ref 0

let debug = ref true
let debugx = ref false
let gdebug = ref false (* print graph reachability spew if true *)
let grdebug = ref true (* print graph reduction  spew if true *)
let printcfgs = ref false (* whether to print cfgs for all functions *)
let dumpvargraph = ref false
let printStats = ref true (* print stats at the end *)

(* stats *)
let totalChecks = ref 0
let eligibleChecks = ref 0
let matchedChecks = ref 0
let redundantChecks = ref 0
let changedChecks = ref 0
let goofed_fns = ref 0 (* functions whose analysis terminates with an uncaught exception *)

(*********************************************************************)

let currentFnName = ref ""
let currentFileName = ref ""
let stmts = ref [] (* for easy traversal of all stmts *)

(* indicates that an expression isn't of the form that we can match *)
exception NoMatch


(*-----------------------------------------------------------------*)
let starts_with (s : string) (prefix : string) : bool =
  let len_s = String.length s in
  let len_p = String.length prefix in
  let rec strcmp pos =
    pos >= len_p ||
    (s.[pos] == prefix.[pos] && strcmp (pos+1))
  in
  len_p <= len_s && strcmp 0


(* Decide whether a call is a CHECK_something *)
let isCheckCall_str s = starts_with s "CHECK_"
let isInstrCheck : instr -> bool = function
    Call (_,Lval(Var x,_),args,l) when isCheckCall_str x.vname -> true
  | _ -> false

let checkLoc (i : instr) : location =
  match i with
    | Call (_,_,_,loc) when isInstrCheck i -> loc
    | _ -> failwith "checkLoc called on non-check\n"



(* misc *)
let isIntType (vi:varinfo) : bool =
  (match unrollTypeDeep vi.vtype with TInt _ -> true | _ -> false)

let isPAType (vi:varinfo) : bool =
  (match unrollTypeDeep vi.vtype with (TPtr _ | TArray _) -> true | _ -> false)

let mapString f s =
  let copy_s = String.copy s in
  let rec ms' x i =
    if (i>=0) then (x.[i] <- f(x.[i]); ms' x (i-1)) else ()
  in
    ms' copy_s (-1 + String.length copy_s);
    copy_s

let chomp_suffix s suf =
  if Filename.check_suffix s suf then
    (Filename.chop_suffix s suf)
  else
    s

let filter_fn_name s =
  mapString (fun c -> if c='/' || c='*' then 'x' else c) s

let filter_file_name s =
  chomp_suffix (chomp_suffix s ".i") ".c"
;;

(**************************************************************)
(*                                                            *)
(*  type and helpers for variable/constraint graph            *)
(*                                                            *)
(**************************************************************)

type node_kind =
    Phi | Pi | Assign
  | PtrPhi | PtrPi | PtrAssign
  | Zero | PosInfty | NegInfty
                         (* lb   lb ov ub   ub ov *)
and edge = node ref * int
and cedge = (node ref * int *bool*bool*bool*bool)
and jedge = node ref
and node = {
  mutable nnum : int;

  mutable nvar : varinfo option;
  mutable ninum : int; (* instruction number *)

  mutable nkind : node_kind;

  (* regular edges -- good for upper and lower bound checks *)
  mutable nsuccs : edge list;
  mutable npreds : edge list;

  (* constrained edges -- arise from check or if *)
  mutable csuccs : cedge list;
  mutable cpreds : cedge list;

  (* join edges -- arise from phi/ptrphi nodes -- order matters for these *)
  mutable jsuccs : jedge list;
  mutable jpreds : jedge list;

  mutable nvisit : int option;

  mutable diamonds : (bool*bool*bool*bool);
  mutable hexagons : (bool*bool*bool*bool);
  mutable tainted : (bool*bool*bool*bool);
}
;;

(*
 * upper bound checks
 *      assign edge y--[c]-->x means y+c >= x
 *      if edge     y--[c]-->x means y+c >= x
 * lower bound checks
 *      assign edge y--[c]-->x means y+c <= x (reverse dir, opp sign)
 *      if edge     y--[c]-->x means y+c >= x (same as ub)
 *
 * There is only one node per pointer.  Edges from pointer nodes to
 * non-pointer nodes are only induced by checks or __SIZE annotations.
 * Whether an edge "counts" for a particular traversal depends on whether
 * we're trying to eliminate an  upper bound check or a lower bound check.
 * In particular, edges induced by checks only count for eliminating checks
 * of the same kind  (ub, lb, no overflow ub/lb).  The decision is
 * encapsulated in the  node_succs and node_preds functions.
 *
 *)
(* if edges have one bit of strangeness
 *  we must not return an if edge from
 *       (int)--x-->(0) nor (0)--x-->(p.last) for ub checks
 *   (p.first)--x-->(0) nor (0)--x-->(int)    for lb checks
 *
 *  such edges do not help prove ub/lb assertions and
 *  lead to bogus paths through the graph
 * e.g. if (x<c) leads to (x)<--[0]--(xf)<--[-c+1]--(0)--[c]-->(xt)--[0]-->(x)
 *         true: xt <= c-1 false: xf >= c
 *
 * result: if edges must have suitable ub/lb labels
 * sfg: I no longer understand the example, but the extra edges don't help
 *)

let match_edge_con (lb,lbov,ub,ubov) (targ,w,lb',lbov',ub',ubov') =
  ((not ub)||ub') && ((not ubov)||ubov')
  && ((not lb)||lb') && ((not lbov)||lbov')

let edge_proj (targ,w,lb',lbov',ub',ubov') = (targ,w)
let zip_zero = List.map (fun x -> (x, 0))
let zip_trues = List.map (fun (a,b) -> (a,b,true,true,true,true))

let node_succs (n: node) ~(lb: bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) ~(jedges:bool) : (node ref * int) list =
  List.rev_append (if jedges then (zip_zero n.jsuccs) else [])
    ( List.rev_append
	(List.map edge_proj (List.filter (match_edge_con (lb,lbov,ub,ubov)) n.csuccs))
	n.nsuccs
    )


let node_preds (n: node) ~(lb: bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) ~(jedges:bool) : (node ref * int) list =
  List.rev_append (if jedges then (zip_zero n.jpreds) else [])
    ( List.rev_append
	(List.map edge_proj (List.filter (match_edge_con (lb,lbov,ub,ubov)) n.cpreds))
	n.npreds
    )

(* preds and succs with constraints.  all true for unconstrained *)
let node_csuccs (n: node) = List.rev_append n.csuccs (zip_trues n.nsuccs)
let node_cpreds (n: node) = List.rev_append n.cpreds (zip_trues n.npreds)

(***)
let node_ctr = ref 10
let new_nnum () = begin incr node_ctr; !node_ctr end

let varnodes : (int, node ref) H.t = H.create 100
let ptrphi_nodes : (int, node ref) H.t = H.create 20
let phi_nodes : (int, node ref) H.t = H.create 20

let addNode (nr : node ref) = H.add varnodes !nr.nnum nr

let newNode' (vio : varinfo option) (nnum:int) (inum:int) (o:node_kind) : node =
  { nnum=nnum; nvar=vio; ninum=inum; nkind=o;
    nsuccs=[]; npreds=[]; csuccs=[]; cpreds=[]; jsuccs=[]; jpreds=[];
    diamonds=(false,false,false,false); hexagons=(false,false,false,false);
    tainted=(false,false,false,false);
    nvisit=None; }

let newNode (vi:varinfo) (inum:int) (o:node_kind) : node ref =
  let nr = ref (newNode' (Some vi) (new_nnum()) inum o) in
    addNode nr;
    (match o with
       | Phi -> H.add phi_nodes inum nr
       | PtrPhi -> H.add ptrphi_nodes inum nr
       | _ -> ());
    nr

(* node for var at top of function -- never ok to diamond from/to one of these *)
(* cheap hack: entry nodes not added to ptr/phi_nodes and thus not
 *   diamond/hexagon-ed
 * maybe they needn't be phi/ptrphi nodes?
 *)
let newEntryNode (vi:varinfo) (inum:int) (o:node_kind) : node ref =
  let nr = newNode vi inum o in
    !nr.tainted <- (true, true, true, true);
    nr

(* some presets: zero, +infinity, -infinity
 * the node numbers for these are arbitrary, but should be distinct and
 * consistent
 *)
let newZeroNode () : node =
  newNode' None 0 0 Zero

(* invariant: posInftyNode has no preds (so backward search always returns failure) *)
let newPosInftyNode () : node =
  newNode' None 1 1 PosInfty

(* invariant: negInftyNode has no succs (so forward search always returns failure) *)
let newNegInftyNode () : node =
  newNode' None (-1) (-1) NegInfty

let isInfinity (n:node) : bool =
  match n.nkind with
    | (PosInfty|NegInfty) -> true
    | _ -> false


let zeroNode = ref (newZeroNode())
let posInftyNode = ref (newPosInftyNode())
let negInftyNode = ref (newNegInftyNode())


(* add a regular edge from n1 to n2 with weight c *)
let addedEdge (n1 : node ref) (n2 : node ref) (weight : int) : bool =
  if not ( (n1==n2)
           || isInfinity !n1
           || isInfinity !n2
           || (List.mem (n2,weight) !n1.nsuccs)
         )
  then
    begin
      !n1.nsuccs <- (n2, weight) :: (!n1.nsuccs);
      !n2.npreds <- (n1, weight) :: (!n2.npreds);
      true
    end
  else false

let addEdge n1 n2 w = ignore(addedEdge n1 n2 w)

(* add constrainted edge (e.g. only for u.b.) *)
let addedCEdge (n1 : node ref) (n2 : node ref) (w : int)
  ~(lb:bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) : bool =
  begin
    if (lb&&lbov&&ub&&ubov) then addedEdge n1 n2 w else
    if not (lb||lbov||ub||ubov) then false else
    (* check for dups - makes traversal more reasonable and the graph nicer *)
    if not ( (n1==n2)
             || isInfinity !n1
             || isInfinity !n2
             || (List.mem (n2, w, lb,lbov,ub,ubov) !n1.csuccs)
           )
    then
      begin
        !n1.csuccs <- (n2, w, lb,lbov,ub,ubov) :: (!n1.csuccs);
        !n2.cpreds <- (n1, w, lb,lbov,ub,ubov) :: (!n2.cpreds);
        true
      end
    else false
  end

let addCEdge n1 n2 w   ~(lb:bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) =
  ignore(addedCEdge n1 n2 w ~lb:lb ~lbov:lbov ~ub:ub ~ubov:ubov)

(* combine cedges with same target and weight *)
let cleanup_cedges (n : node) =
  let rec reduce_cedges' ((nr,w,a,b,c,d) as e : cedge) (es : cedge list) (acc : cedge list) =
    match es with
      | [] -> e::acc
      | ((nr',w',a',b',c',d') :: es') when nr=nr' && w=w' ->
          reduce_cedges' (nr,w,a||a',b||b',c||c',d||d') es' acc
      | e'::es' ->
          reduce_cedges' e' es' (e::acc)
  in
  let reduce_cedges = function
    | [] -> []
    | e::es -> reduce_cedges' e es []
  in
  let comp ((n1,w1, _,_,_,_) as _e1) ((n2,w2,_,_,_,_) as _e2) =
    if (n1=n2 && w1=w2) then 0
    else let res = compare n1 n2 in
      if res=0 then compare w1 w2
      else res
  in
    begin
      n.csuccs <- reduce_cedges (List.sort comp n.csuccs);
      n.cpreds <- reduce_cedges (List.sort comp n.cpreds);
    end


(*
 * add a special (cf join) edge from n1 to n2
 * need to actually add infinity edges to avoid bad applications of diamond rule
 *)
let addJEdge (n1 : node ref) (n2 : node ref) : unit =
  if not ( (n1==n2) || (List.mem n2 !n1.jsuccs) ) then
  begin
    !n1.jsuccs <- n2 :: (!n1.jsuccs);
    !n2.jpreds <- n1 :: (!n2.jpreds);
  end


let addAssignEdge n1 n2 w = addEdge n1 n2 w

(* NB: if edges are interpreted in reverse for lb's!
 *
 * unhelpful IF edges are not added (see also comment above)
 *)
let addIfEdge n1 n2 w =
  let (lb, ub) =
    match (!n1.nkind, !n2.nkind) with

      (* ptr >= 0 >= int ok for ub *)
      | (PtrPi|PtrAssign|PtrPhi), Zero -> false, true
      | Zero, (Pi|Assign|Phi) ->  false, true

      (* ptr <= 0 <= int ok for lb *)
      | (Pi|Assign|Phi), Zero -> true, false
      | Zero, (PtrPi|PtrAssign|PtrPhi) -> true, false

      | _ -> true, true
  in begin
    if lb then (* if edges flip direction and sign of weight for lb *)
      addCEdge n2 n1 (-w) ~lb:true ~lbov:true ~ub:false ~ubov:false;
    if ub then
      addCEdge n1 n2 w ~lb:false ~lbov:false ~ub:true ~ubov:true;
    end

let clearVisit () = H.iter (fun _ nr -> !nr.nvisit <- None) varnodes

let clearVarGraph () =
  begin
    H.clear varnodes;
    H.clear ptrphi_nodes;
    H.clear phi_nodes;
    zeroNode := newZeroNode();
    posInftyNode := newPosInftyNode();
    negInftyNode := newNegInftyNode();
    addNode zeroNode;
    addNode posInftyNode;
    addNode negInftyNode;
  end

let _ = clearVarGraph()
;;


(* do some cleanup on the graph to make it more readable -- dump lots of
 * edges
 * this function makes the graph unusable for check elimination
 * and is only done to make the dump nicer right before the graph is cleared
 *)
let untransclose () =
  let doNode _ (n : node ref) : unit =
    (* transfer csucc with all true to nsucc *)
    !n.nsuccs <- List.rev_append (!n.nsuccs)
                      ( List.map (fun (s,w,_,_,_,_) -> (s,w))
                             (List.filter (fun (s,w,a,b,c,d) -> a && b && c && d) !n.csuccs) );
    !n.csuccs <- List.filter (fun (s,w,a,b,c,d) -> not (a && b && c && d)) !n.csuccs;

    (* remove transitive csucc edges *)
    !n.csuccs <- List.filter (fun (s,w,a,b,c,d) ->
                      not (List.exists (fun (n',w',a',b',c',d') ->
                               List.exists (fun (n'',w'',a'',b'',c'',d'') ->
                                    n''==s && w'+w''=w
                                      && ((not a) || (a'&&a''))
                                      && ((not b) || (b'&&b''))
                                      && ((not c) || (c'&&c''))
                                      && ((not d) || (d'&&d''))
                               ) (node_csuccs !n')
                      ) (node_csuccs !n)
                 )) !n.csuccs;

    (* remove transitive nsucc edges *)
    !n.nsuccs <- List.filter (fun (s,w) ->
                      not (List.exists (fun (n',w') ->
                               List.exists (fun (n'',w'') ->
                                    n''==s && w'+w''=w
                               ) !n'.nsuccs
                          ) !n.nsuccs
                 )) !n.nsuccs;
  in begin
      H.iter doNode varnodes;
    end
;;


(**************************************************************)
(*                                                            *)
(*  printing the variable graph (in dot/graphviz form)        *)
(*                                                            *)
(**************************************************************)

let d_intlist = d_list "_" (fun () -> num)
let d_stringlist = d_list "," (fun () -> text)
let d_vilist = d_list "," (fun () vi -> text vi.vname)

let d_nodename () (n:node) = dprintf "node_%d" n.nnum

let d_nodelabel () (n:node) =
  match (n.nkind, n.nvar) with
    | (Phi, Some vi) ->
        dprintf "%s_%d_phi" vi.vname n.ninum

    | (Pi, Some vi) ->
        dprintf "%s_%d_pi" vi.vname n.ninum

    | (Assign, Some vi) ->
        dprintf "%s_%d_assign" vi.vname n.ninum

    | (PtrPi, Some a) ->
        dprintf "%s.ptr_pi_%d" a.vname n.ninum

    | (PtrAssign, Some a) ->
        dprintf "%s.ptr_assign_%d" a.vname n.ninum

    | (PtrPhi, Some a) ->
        dprintf "%s_ptrphi_%d" a.vname n.ninum

    | (Zero, None) -> dprintf "0"

    | (PosInfty, None) -> dprintf "PositiveInfinity"

    | (NegInfty, None) -> dprintf "NegativeInfinity"

    | _ -> invalid_arg "Malformed graph node"

let d_nodereflabel () (nr : node ref) = d_nodelabel () !nr

let d_edge (from:node) () (nr,w) =
  dprintf "%a -> %a [label=\"%d\",style=solid]"
    d_nodename from
    d_nodename !nr
    w

let d_cedge (from:node) () (nr, w, lb,lbov,ub,ubov) =
  dprintf "%a -> %a [label=\"%d%s\",style=solid]"
    d_nodename from
    d_nodename !nr
    w
    ("("
     ^ (if lb then "lb," else "")
     ^ (if lbov then "lbov," else "")
     ^ (if ub then "ub," else "")
     ^ (if ubov then "ubov," else "")
     ^ ")" )

(* used for succs of PtrPhi, preds of Phi *)
let d_jedge (n1:node) () (n2r,num) =
    match (n1.nkind) with
      | PtrPhi ->
          dprintf "%a -> %a [label=\"(%d_%d\",color=red]"
          d_nodename n1
          d_nodename !n2r
          n1.ninum
          num
      | Phi ->
          dprintf "%a -> %a [label=\")%d_%d\",color=red]"
          d_nodename !n2r
          d_nodename n1
          n1.ninum
          num
      | _ ->
          dprintf "%a -> %a [label=\"??\",color=red]"
          d_nodename n1
          d_nodename !n2r
      (*| _ -> invalid_arg "join edge not connected to join node"*)

let rec number_list l n =
  match l with
    | [] -> []
    | h :: t -> (h, n) :: (number_list t (n+1))

(* print out any join edges of n if applicable
 * skip join edge if it's the only one (there'll be a regular edge) *)
let d_jedges () (n : node) =
  match (n.nkind, List.length n.jsuccs, List.length n.jpreds) with
    | (Phi, _, x) when x>1 ->
        dprintf "\n\t%a" (d_list "\n\t" (d_jedge n)) (number_list n.jpreds 1)

    | (PtrPhi, x, _) when x>1 ->
        dprintf "\n\t%a" (d_list "\n\t" (d_jedge n)) (number_list n.jsuccs 1)

    | _ ->
        Pretty.nil


let node_print_filter (n : node) =
  true
    (*  (n.nkind = Phi || n.nkind = PtrPhi) *)

let d_node () (n:node) =
  if ( List.length n.nsuccs = 0 && List.length n.npreds = 0
        && List.length n.csuccs = 0 && List.length n.cpreds = 0
        && List.length n.jsuccs = 0 && List.length n.jpreds = 0
     ) then Pretty.nil
  else
    if (node_print_filter n) then (* debug: filter nodes *)
      dprintf "%a [label=\"%a\" shape=%s]\n\t%a\n\t%a%a"
        d_nodename n
        d_nodelabel n
        (match n.nkind with Phi -> "box" | PtrPhi -> "ellipse" | _ -> "plaintext")
        (d_list "\n\t" (d_edge n)) n.nsuccs
        (d_list "\n\t" (d_cedge n)) n.csuccs
        d_jedges n
    else
      Pretty.nil

let dumpVarGraph () =
  let graphOutChannel = open_out (!currentFileName ^ "vargraph." ^
                                  !currentFnName ^ ".dot") in
  let graphOut s = output_string graphOutChannel s in
  let printNode _ nr = graphOut (sprint ~width:80 (dprintf "%a\n" d_node !nr)) in
    begin
      (*if !graphCleanup then*) untransclose();
      graphOut("digraph variables_" ^ !currentFnName ^ " {\n");
      H.iter printNode varnodes;
      graphOut("}\n");
      close_out graphOutChannel;
    end
;;


(*******************************************************************)
(*                                                                 *)
(* graph traversal: transitive closure, diamond and hexagon rules  *)
(*                                                                 *)
(*******************************************************************)

(*
 * Is there a path from src to dest of weight
 *   >= len (l.b.)
 *   <= len (u.b.)
 *)

(*
 * generic traveral, (twiddle next to make forward / backward)
 *   call visit on each node with path length so far (w)
 *   return (n,w) if visit returns true, continue if false
 *   call next on node to get successors
 *)
let rec traverse (next) (visit) (nr : node ref) (w : int) ~(jedges:bool)
  ~(lb:bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) =

  (* follow each edge in succs *)
  let rec traverse' (succs) =
    match succs with
      | [] -> None
      | (succ,sw, lb',lbov',ub',ubov') :: rest -> begin
	  match (traverse next visit succ (w+sw) ~jedges:jedges ~lb:(lb&&lb') ~lbov:(lbov&&lbov') ~ub:(ub&&ub') ~ubov:(ubov&&ubov')) with
	    | None -> traverse' rest
	    | Some x -> Some x
	end
  in
    begin
      if (lb||lbov||ub||ubov) then (* that last constraint edge was allowed *)
	match !nr.nvisit with
	  | Some(oldw) -> (* been here *) None
	  | None ->
	      !nr.nvisit <- Some w;
	      let res =
		if (visit nr w ~lb:lb ~lbov:lbov ~ub:ub ~ubov:ubov) then
		  Some (nr,w)
		else
		  traverse' (next !nr)
	      in
		!nr.nvisit <- None;
		res
      else
	None
    end

let trans_close_node_forward (start : node ref) : unit =
  let add_trans_edge nr w ~(lb:bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) =
    begin addCEdge start nr w ~lb:lb ~lbov:lbov ~ub:ub ~ubov:ubov; false end
  in
    clearVisit();
    ignore (traverse (node_csuccs) (add_trans_edge) (start) (0) ~lb:true ~lbov:true ~ub:true ~ubov:true ~jedges:false)

let trans_close_node_backward (start : node ref) : unit =
  let add_trans_edge nr w ~(lb:bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) =
    begin addCEdge nr start w ~lb:lb ~lbov:lbov ~ub:ub ~ubov:ubov; false end
  in
    clearVisit();
    ignore (traverse (node_cpreds) (add_trans_edge) (start) (0) ~lb:true ~lbov:true ~ub:true ~ubov:true ~jedges:false)

let do_transclose () =
  let do_tc_node _ (nr : node ref) =
    match !nr.nkind with
      | Phi -> List.iter trans_close_node_backward !nr.jpreds
      | PtrPhi -> List.iter trans_close_node_forward !nr.jsuccs
      | _ -> ()
  in
    H.iter do_tc_node varnodes

let do_full_transclose () =
    H.iter (fun _ nr -> trans_close_node_forward nr) varnodes
;;

(* diamond rules *)
let s_bool (b) = if b then "T" else "F"
let d_c4 () (a,b,c,d) = dprintf "%s%s%s%s" (s_bool a) (s_bool b) (s_bool c) (s_bool d)
let print_cedge () (nr, w, lb, lbov, ub, ubov) =
  dprintf "[%a, w=%d, c=%a]" d_nodelabel !nr w d_c4 (lb,lbov,ub,ubov)

let compare4bool (a1,b1,c1,d1) (a2,b2,c2,d2) =
  (a1&&a2) || (b1&&b2) || (c1&&c2) || (d1&&d2)

let or4 (a1,b1,c1,d1) (a2,b2,c2,d2) =
  (a1||a2, b1||b2, c1||c2, d1||d2)

let and4 (a1,b1,c1,d1) (a2,b2,c2,d2) =
  (a1&&a2, b1&&b2, c1&&c2, d1&&d2)


exception GiveUp of string

(*
 * apply diamond rules until fixed point
 *   keep jpreds of phis backward transitive closed, jsuccs/ptrphis/forward
 *
 * lb:
 *   pos,zero weight cycles harmless; neg weight cycles bad
 *   edge x --[c]--> y means  x+c <= y
 *   want to show: p+c <= x, suffices to show: p+d <= x for d >= c
 *   i.e. min weight is weakest condition on diamond
 *
 * ub:
 *   neg,zero weight cycles harmless; pos weight cycles bad
 *   edge x --[c]--> y means  x+c >= y
 *   wts: p+c >= x, sts: p+d >= x and d <= c
 *   i.e. max weight is weakest condition on diamond
 *
 *)
let do_diamonds () : unit =

  (* if given a bad cycle edge, update tainted OR if we've already formed a diamond, give up*)
  let do_taint (phi_node : node ref) (for_lb : bool) (dest, w, lb, lbov, ub, ubov) : unit =
    if (dest=phi_node) then
      if (for_lb && (lb||lbov) && w<0) then
          if (compare4bool !phi_node.diamonds (lb,lbov,false,false)) then
            raise (GiveUp "LB diamond already created, but just found bad cycle")
          else if (compare4bool !phi_node.hexagons (lb,lbov,false,false)) then
            raise (GiveUp "LB hexagon already created, but just found bad cycle")
          else
            !phi_node.tainted <- or4 !phi_node.tainted (lb, lbov, false, false)
      else if ((not for_lb) && (ub||ubov) && w>0) then
        if (compare4bool !phi_node.diamonds (false,false,ub,ubov)) then
          raise (GiveUp "UB diamond already created, but just found bad cycle")
        else if (compare4bool !phi_node.hexagons (false,false,ub,ubov)) then
          raise (GiveUp "UB hexagon already created, but just found bad cycle")
        else
          !phi_node.tainted <- or4 !phi_node.tainted (false, false, ub, ubov)
      else ()
    else ()
  in

  (* used to filter out impossible (all false) edges  *)
  let possible_edge (for_lb : bool) (dest, w, lb, lbov, ub, ubov) : bool =
    if for_lb then
      (lb||lbov)
    else
      (ub||ubov)
  in

  (* constrain edge to non-tainted paths *)
  let apply_taint (lb',lbov',ub',ubov') (dest, w, lb, lbov, ub, ubov) =
    (dest, w, (not lb')&&lb, (not lbov')&&lbov, (not ub')&&ub, (not ubov')&&ubov)
  in

  (* take intersection of edge_lists, join weights & conjoin constraints according to pick_edges *)
  let join_inter_list (pick_edges) (edge_lists) =
    let join_inter ns ms =
      if (!grdebug) then ignore(E.log " ns: %a\n ms: %a\n" (d_list " " print_cedge) ns (d_list " " print_cedge) ms);
      let res = List.fold_left (pick_edges ms) [] ns in
        if (!grdebug) then ignore(E.log " res: %a\n\n" (d_list " " print_cedge) res);
        res
    in
      match edge_lists with
        | [] -> []
        | el :: els -> List.fold_left join_inter el els
  in

  (* used to filter jsuccs/jpreds of ptrphi/phi node to those without harmless (i.e. ignorable)  cycles *)
  (* for the moment fail to ignore constrained cycles *)
  let non_ignored_js (phi_node : node ref) (for_lb : bool) (cnext) (j : node ref) =
    if for_lb then
      not (List.exists (fun (nr,w,lb,lbov,_,_) -> nr=phi_node && w>=0 && lb && lbov) (cnext !j))
    else
      not (List.exists (fun (nr,w,_,_,ub,ubov) -> nr=phi_node && w<=0 && ub && ubov) (cnext !j))
  in

  (*
   * highly parameterized aaplication of diamond rule for lb/ub and ptrphi/phi
   *
   * update tainted-ness, check for bad situation (apply diamond rule, later find bad cycle)
   * take the joined intersection of phi_node's non-ignorable nexts
   *  filter that based on tainted and prune out impossible paths
   *  add the edges
   *)
  let diamonds (phi_node : node ref)
    (cnext : node -> cedge list)
    (jnext : node -> node ref list)
    (add_d_edge : bool -> cedge -> bool)
    (for_lb : bool)
    (pick_edges : cedge list -> cedge list -> cedge -> cedge list) =
    begin
      List.iter (fun j -> List.iter (do_taint phi_node for_lb) (cnext !j)) (jnext !phi_node);

      List.fold_left add_d_edge false
        (List.filter (possible_edge for_lb)
           (List.map (apply_taint !phi_node.tainted)
              (join_inter_list pick_edges
                 (List.map (fun nr -> (nr, 0, for_lb, for_lb, not for_lb, not for_lb) :: (cnext !nr))
                    (List.filter (non_ignored_js phi_node for_lb cnext)
                       (jnext !phi_node) )))))

    end
  in

  let lb_diamonds (phi_node : node ref) (cnext) (jnext) (add_d_edge) =
    let rec lb_pick_edges (es) (acc) ((nr,w,lb,lbov,_,_) as e) =
      match es with [] -> acc
        | (nr',w',lb',lbov',_,_) :: rest ->
            if (nr=nr' && ((lb&&lb')||(lbov&&lbov'))) then
              lb_pick_edges rest ((nr, min w w', lb&&lb', lbov&&lbov', false, false) :: acc) e
            else
              lb_pick_edges rest acc e
    in
      diamonds phi_node cnext jnext add_d_edge true lb_pick_edges
  in

  let ub_diamonds (phi_node : node ref) (cnext) (jnext) (add_d_edge) =
    let rec ub_pick_edges (es) (acc) ((nr,w, _, _, ub,ubov) as e) =
      match es with [] -> acc
        | (nr',w',_, _,ub',ubov') :: rest ->
            if (nr=nr' && ((ub&&ub')||(ubov&&ubov'))) then
              ub_pick_edges rest ((nr, max w w', false, false, ub&&ub', ubov&&ubov') :: acc) e
            else
              ub_pick_edges rest acc e
    in
      diamonds phi_node cnext jnext add_d_edge false ub_pick_edges
  in

  let changed = ref true in

  let do_lb_diamond _ (phi_node : node ref) =
    let add_d_edge phifirst (acc) (dn, w, lb, lbov, _, _) =
      let (n1, n2) = if phifirst then (phi_node, dn) else (dn, phi_node) in
      let res = addedCEdge n1 n2 w ~lb:lb ~lbov:lbov ~ub:false ~ubov:false
      in begin
          if (res) then !phi_node.diamonds <- or4 !phi_node.diamonds (lb, lbov, false, false);
          acc || res
          end
    in
    if (match !phi_node.nkind with
          | Phi ->
              lb_diamonds (phi_node) (node_cpreds) (fun n -> n.jpreds) (add_d_edge false)

          | PtrPhi ->
              lb_diamonds (phi_node) (node_csuccs) (fun n -> n.jsuccs) (add_d_edge true)

          | _ -> false)
    then begin
      do_transclose();
      changed := true;
    end else ()
  in

  let do_ub_diamond _ (phi_node : node ref) =
    let add_d_edge phifirst acc (dn, w, _, _, ub, ubov) =
      let (n1, n2) = if phifirst then (phi_node, dn) else (dn, phi_node) in
      let res = addedCEdge n1 n2 w ~lb:false ~lbov:false ~ub:ub ~ubov:ubov
      in begin
          if (res) then !phi_node.diamonds <- or4 !phi_node.diamonds (false, false, ub, ubov);
          acc || res
        end
    in
    if (match !phi_node.nkind with
          | Phi ->
              ub_diamonds (phi_node) (node_cpreds) (fun n -> n.jpreds) (add_d_edge false)

          | PtrPhi ->
              ub_diamonds (phi_node) (node_csuccs) (fun n -> n.jsuccs) (add_d_edge true)

          | _ -> false)
    then begin
      do_transclose();
      changed := true;
    end else ()
  in
    begin
      (* help, I'm looping forever *)
      if (!grdebug) then ignore(E.log "--- exhaustively applying LB diamond rules\n");
      changed := true;
      while(!changed) do
        changed := false;
        H.iter do_lb_diamond phi_nodes;
        H.iter do_lb_diamond ptrphi_nodes;
      done;

      if (!grdebug) then ignore(E.log "--- exhaustively applying UB diamond rules\n");
      changed := true;
      while(!changed) do
        changed := false;
        H.iter do_ub_diamond phi_nodes;
        H.iter do_ub_diamond ptrphi_nodes;
      done;
    end
;;


let prod_map2 (f : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list) : 'c list =
  List.flatten( List.map (fun a -> List.map (f a) ys) xs )
let prod_iter2 (f : 'a -> 'b -> unit) (xs : 'a list) (ys : 'b list) : unit =
  List.iter (fun a -> List.iter (f a) ys) xs
;;

(*
 * hexagon rule
 *
 * in the unlikely event that a negative cycle and positive cycle cancel each other
 *  in favor of the harmless way, we'll miss it
 *)
let do_hexagons () =

  let changed = ref true in

  (* find hexagon (if one exists) between ptrphi,phi *)
  let hexagons (ptrphi : node ref)  (phi : node ref)
    (join : int -> int -> int -> int -> int)
    (worse : int -> int -> int)  (better : int -> int -> int)  (worst : int)  (best : int)
    : (int*int*int*int) =

    (* use choose to accumulate weights of paths to targ *)
    let choose_path_to (choose : int -> int -> int) (targ : node ref) ((wa,wb,wc,wd) as acc) ((nr,w,a,b,c,d) as _e : cedge) =
      if (nr=targ) then
        ( (if a then choose w wa else wa),
          (if b then choose w wb else wb),
          (if c then choose w wc else wc),
          (if d then choose w wd else wd) )
      else
        acc
    in
    let worst_to (targ : node ref) =
      List.fold_left (choose_path_to worse targ) (best,best,best,best)
    in
    let best_to (targ : node ref) =
      List.fold_left (choose_path_to better targ) (worst,worst,worst,worst)
    in

    (* find best path from pn to xn, bad cycle => no path (worst), harmless cycle => ignore *)
    let hexpath (wa,wb,wc,wd) (pn : node ref) (xn : node ref) =
      let (a1,b1,c1,d1) = worst_to (ptrphi) (node_csuccs !pn) in (* cycle ptrphi->pn->ptrphi*)
      let (a2,b2,c2,d2) = worst_to (phi) (node_cpreds !xn) in (* cycle phi->xn->phi *)
      let (pa,pb,pc,pd) = best_to (xn) (node_csuccs !pn) in (* path pn -> xn *)
        (join wa pa a1 a2, join wb pb b1 b2, join wc pc c1 c2, join wd pd d1 d2)
    in
      begin
        try
          List.fold_left2 (hexpath) (best, best, best, best) (!ptrphi.jsuccs) (!phi.jpreds)
        with
          | Invalid_argument reason ->
              let _s = sprint ~width:80
                    ( dprintf
                        "hexagons (%s): [%a].jsuccs = [%a] different size than [%a].jpreds = [%a]"
                        reason
                        d_nodelabel !ptrphi
                        (d_list ", " d_nodereflabel) !ptrphi.jsuccs
                        d_nodelabel !phi
                        (d_list ", " d_nodereflabel) !phi.jpreds
                    )
              in
                (* creating a hexagon cannot create a cycle (backedge),
                 * so ignoring a hex is always sound
                 *
                 * I'm not sure where this case occurs, but I think it does
                 *)
                (*failwith s*)
                (worst, worst, worst, worst)
      end (* hexagons body *)
  in

  (* do hexagons for lb paths *)
  let lb_hexagons (ptrphi) (phi) =
    let (worse, better, worst, best) = ( min, max, min_int, max_int ) in
    let lb_join acc p c1 c2 =
      if (c1 <> best && c2 <> best && c1 <> worst && c2 <> worst) then
        if (c1+c2 < 0) then worst (*bad cycle*)
        else acc (*harmless cycle*)
      else
        worse acc p
    in
    let (lb_path, lbov_path, _, _) =
      hexagons (ptrphi) (phi)  lb_join  worse  better  worst  best
    in let lb_ok = not ( compare4bool (true,false,false,false)
                           (or4 !ptrphi.tainted !phi.tainted) )
    in let r1 =
        if (lb_ok && lb_path > min_int && lb_path < max_int) then
          addedCEdge ptrphi phi lb_path ~lb:true ~lbov:false ~ub:false ~ubov:false
        else false
    in let lbov_ok = not ( compare4bool (false,true,false,false)
                           (or4 !ptrphi.tainted !phi.tainted) )
    in let r2 =
        if (lbov_ok && lbov_path > min_int && lbov_path < max_int) then
          addedCEdge ptrphi phi lbov_path ~lb:false ~lbov:true ~ub:false ~ubov:false
        else false
    in
      if (r1 || r2) then begin
        changed := true;
        !ptrphi.hexagons <- or4 !ptrphi.hexagons (r1, r2, false, false);
        !phi.hexagons <- or4 !phi.hexagons (r1, r2, false, false);
      end else ()
  in

  (* do hexagons for ub paths *)
  let ub_hexagons (ptrphi) (phi) =
    let (worse, better, worst, best) = (max, min, max_int, min_int) in

    let ub_join acc p c1 c2 =
      if (c1 <> best && c2 <> best && c1 <> worst && c2 <> worst) then
        if (c1+c2 > 0) then worst (*bad cycle*)
        else acc (*harmless cycle*)
      else
        worse acc p
    in
    let (_, _, ub_path, ubov_path) =
      hexagons (ptrphi) (phi)  ub_join  worse  better  worst  best
    in let ub_ok = not ( compare4bool (false,false,true,false)
                           (or4 !ptrphi.tainted !phi.tainted) )
    in let r1 =
        if (ub_ok && ub_path > min_int && ub_path < max_int) then
          addedCEdge ptrphi phi ub_path ~lb:false ~lbov:false ~ub:true ~ubov:false
        else false
    in let ubov_ok = not ( compare4bool (false,false,false,true)
                             (or4 !ptrphi.tainted !phi.tainted) )
    in let r2 =
        if (ubov_ok && ubov_path > min_int && ubov_path < max_int) then
          addedCEdge ptrphi phi ubov_path ~lb:false ~lbov:false ~ub:false ~ubov:true
        else false
    in
      if (r1 || r2) then begin
        changed := true;
        !ptrphi.hexagons <- or4 !ptrphi.hexagons (false, false, r1, r2);
        !phi.hexagons <- or4 !phi.hexagons (false, false, r1, r2);
      end else ()
  in

  (* do f for all pairs of ptrphi,phi nodes at same instr num *)
  let iter_phi f =
    H.iter (fun inum ptrphi -> List.iter (f ptrphi) (H.find_all phi_nodes inum)) ptrphi_nodes
  in
    begin
      changed := true;
      while(!changed) do changed := false; iter_phi lb_hexagons; done;
      changed := true;
      while(!changed) do changed := false; iter_phi ub_hexagons; done;
    end
;;


(* ... seems to cause blowup on switch2.c ?? *)
let do_cleanup_cedges () =
    H.iter (fun _ nr -> cleanup_cedges !nr) varnodes
;;

(* reduce the graph *)
let reduce_graph () =
  begin
    if (!grdebug) then ignore(E.log "--- transitively closing phi preds / ptrphi succs\n");
    do_transclose();

    do_diamonds();

    if (!grdebug) then ignore(E.log "--- exhaustively applying hexagon rule\n");
    do_hexagons();

    if (!grdebug) then ignore(E.log "--- computing full transitive closure \n");
    do_full_transclose ();
    do_cleanup_cedges ();
  end
;;

(* check elimination query *)
let path_from_to_lt (src : node ref) (dest : node ref) (weight : int)
  ~(lb:bool) ~(lbov:bool) ~(ub:bool) ~(ubov:bool) : bool =

  let matching_edge (n', w', lb', lbov', ub', ubov') : bool =
    ( n' = dest
           && ((not (ub||ubov)) || (w' <= weight))
           && ((not (lb||lbov)) || (w' >= weight))
           && ((not lb)         || lb')
           && ((not lbov)       || lbov')
           && ((not ub)         || ub')
           && ((not ubov)       || ubov') )
  in begin
      if !gdebug then ignore(E.log "\n");
      if !gdebug then List.iter (fun e -> ignore (E.log "\t%a\n" print_cedge e)) (node_csuccs !src);
      let res = (List.length (List.filter matching_edge (node_csuccs !src)) > 0) in
        if !gdebug then
          ignore (E.log "%s: looking for %a path from [%a] to [%a] of weight %d... %s\n"
                    !currentFnName
                    d_c4 (lb,lbov,ub,ubov)
                    d_nodelabel !src
                    d_nodelabel !dest
                    weight
                    (if res then "found" else "not found")
                 );
        res
    end
;;


(*******************************************************************)
(*                                                                 *)
(* Redudant check elimination:                                     *)
(* For each check, store a continuation to run                     *)
(* when the graph is complete - return ChangeTo ...                *)
(* to eliminate/change it or DoChildren to leave it be             *)
(*                                                                 *)
(*******************************************************************)

let checkCode : (instr, unit -> instr list visitAction) H.t = (H.create 50)

let registerCheckCode (i:instr) (code) =
  H.add checkCode i code

let maybeRemoveCheck (i:instr) : instr list visitAction =
  try
    let code = H.find checkCode i in
      if !removeAllMatchedChecks then ChangeTo []
      else code()
  with
      Not_found -> DoChildren
;;


(*******************************************************************)
(*                                                                 *)
(* pattern matching on CIL expressions                             *)
(*                                                                 *)
(*******************************************************************)

let instrnum = ref 0


(*
 *
 * the new world order: return varinfo options, constants, flag if cast?
 * match_vPw two vars
 * match_vPc var plus constant
 * match_pPi ptr + intvar
 * match_pPc ptr + const
 * match_iPc intvar + const
 * match_pPiPc ptr + intvar + const
 *)



(* return (v, c) if e is of the form (variable v + constant c) *)
let rec match_vPc (e:exp) : (varinfo option * int) =
  match e with
    | Const(CInt64(c,_,_)) ->
        (None, Int64.to_int c)

    | (Lval (Var vi, NoOffset) | StartOf (Var vi, NoOffset)) ->
	(Some vi, 0)

    | BinOp ((PlusA|PlusPI|IndexPI), (Lval (Var vi, NoOffset)| StartOf (Var vi, NoOffset)), Const(CInt64(c,_,_)), _) ->
	(Some vi, Int64.to_int c)

    | BinOp ((PlusA|PlusPI|IndexPI), Const(CInt64(c,_,_)), (Lval (Var vi, NoOffset)| StartOf (Var vi, NoOffset)), _) ->
	(Some vi, Int64.to_int c)

    | BinOp ((MinusA|MinusPI), (Lval (Var vi, NoOffset)| StartOf (Var vi, NoOffset)) , Const(CInt64(c,_,_)), _) ->
	(Some vi, -Int64.to_int c)

    | _ ->
        begin
          if !debugx then
            ignore( warn "Couldn't match expression: %a\n" d_exp e );
          raise NoMatch
        end

and match_vPw (e:exp) : (varinfo * varinfo option) =
  match e with
    | BinOp ((PlusA|PlusPI|IndexPI),
             (Lval (Var v, NoOffset) | StartOf (Var v, NoOffset)),
             (Lval (Var w, NoOffset) | StartOf (Var w, NoOffset)), _) ->
        (v, Some w)

    | ( StartOf (Var v, NoOffset) | Lval (Var v, NoOffset) ) ->
        (v, None)

    | _ -> raise NoMatch

and stripCast (e:exp) : exp =
  match e with
    | CastE (t,e') -> stripCast e'
    | _ -> e

(* like vPc but allow a cast in the front *)
and match_CvPc (e:exp) = match_vPc (stripCast e)

and match_pPc (e:exp) =
  match (match_vPc e) with
    | (Some p, c) when isPAType p -> (p, c)
    | _ -> raise NoMatch

and match_CpPc (e:exp) = match_pPc (stripCast e)

and match_iPc (e:exp) =
  match (match_vPc e) with
    | (Some i, c) when isIntType i -> (Some i, c)
    | (Some _, _) -> raise NoMatch
    | (None, c) -> (None, c)

and match_CiPc (e:exp) = match_iPc (stripCast e)

(* match (cast)( (cast)x + c ) -- casts are optional *)
and match_CCiPc (e:exp) =
  match (stripCast e) with
    | BinOp (op, e1, e2, x) -> match_iPc (BinOp(op, stripCast e1, stripCast e2, x))
    | e' -> match_iPc e'

and match_pPi (e:exp) =
  match match_vPw e with
    | (p,Some i) when (isPAType p && isIntType i) -> (p, Some i)
    | (i,Some p) when (isPAType p && isIntType i) -> (p, Some i)
    | (p,None) when (isPAType p) -> (p,None)
    | _ -> raise NoMatch

and match_CpPiPc (e'':exp) : (varinfo * varinfo option * int) =
  let e' = stripCast e'' in
    try
      let (p,c) = match_pPc e'' in (p, None, c)
    with NoMatch -> begin
      match e' with
        | (Lval (Var p, NoOffset)| StartOf (Var p, NoOffset)) when isPAType p ->
            (p, None, 0)

        | ( BinOp( (PlusPI|IndexPI|PlusA), (Lval(Var p, NoOffset)| StartOf (Var p, NoOffset)) , e, _)
          | BinOp( (PlusPI|IndexPI|PlusA), e, (Lval(Var p, NoOffset)| StartOf (Var p, NoOffset)) , _) )
            when isPAType p ->
            let (io,c) = match_CiPc e in
              (p, io, c)

        | ( BinOp( (PlusPI|IndexPI|PlusA), (Lval(Var i, NoOffset)| StartOf (Var i, NoOffset)) , e, _)
          | BinOp( (PlusPI|IndexPI|PlusA), e, (Lval(Var i, NoOffset)| StartOf (Var i, NoOffset)) , _) )
            when isIntType i ->
            let (p,c) = match_pPc e in
              (p, Some i, c)

        | ( BinOp( (PlusPI|PlusA|IndexPI), Const(CInt64(c,_,_)), e, _ )
          | BinOp( (PlusPI|PlusA|IndexPI), e, Const(CInt64(c,_,_)), _ ) ) ->
            let (p,io) = match_pPi e in (p, io, Int64.to_int c)

        | BinOp ( (MinusPI|MinusA), e, Const(CInt64(c,_,_)), _ ) ->
            let (p,io) = match_pPi e in (p, io, -Int64.to_int c)


        | _ -> raise NoMatch
    end
(* add edges based on the test in e
 * only works on stuff of form x + c op y + d *)
and branchExp (e : exp) =

  let dualOp op = begin
    match op with
      | Lt -> Ge
      | Gt -> Le
      | Le -> Gt
      | Ge -> Lt
      | Eq -> Ne
      | Ne -> Eq
      | _ -> raise NoMatch
  end in

  let rec stripNot (e:exp) (flip:bool) =
    begin
      match e with
	| UnOp(LNot, e', t) -> stripNot e' (not flip)
	| _ -> (e, flip)
    end
  in
  let matchCompare (x,c) (y,d) op =
    match op with
      | Le -> (fun (x,y) -> addIfEdge y x (d-c))   (* x+c <= y+d -> x <= y+d-c *)
      | Lt -> (fun (x,y) -> addIfEdge y x (d-c-1)) (* x+c <  y+d -> x <= y+d-c-1 *)
      | Gt -> (fun (x,y) -> addIfEdge x y (c-d-1)) (* x+c >  y+d -> y <= x+c-d-1 *)
      | Ge -> (fun (x,y) -> addIfEdge x y (c-d))   (* x+c >= y+d -> y <= x+c-d *)
      | Eq -> (fun (x,y) -> (addIfEdge y x (d-c); addIfEdge x y (c-d))) (* x+c = y+d -> x <= y+d-c ^ y <= x+c-d *)
      | Ne -> (fun (x,y) -> ())
      | _ -> invalid_arg "matchCompare on something not a comparison"
  in
  let branches (x,c) (y,d) op =
    ( x, y,
      matchCompare (x,c) (y,d) op,
      matchCompare (x,c) (y,d) (dualOp op) )
  in
  let (e', flip) = stripNot e false in
	match e' with
	  | BinOp( (Lt|Gt|Le|Ge|Eq|Ne) as op, e1, e2, _ ) ->
	      branches
              (match_vPc e1)
              (match_vPc e2)
              (if flip then (dualOp op) else op)
	  | _ -> raise NoMatch
;;


(***********************************************************)
(*                                                         *)
(* check disection                                         *)
(*                                                         *)
(***********************************************************)


(* we can extract the ptr that we're checking from the args *)
let checkedExp (chk : string) (args : exp list) : exp list =
  match (chk, args) with
    | ("CHECK_FSEQ2SAFE", bend::ptr::_) -> [ptr]
    | ("CHECK_FSEQARITH", p::plen::ptr::_) -> [ptr]
    | ("CHECK_FSEQARITH2SAFE", p::bend::ppi::_) -> [ppi]
    | ("CHECK_SEQ2SAFE", base::bend::p::_) -> [p]
    | ("CHECK_SEQ2FSEQ", b::e::p::_) -> [p]

    | ("CHECK_GEU", e1::e2::_) -> [e1;e2] (* e1,e2: unsigned long *)
    | ("CHECK_POSITIVE", x::_) -> [x] (* x:int *)

    | ( ("CHECK_FSEQ2SAFE"
        | "CHECK_FSEQARITH"
        | "CHECK_FSEQARITH2SAFE"
        | "CHECK_GEU"
        | "CHECK_SEQ2SAFE"
        | "CHECK_SEQ2FSEQ"
        | "CHECK_POSITIVE") as chk, _) ->
        failwith (sprint ~width:80 (dprintf
              "number of parameters to %s appears to have changed" chk ))

    | _ -> raise NoMatch



(* is this a check we care about?  for gathering statistics / debug printing *)
let interestingCheck  (i : instr) =
  match i with
    | (Call (None, Lval(Var chk,_), args, loc)) when isInstrCheck i ->
        begin
          match (chk.vname) with
            | ("CHECK_FSEQ2SAFE"
              | "CHECK_FSEQARITH"
              | "CHECK_FSEQARITH2SAFE") -> true
            | _ -> false
        end
    | _ -> false


(* convert check *)
and seq2safe_to_seq2fseq (args : exp list) (loc : location) : instr =
  match args with
    | [base; bend; p; src_element_len; destlen; foraccess; nonnull] ->
        Call (None, Lval(var Curechecks.checkSeq2FSeqFun.svar), [base;bend;p], locUnknown)
    | _ -> failwith "seq2safe_to_seq2fseq: args changed"

and seq2safe_to_fseq2safe (args : exp list) (loc: location) : instr =
  match args with
    | [base; bend; p; src_element_len; destlen; foraccess; nonnull] ->
        Call (None, Lval(var Curechecks.checkFSeq2SafeFun.svar), [bend;p;src_element_len;destlen;foraccess;nonnull], locUnknown)
    | _ -> failwith "seq2safe_to_seq2fseq: args changed"

;;


(***********************************************************)
(*                                                         *)
(* env stuff                                               *)
(*                                                         *)
(***********************************************************)

type binding = varinfo * (node ref)

(* integer variables, last nodes, no-overflow nodes *)
and  varsmap = (binding list) * (binding list)

(* map stmt.sid (unique w/in fn, computed with cfg)
   to pre-env and post-env respectively *)
let stmtPres  : (int, varsmap) H.t = H.create 50
let stmtPosts : (int, varsmap) H.t = H.create 50

let vars = ref []
let ptrvars = ref []

(* find node for int variable v in env
 * anyone using lookup on something not definitely in env
 * should catch NoMatch and do something sensible *)
let rec lookup (env,_ : varsmap) (v : varinfo) =
  if v.vglob || (not (isIntType v)) then
    raise NoMatch
  else
    try
      find env v
    with
        Not_found ->
          failwith (sprint ~width:80 (dprintf
             "Bug in elimabc: varinfo %s::%s : %a not found in env"
                            !currentFnName
                            v.vname
                            d_type v.vtype ))

and ptrlookup(_,penv : varsmap) (v : varinfo) =
  if v.vglob || (not (isPAType v)) then
    raise NoMatch
  else
    try
      find penv v
    with
        Not_found ->
          failwith (sprint ~width:80 (dprintf
             "Bug in elimabc: ptr node %s::%s : %a not found in env"
             !currentFnName
             v.vname
             d_type v.vtype ))


and bind (env,penv : varsmap) (b : binding) = (b::env, penv)
and bindptr (env,penv : varsmap) (b : binding) = (env, b::penv)

  (* maybe useful for debugging if nodes are actually labeled *)
and newenv () = (
  List.map (fun vi -> (vi, newNode vi !instrnum Phi (*IntNode*) )) (!vars),
  List.map (fun vi -> (vi, newNode vi !instrnum PtrPhi (*PtrNode*) )) (!ptrvars)
)

and find (bs : binding list) (v : varinfo) = List.assq v bs
;;


(***********************************************************)
(*                                                         *)
(* tree walk to build the graph                            *)
(*                                                         *)
(***********************************************************)

let rec doFundec (fd : fundec) (stmts : stmt list) : unit =
  begin
    (* create graphs for each stmt *)
    vars := List.filter isIntType (fd.sformals @ fd.slocals);
    ptrvars := List.filter isPAType (fd.sformals @ fd.slocals);
    instrnum := 0;
    (* vi.vattr contains __size() attribute *)
    (*
    List.iter (fun vi -> ignore(E.log "%s : %a {%a}\n" vi.vname d_type
                                  vi.vtype d_attrlist vi.vattr))
      (fd.sformals @ fd.slocals);
    *) (*
    List.iter (fun vi -> ignore(E.log "%s : %a {%a}\n"
                                  vi.vname
                                  d_type vi.vtype
                                  (d_list ", " (fun () -> text)) (List.map (fun (Attr(s,_)) -> s) vi.vattr)
                               ))
      (fd.sformals @ fd.slocals);
       *)
    let env =
      let venv = List.map (fun vi -> (vi, newEntryNode vi 0 Phi)) (!vars) in
      let penv =
        List.map (fun vi ->
                    let binding = (vi, newEntryNode vi 0 PtrPhi) in begin
                      match (List.filter (fun (Attr(name,_)) -> "size"=name) vi.vattr) with
                        | (Attr("size", [ACons (sizevar,[])])::_) -> begin
                            ignore (E.log "%s : %a [%s]\n"
                                      vi.vname d_type vi.vtype sizevar);
                            try
                              let sizenode = snd (List.find (fun (vi,_) -> sizevar=vi.vname) venv)
                              in addCEdge (snd binding) sizenode 1 ~lb:false ~lbov:false ~ub:true ~ubov:true
                            with Not_found -> ()
                          end
                        | _ -> ()
                      end; binding
                 ) (!ptrvars)
      in
        (venv, penv)
    in

    doBlock (Some env) fd.sbody;

    (* connect the graphs *)
    List.iter connectStmts stmts;
  end


and doBlock (envo : varsmap option) (b : block) : varsmap option =
  List.fold_left doStmt envo b.bstmts


(* invariant about the returned varsmap option:
 * anything which jumps (goto,return,break,continue) returns None
 *  and registers its post-env to connect to its successor's pre-envs later
 * any control flow join (stmt with multiple predecessors) gets a
 *  phi node as its pre-env and envo phis into it
 * a stmt whose only sucessor is the thing that follows it in a block
 *  (egs If, Block, Instr -- NOT Loop nor Switch)
 *  just returns Some(post-env) - if it's the last stmt in the block
 *  Loop and If will phi it into the right thing
 * see code for Switch for details on its workings
 *
 * the goal of all this is to add all the control flow edges into the
 *  graph without introducing lots of extra phi nodes
 *)
and doStmt (envo : varsmap option) (s : stmt) : varsmap option =

  incr instrnum;

  (*if !debugx then ignore (E.log "Stmt %d,%d: %a\n\n" (s.sid) (!instrnum) d_stmt s);*)

  let singleton = function
    | [] -> true
    | x::[] -> true
    | x::y::[] when x==y -> true (* a hack for twonky if handling in cfgs *)
    | _ -> false
  in

  let env =
    begin
      match (envo, singleton s.preds) with
        | (Some env', true) -> env' (* only one pred, just use its post *)

        | (Some env', _) -> (* create new nodes for other preds to phi into *)
            let env'' = newenv() in
              begin
                connectVarsmaps env' env'';
                env'';
              end;

        | (None, false) -> newenv()

        (* note: may cause some self-loops to be added *)
        (* I wonder if that will cause problems... *)
        | (None, true) -> (* only one pred, see if we've done it *)
            begin
              try
                let pred = (List.hd s.preds) in
                  H.find stmtPosts pred.sid
              with
                  (Not_found | Failure "hd") -> newenv()
            end
    end in

  (* every stmt has its pre-env recorded *)
  let _ = H.add stmtPres s.sid env in

  let postenv =
    match s.skind with
      | Instr il -> Some (List.fold_left doInstr env il)

      | Block b -> doBlock (Some env) b (* push envo through? *)

      | Return _ -> None

      | (Goto (_, loc) | Break (loc) | Continue (loc)) ->
          begin
            H.add stmtPosts s.sid env;
            None;
          end

      (* presumably these span multiple functions, so should cause the
         whole file to fail *)
      | TryExcept (_, _, _, _) -> failwith "TryExcept not implemented"
      | TryFinally (_, _, _) -> failwith "TryFinally not implemented"

      (* loop is exitted with a break - post env of loop body just needs to
         be connected to the pre-env for the loop body
      *)
      | Loop (b, loc, s1, s2) ->
          let bodypost = doBlock (Some env) b in
            begin
              (match bodypost with
                | None -> ()
                | Some bp -> connectVarsmaps bp env);
              None;
            end

      | If (e, tb, fb, loc) ->
          begin
            incr instrnum;
            let ifnodes (zo : varinfo option) :
              (varsmap * node ref -> varsmap)
              * node ref
              * node ref
              * node ref =
              begin
                match zo with
                  | None -> ( (fun (env',node) -> env'),
                              zeroNode,
                              zeroNode,
                              zeroNode)
                  | Some viz ->
                      ( (fun (env',node) -> bind env' (viz,node)),
                        lookup env viz,
                        newNode viz !instrnum Pi,
                        newNode viz (!instrnum+1) Pi )
              end
            in

            (* derive from env pre-envs for true/false branches *)
            let (tenv, fenv) =
              begin
                incr instrnum; (* true branch, false branch, post *)
                incr instrnum;
                try
                  (* match the if predicate *)
                  let (xo, yo, tedges, fedges) = branchExp e in

                  (* get current node for x and create new nodes for x on
                     the branches (same for y)
                  *)
                  let (bindx, xn, xt, xf) = ifnodes xo in
                  let (bindy, yn, yt, yf) = ifnodes yo in

                  (* add edges from Pi assignments and
                     edges based on if predicate *)
                  let _ =
                    begin
                      addAssignEdge xn xt 0;
                      addAssignEdge yn yt 0;
                      tedges(xt,yt);

                      addAssignEdge xn xf 0;
                      addAssignEdge yn yf 0;
                      fedges(xf,yf);
                    end in

                    ( bindy (bindx (env,xt), yt),
                      bindy (bindx (env,xf), yf) )

                with NoMatch -> (env, env)
              end
            in
              (* get post-envs for branches, phi them together (if needed)
                 to get postenv for the whole if *)
            let tpost = doBlock (Some tenv) tb in
            let fpost = doBlock (Some fenv) fb in
              incr instrnum;
              match (tpost, fpost) with
                | ((None, post) | (post, None)) -> post
                | (Some tp, Some fp) -> Some (joinVarsmaps tp fp)
          end

      | Switch (e, b, sl, loc) ->
	  begin
            (* sl is a list of statements where cases start but _does not_
               include all statements in the case, so we use b
               -register env as post env so all case beginings can connect
               to it in the post pass
               -return the postenv of the last case because there may not be
                an explicit break (so it won't be connected in the post pass)
            *)
            H.add stmtPosts s.sid env;
            doBlock (Some env) b
	  end

  in begin
      postenv;
    end


(* need to use abslocs b/c can only get pts to sets for exps that exist in
   the program *)

(* sfg 6-feb-04
 * ccured maintains the following invariant with regard to local variables:
 * -addresses of locals from main /may/ be stored on the heap or in globals
 * -addresses of other local variables /may not/ be stored on the heap or in globals
 * -addresses of all locals /may/ be stored on the same or higher stack frames
 *
 * so, conservatively:
 * -any function call may update any local from main whose address is taken
 * -a function call that is passed an alias of a local may update that local
 * -assignments through local pointers (same stack frame) may update a local
 * -NB: local also means local pointer (i.e. ptr first/last nodes)
 *)

(* invalidate any aliases of /updated/ *)
(* /invu/ = if true, invalidate entry for /updated/ in env *)
and invalidateLval (env : varsmap) (updated : lval) (notouch) : varsmap =
  try
    invalidateAbslocs  env  (P.absloc_lval_aliases updated)  notouch
  with
      Not_found -> failwith "Pointer analysis raises Not_found from invalidateLval!!"

and invalidateAbslocs (env : varsmap) (abslocs : P.absloc list) (notouch : varinfo option) : varsmap =
  List.fold_left (fun env'' absloc -> invalidateAbsloc env'' absloc notouch) (env) (abslocs)

and invalidateAbsloc ((ienv, penv) : varsmap) (updated_absloc : P.absloc) (notouch : varinfo option) : varsmap =
  try
    let inv  (infty) ((vi,nr) : binding) : binding =
      if ( (P.absloc_eq updated_absloc (P.absloc_of_varinfo vi))
           && (match notouch with Some(vi') when vi'==vi -> false | _ -> true)
	 )
      then (vi, infty)
      else (vi, nr)
    in
      ( List.map (inv posInftyNode) ienv,
	List.map (inv negInftyNode) penv )
  with
      Not_found -> failwith "Pointer analysis raises Not_found from invalidateAbsloc!!"

(* use abslocs (low level interface from ptr analysis)
 *  keep list of abslocs for stuff in graph
 *  have map from absloc to varinfo
 *  find abslocs that alias, look up their varinfos and shoot 'em down
 *
 * updates to loal variables need not shoot anything down
 *)

and doInstr (env:varsmap) (i : instr) =

  incr instrnum;
  (*if !debugx then ignore (E.log "instr %d: %a\n" (!instrnum) d_instr i);*)

  match i with

    (* intvar = intvar + intconst *)
    | Set ((Var x, NoOffset) as _lhs, rhs, loc) when isIntType x ->
        begin
          let env' =
            try
              let (yo,c) = match_vPc rhs in
              let yn = (match yo with
                          | Some y -> lookup env y
                          | None -> zeroNode)
              in
              let xn' = newNode x !instrnum Assign in
                begin
                  addAssignEdge yn xn' c;
                  bind env (x, xn')
                end
            with NoMatch -> bind env (x, posInftyNode)
          in
            env' (*invalidateLval env' lhs (Some x)*)
        end

    (* ptr = ptr' + intconst *)
    | Set ((Var p, NoOffset) as _lhs, rhs, loc) when isPAType p ->
        begin
          let env' =
            try
              let (q,c) = match_CpPc rhs in
              let qn = ptrlookup env q in
              let pn' = newNode p !instrnum PtrAssign in
                begin
                  addAssignEdge pn' qn c;
                  bindptr env (p, pn')
                end
            with NoMatch -> bindptr env (p, negInftyNode)
          in
            env' (*invalidateLval env' lhs (Some p)*)
        end

    (* assign to more complex lvalue - invalidate aliases *)
    | Set (lhs, rhs, loc) ->
        invalidateLval env lhs None

    (* a check *)
    | (Call (None, Lval(Var chk,_), args, loc)) when isCheckCall_str chk.vname ->
        doCheck env i

    (* invalidate anything transitively pointed to by fn args
     * if we're in main, invalidate anything whose address is taken (see above)
     * also invalidate may aliases of lhs (to which fn's return value assigned) *)
    | Call (lhso, fn, args, loc) ->
        let env0 = begin match lhso with
            None -> env
          | Some lhs -> invalidateLval env lhs None
        end in
        let env1 =
          if ("main" = !currentFnName) then begin
            let inv infty ((vi, nr) : binding) : binding =
              if (vi.vaddrof) then (vi, infty) else (vi, nr)
            in
            let (ienv0, penv0) = env0 in
              ( List.map (inv posInftyNode) ienv0,
	        List.map (inv negInftyNode) penv0 )
          end else env0
        in
          List.fold_left
	    (fun env' e -> invalidateAbslocs env' (P.absloc_e_transitive_points_to e) None)
	    env1
	    args

    | Asm _ -> env


and doCheck (env : varsmap) (i : instr) =
  match i with
    | (Call (None, Lval(Var chk,_), args, loc)) when isCheckCall_str chk.vname ->
        begin
	  if !debugx then ignore(E.log "[%d] Check: %a\n" !instrnum d_instr i);
          incr totalChecks;

          (* create a 0-weight succ for x and bind it in env *)
          let newx xo env =
            begin match xo with
              | None -> (zeroNode,zeroNode,env)
              | Some x ->
                  let xn = lookup env x in
                  let xn' = newNode x !instrnum Pi in
                  let env' = bind env (x, xn') in
                    (* (x)---[0]--->(x') *)
                    addAssignEdge xn xn' 0;
                    (xn,xn',env')
            end in

          let newp p env =
            let pn = ptrlookup env p in
            let pn' = newNode p !instrnum PtrPi in
            let env' = bindptr env (p, pn') in
              addAssignEdge pn' pn 0;
              (pn, pn', env')
          in

          (* p.last >= x+c
           * i.e. p.last + (-c) >= x
           *
           * to elim want (p.last)---[-c]---->(x)
           * add (x')<---[-c]---(p'.last)
           *)
          let xPcLEQlastp pln pln' xn xn' c =
            let len = -c in
              begin
                addCEdge pln' xn' len ~lb:false ~lbov:false ~ub:true ~ubov:false;
                (fun () -> path_from_to_lt pln xn len ~lb:false ~lbov:false ~ub:true ~ubov:false)
              end in

          (* p+x+c doesn't overflow
           *
           * to elim want (p.nooverflow)---[-c]--->(x)
           * add         (p'.nooverflow)---[-c]--->(x')
           *)
          let pPxPcNoOverflow pno pno' xn xn' c =
            begin
              let len = -c in
                addCEdge pno' xn' len ~lb:false ~lbov:false ~ub:false ~ubov:true;
                (fun () -> path_from_to_lt pno xn len ~lb:false ~lbov:false ~ub:false ~ubov:true)
            end in

          (* p.first <= x+c  (l.b.)
           *
           * to elim want (p.first)<<--[c]--(x)
           * add         (p'.first)<<--[c]--(x') i.e. (p'.first)--[-c]-->(x')
           *)
          let xPcGEQfirstp pn pn' xn xn' c =
            begin
              let len = -c in
                addCEdge pn' xn' len ~lb:true ~lbov:false ~ub:false ~ubov:false;
                (fun () -> path_from_to_lt pn xn len ~lb:true ~lbov:false ~ub:false ~ubov:false) (***)
            end in

          (* 0 <= x+c i.e. 0-c <= x (for l.b. checks)
           *
           * add 0<<--[c]--(x') i.e. 0--[-c]-->(x')
           * to elim want 0<<--[c]--(x)
           *)
          let xPcGEQzero xn xn' c =
            begin
              let len = -c in
                addCEdge zeroNode xn' len ~lb:true ~lbov:false ~ub:false ~ubov:false;
                (fun () -> path_from_to_lt zeroNode xn len ~lb:true ~lbov:false ~ub:false ~ubov:false)
            end in

          (* c >= x i.e. 0+c >= x for u.b. checks
           *
           * add (0)--[c]-->(x')
           * to elim want (0)-->[c]-->(x)
           *)
          let xLEQc xn xn' c =
            begin
              let len = c in
                addCEdge zeroNode xn' len ~lb:false ~lbov:false ~ub:true ~ubov:false;
                (fun () -> path_from_to_lt zeroNode xn len ~lb:false ~lbov:false ~ub:true ~ubov:false)
            end in

            (* do the pi assignment and add constraints for the check
             * also register a predicate that will (when the graph has been
             * built) tell whether the check can be eliminated
             *)
            (*xxx: the var graphs we build is unsuitable for lower bound checks ***)
            try begin
              incr matchedChecks;
	      match (chk.vname, checkedExp chk.vname args) with
	        | ("CHECK_FSEQ2SAFE", [e]) ->
                    let (p,xo,c) = match_CpPiPc e in
                    let (xn, xn', env') = newx xo env in
                    let (pn, pn', env'') = newp p env' in
                    let pred = xPcLEQlastp pn pn' xn xn' c in
                    let remove = (fun () ->
                                          if pred() then ChangeTo []
                                          else DoChildren)
                    in
                      registerCheckCode i remove;
                      env''

	        | ("CHECK_FSEQARITH", [e]) ->
                    let (p,xo,c) = match_CpPiPc e in
                    let (xn, xn', env') = newx xo env in
                    let (pn, pn', env'') = newp p env' in
                    let pred = pPxPcNoOverflow pn pn' xn xn' c in
                    let remove = (fun () ->
                                          if pred() then ChangeTo []
                                          else DoChildren)
                    in
                      registerCheckCode i remove;
                      env''

	        | ("CHECK_FSEQARITH2SAFE", [e]) ->
                    let (p,xo,c) = match_CpPiPc e in
                    let (xn, xn', env') = newx xo env in
                    let (pn, pn', env'') = newp p env' in
                    let p1 = xPcLEQlastp pn pn' xn xn' c in
                    let p2 = pPxPcNoOverflow pn pn' xn xn' c in
                    let remove = (fun () ->
                                          if p1() && p2() then ChangeTo []
                                          else DoChildren)
                    in
                      registerCheckCode i remove;
                      env''

                | ("CHECK_SEQ2SAFE", [e]) ->
                    let (p,xo,c) = match_CpPiPc e in
                    let (xn, xn', env') = newx xo env in
                    let (pn, pn', env'') = newp p env' in
                    let ub = xPcLEQlastp pn pn' xn xn' c in
                    let lb = xPcGEQfirstp pn pn' xn xn' c in
                    let change =
                      (fun () ->
                               match (lb(), ub()) with
                                 | true,true -> ChangeTo []
                                 | false,true -> ChangeTo [seq2safe_to_seq2fseq args loc]
                                 | true,false -> ChangeTo [seq2safe_to_fseq2safe args loc]
                                 | false,false -> DoChildren
                      )
                    in
                      registerCheckCode i change;
                      env''

                | ("CHECK_SEQ2FSEQ", [e]) ->
                    let (p,xo,c) = match_CpPiPc e in
                    let (xn, xn', env') = newx xo env in
                    let (pn, pn', env'') = newp p env' in
                    let pred = xPcGEQfirstp pn pn' xn xn' c in
                    let remove = (fun () ->
                                          if pred() then ChangeTo []
                                          else DoChildren)
                    in
                      registerCheckCode i remove;
                      env''

                | ("CHECK_POSITIVE", [e]) ->
                    let (xo, c) = match_CCiPc e in
                    let (xn, xn', env') = newx xo env in
                    let pred = xPcGEQzero xn xn' c in
                    let remove = (fun () ->
                                          if pred() then ChangeTo []
                                          else DoChildren)
                    in
                      registerCheckCode i remove;
                      env'

                | ("CHECK_GEU", [e1;e2]) ->
                    begin
                      let (xo, c) = match_CCiPc e1 in
                      let (yo, d) = match_CCiPc e2 in
                      let (remove, env') =
                        begin
                          match (xo, yo) with

                            (* (u)(x+c) >= (u)d *)
                            | (Some x, None) ->
                                let (xn,xn',env') = newx xo env in
                                  (* implement me!! **)
                                  ((fun () -> DoChildren), env') (***)

                            (* (u)c >= (u)(y+d)
                             * c >= 0 and check passes
                             *    <=> 0 <= y+d <= c
                             *    <=> (lb) 0 <= y+d and (ub) y <= c-d
                             *)
                            | (None, Some y) ->
                                if c >= 0 then
                                  let (yn, yn', env') = newx yo env in
                                  let lb = xPcGEQzero yn yn' d in
                                  let ub = xLEQc yn yn' (c-d) in
                                  let remove = (fun () ->
                                                  if  lb() && ub() then ChangeTo []
                                                  else DoChildren)
                                  in
                                    (remove, env')
                                else
                                  ((fun () -> DoChildren), env)

                            | (None, None) ->
                                (* constant >= constant!! *)
                                ( (if c>=0 && d>=0 && c>=d then
                                     (fun () -> ChangeTo [])
                                   else
                                     (fun () -> DoChildren)
                                  ), env )

                            | _ -> raise NoMatch
                        end
                      in
                        registerCheckCode i remove;
                        env'
                    end

                | _ -> (decr matchedChecks; env)

	    end with NoMatch -> (decr matchedChecks; env)
        end

    | _ -> failwith "impossible: called doCheck on something not a check"


(***********************************************************)
(*                                                         *)
(* finish up the var graph (connect jump edges)            *)
(*                                                         *)
(***********************************************************)

(* any jumps (break, continue, goto) needs to add edges to the variable
   graph - we do it here based on the CFG and the post-stmt varsmaps
   registered in stmtPosts (which we connect to their successors' pres from
   stmtPres) *)

(* connect a stmt to its successors *)
and connectStmts (s : stmt) : unit =
  List.iter (connectStmtPair s) s.succs

(* connect varnode src's post to the corresponding varnodes in dest's pre *)
and connectStmtPair (src : stmt) (dest : stmt) : unit =
  try  connectVarsmaps (H.find stmtPosts src.sid) (H.find stmtPres dest.sid)
  with Not_found -> () (* no post => connection taken care of in dostmt *)

(* ptr.last edges go other way at control flow join *)
(* a flows into b   a->b *)
and connectVarsmaps (a1,a2 : varsmap) (b1,b2 : varsmap) =
  begin
    List.iter (connectVarnodes a1 b1) !vars;
    List.iter (connectVarnodes b2 a2) !ptrvars
  end

and connectVarnodes (sns : binding list) (dns : binding list) (x : varinfo) : unit =
  try
    addJEdge (find sns x) (find dns x)
  with
      Not_found -> failwith (sprint ~width:80 (dprintf
                       "Bug! connectVarnodes can't find %s::%s"
                       !currentFnName x.vname ))

(* handle control-flow join of two varsmaps, create new phi nodes as needed *)
and joinVarsmaps (a1,a2 : varsmap) (b1,b2 : varsmap) : varsmap =
  (List.map (joinVar a1 b1) !vars,
   List.map (joinPtrVar a2 b2) !ptrvars
  )

(* a and b join to produce result a->.<-b *)
and joinVar (a : binding list) (b : binding list) (x : varinfo) : binding =
  try
    let aa = find a x in
    let bb = find b x in
      if (aa==bb) then
	(x, aa)
      else
	let xn = newNode x !instrnum Phi in
          begin
            addJEdge aa xn;
            addJEdge bb xn;
            (x, xn);
          end
  with
      Not_found -> failwith (sprint ~width:80 (dprintf
			 "Bug! joinVar can't find %s::%s"
			 !currentFnName x.vname ))


(* ptr.last edges go other way at control flow join *)
and joinPtrVar (a : binding list) (b : binding list) (x : varinfo) : binding =
  try
    let aa = find a x in
    let bb = find b x in
      if (aa==bb) then
	(x, aa)
      else
	let xn = newNode x !instrnum PtrPhi in
          begin
            addJEdge xn aa;
            addJEdge xn bb;
            (x, xn);
          end
  with
      Not_found -> failwith (sprint ~width:80 (dprintf
			 "Bug! joinPtrVar can't find %s::%s"
			 !currentFnName x.vname ))
;;

(****************************************************************)
(*                                                              *)
(*  The outer loop: process each function                       *)
(*                                                              *)
(*  for each function                                           *)
(*    compute cfg                                               *)
(*    create var graph, transitively close and summarize        *)
(*    eliminate redundant checks                                *)
(*    throw away the var graph                                  *)
(*                                                              *)
(****************************************************************)

(* a visitor to eliminate checks based on stored predicates and var graph *)
(*let instrnum = ref 0*)

class elimChecksVisitorClass = object (self)
  inherit nopCilVisitor


  (* compute constraint graph for the function *)
  method vfunc (fd : fundec) : fundec visitAction =
    begin
      (* after done with this fn, get rid of all fn specific state *)
      let after fd =
	( if !dumpvargraph then dumpVarGraph();
          clearVarGraph();
	  H.clear stmtPres;
	  H.clear stmtPosts;
	  H.clear checkCode;
	  fd )
      in
        currentFnName := filter_fn_name fd.svar.vname;
        let cfgfilename = !currentFileName ^ "cfg." ^ !currentFnName ^ ".dot" in

        ignore(Cfg.cfgFun fd); (* fill out the cfg *)
        stmts := fd.sallstmts; (* all stmts in fd *)
        if (!printcfgs) then Cfg.printCfgFilename cfgfilename fd;

        let res = ref SkipChildren in
          begin
	    try
              if (!debug) then ignore(E.log "--Building Graph for '%s'\n" !currentFnName);
	      doFundec fd !stmts; (* compute the variable graph *)

              if (!debug) then ignore(E.log "--Reducing Graph for '%s'\n" !currentFnName);
              reduce_graph ();    (* transitively close and summarize it *)

              if (!debug) then ignore(E.log "--Eliminate Checks for '%s'\n" !currentFnName);
              res := ChangeDoChildrenPost (fd, after);
	    with
	      | Failure reason ->
		  incr goofed_fns;
		  ignore (warn "Array bounds check elimination failed for %s: %s\n"
                            !currentFnName reason)

	      | Not_found ->
		  incr goofed_fns;
		  ignore (warn "unhandled Not_found while processing %s\n"
                            !currentFnName)

              | Invalid_argument reason ->
		  incr goofed_fns;
		  ignore (warn "Bug in elimabc! <Invalid_argument> while processing %s: %s"
                            !currentFnName reason)

              | NoMatch ->
		  incr goofed_fns;
		  ignore(warn "Bug in elimabc!  Missed a NoMatch while processing %s!"
                           !currentFnName)

              | Match_failure (f,s,e) ->
		  incr goofed_fns;
		  ignore(warn "Bug in elimabc!  during processing of %s match failed at %s: %d-%d"
                           !currentFnName f s e)

              | GiveUp reason ->
		  incr goofed_fns;
                  ignore(warn "Gave up on function %s: %s"
                           !currentFnName reason)

	(*| _ -> incr goofed_fns;
          ignore(warn "Bug in elimabc!  Some other exception raised during processing of %s"
          !currentFnName)
        *)
	end;

        !res
    end

  method vstmt (s : stmt) : stmt visitAction = DoChildren

  (* if i is a fully redundant check, eliminate it, o/w try to hoist it *)
  method vinst (i : instr) : instr list visitAction =
    begin
      match i with
        | (Call (None, Lval(Var chk,_), args, loc)) when isInstrCheck i ->

            (* remove fully redundant check *)
            begin
              match maybeRemoveCheck i with
                | (ChangeTo []) ->
                    if !gdebug then ignore(E.log "%s: REMOVED: @!\t@[%a@]\n\n"
                                           !currentFnName
                                           d_instr i);
                    incr redundantChecks;
                    ChangeTo []

                | ((ChangeTo il') as x) ->
                    if !gdebug then ignore(E.log "%s: CHANGED @!\t@[%a@] @!@[\tTO: @?%a@]@!\n"
                                           !currentFnName
                                           d_instr i
                                           (d_list ";\n" d_instr) il');
                    incr changedChecks;
                    x

                | _ ->
                    if !gdebug then ignore(E.log "%s: LEAVING: @!\t@[%a@]\n\n"
                                           !currentFnName
                                           d_instr i);
                    DoChildren

            end (* handling check *)

        | _ -> DoChildren
    end (* vinst *)

end;;

let elimChecksVisitor = new elimChecksVisitorClass;;


(***************************************************************************)
(*                                                                         *)
(* a way to eliminate all matchable checks and show non-matchable checks   *)
(*   (not part of the usual functionality -- for performance upper bounds) *)
(*                                                                         *)
(***************************************************************************)

let unmatchedChecks : (string * string, int * exp) H.t = H.create 50
let incCheck c p =
  try
    let (count,_) = H.find unmatchedChecks c in
      H.replace unmatchedChecks c (count+1, p)
  with
      Not_found -> H.add unmatchedChecks c (1, p)

let printUnmatchedCheck (chk,ptrexp : string*string) (count,p) =
  ignore(E.log "%d - %s( %s e.g. %a)\n" count chk ptrexp d_exp p)

let printUnmatchedChecks () : unit =
  begin
    ignore(E.log "\nUnmatched Checks:\n--------------------------\n");
    H.iter printUnmatchedCheck unmatchedChecks;
    ignore(E.log "--------------------------\n");
  end

  (* give cannonical string rep of exp *)
let rec stringExp (e : exp) : string =
  match e with
    | Const _ -> "c"
    | Lval lv -> stringLval lv
    | SizeOf _ -> "sizeof_t"
    | SizeOfE _ -> "sizeof_e"
    | SizeOfStr _ -> "sizeof_str"
    | AlignOf _ -> "alignof_t"
    | AlignOfE _ -> "alignof_e"
    | UnOp (op,e,_) -> (stringUnop op) ^ "(" ^ (stringExp e) ^ ")"
    | BinOp (op, e1, e2, _) ->
        (stringBinop op) ^ " " ^ (stringExp e1) ^ " " ^ (stringExp e2)
    | CastE(t,e) -> "(" ^ (stringType t) ^ ")" ^ (stringExp e)
    | AddrOf lv -> "&(" ^ (stringLval lv) ^ ")"
    | StartOf lv -> (stringLval lv)

and stringLval (lv : lval) : string =
  match lv with
    | (Var vi, off) -> (stringVarType vi.vtype) ^ (stringOffset off)
    | (Mem e, off) -> "*(" ^ (stringExp e) ^  (stringOffset off) ^ ")"

and stringType (t : typ) : string =
  sprint ~width:80 (dprintf "%a" d_type t)

and stringVarType (t : typ) : string =
  match (unrollTypeDeep t) with
    | TInt _ -> "i"
    | TPtr (t,i) -> "p" ^ (stringVarType t)
    | TFloat _ -> "d"
    | TArray (t, _, _) -> "a" ^ (stringVarType t)
    | TComp (ci,_) when ci.cstruct -> "s"
    | TComp _ -> "u"
    | TVoid _ -> "v"
    | TFun _ -> "F"
    | _ -> "?"

and stringOffset (off : offset) : string =
  match off with
    | NoOffset -> ""
    | Field(_,off') -> ".f" ^ (stringOffset off')
    | Index(e,off') -> "[" ^ (stringExp e) ^ "]" ^ (stringOffset off')

and stringUnop (u : unop) : string =
  match u with
    | Neg -> "-"
    | BNot -> "~"
    | LNot -> "!"

and stringBinop (b : binop) : string =
  match b with
    | PlusA -> "+"
    | (PlusPI|IndexPI) -> "++"
    | MinusA -> "-"
    | MinusPI -> "--"
    | MinusPP -> "---"
    | Mult -> "*"
    | Div -> "/"
    | Mod -> "%"
    | Shiftlt -> "<<"
    | Shiftrt -> ">>"
    | (Lt | Gt | Le | Ge | Eq | Ne) -> "<=>"
    | BAnd -> "&"
    | BXor -> "^"
    | BOr -> "|"
    | LAnd -> "&&"
    | LOr -> "||"


(* for performance testing purposes - eliminate all recognizable checks *)
class elimAllChecksVC = object (self)
  inherit nopCilVisitor

  (* eliminate the checks we can match (mod magicflag)
   * record eligible checks that we couldn't match
   *)
  method vinst (i : instr) : instr list visitAction =
    match i with
      | (Call (None, Lval(Var chk,_), args, loc)) when isInstrCheck i ->
          begin
            try
              let p = checkedExp chk.vname args in
              let s = stringExp (List.hd p) in
                begin
                  try
                    match (chk.vname, p) with
                      | ( ("CHECK_FSEQ2SAFE" | "CHECK_FSEQARITH" | "CHECK_FSEQARITH2SAFE"), [e] ) ->
                          if (!magicflag >= 1) then
                            let _ = match_CpPiPc e in ChangeTo []
                          else
                            DoChildren

                      | ( ("CHECK_SEQ2SAFE"| "CHECK_SEQ2FSEQ"), [e] ) ->
                          if (!magicflag >= 2) then
                            let _ = match_CpPiPc e in ChangeTo []
                          else
                            DoChildren

                      | ("CHECK_POSITIVE", [e]) ->
                          if (!magicflag >= 2) then
                            let _ = match_CCiPc e in ChangeTo []
                          else
                            DoChildren

                      | ("CHECK_GEU", [e1;e2]) ->
                          if (!magicflag >= 2) then
                            let _ = match_CCiPc e1, match_CCiPc e2 in ChangeTo []
                          else
                            DoChildren

                      | _ -> DoChildren

                    with
                        NoMatch ->
                          (* couldn't match the check, record it *)
                          if (chk.vname = "CHECK_GEU") then
                            let s1 = stringExp (List.hd args) in
                            let s2 = stringExp (List.hd (List.tl args)) in
                            let e = BinOp(Ge, List.hd p, List.hd(List.tl p), intType) in
                              (incCheck (chk.vname, s1 ^ " <=u " ^ s2) e; DoChildren)
                          else
                            (incCheck (chk.vname, s) (List.hd p); DoChildren)
                end (*try to match*)

            with (* checkedExp failed, bail out *)
                (NoMatch | Failure "hd") -> DoChildren

          end (* try - is check eligible? *)

      | _ -> DoChildren

end;;
let elimAllChecksV = new elimAllChecksVC;;

let elimAllChecksFile (f : Cil.file) : Cil.file =
  begin
    visitCilFileSameGlobals elimAllChecksV f;
    if !magicflag = 2 then printUnmatchedChecks ();
    H.clear unmatchedChecks;
    f
 end
;;


(**************************************************************)
(*                                                            *)
(* the entry point                                            *)
(*                                                            *)
(**************************************************************)

let elimabcFile (f : Cil.file) : Cil.file =
  if (not !elimabc) then f (* skip this whole stage *)
  else
    begin
      if !debug then ignore (E.log "**********************Start Elim ABC!\n");
      currentFileName := filter_file_name f.fileName;
      P.debug_may_aliases := true; (*!!!*)
      begin
        try
          visitCilFileSameGlobals elimChecksVisitor f;
        with
	  | Failure reason -> ignore (warn "Array bounds check elimination failed: %s\n" reason)
          | Not_found -> ignore (warn "Bug in elimabc!  Missed a Not_found!")
          | Invalid_argument reason -> ignore (warn "Bug in elimabc! <Invalid_argument>: %s" reason)
          | NoMatch -> ignore(warn "Bug in elimabc!  Missed a NoMatch!")
          | Match_failure (f,s,e) -> ignore(warn "Bug in elimabc!  match failed at %s: %d-%d" f s e)
          (*| _ -> ignore(warn "Bug in elimabc!  Some other exception raised" )*)
      end;

      if !printStats then begin
        ignore (E.log "elimabc stats for %s: \n" !currentFileName);
	ignore (E.log "\t goofed functions %d\n" !goofed_fns);
        (*ignore (E.log "\t eligible checks  %d\n" !eligibleChecks);*)
        ignore (E.log "\t matched checks   %d\n" !matchedChecks);
        ignore (E.log "\t redundant checks %d\n" !redundantChecks);
        ignore (E.log "\t changed checks   %d\n" !changedChecks);
      end;

      if !debug then ignore (E.log "**********************End Elim ABC!\n");
      f
    end
;;
