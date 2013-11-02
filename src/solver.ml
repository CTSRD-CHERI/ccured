(*
 *
 * Copyright (c) 2001-2002,
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
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

(* Weimer
 *
 * CCured pointer kind inference using an extension of the algorithm
 * described in the paper submitted to PLDI'02.
 *
 * INPUT ASSUMPTIONS:
 *
 * The node hashtable includes the following edges:
 *      n1 ECAST n2     for the top-level nodes of casts
 *      n1 EOFFSET n2     from the top of a struct to its non-array fields
 *      n1 EINDEX n2    from the top of a struct to array fields
 *
 * Nodes have the following bits set iff the corresponding fact actually
 * originate at that node:
 *      pkPosArith
 *      pkArith
 *      pkNull
 *      pkUpdated
 *      pkIntCast
 *      pkInterface
 *      pkSized
 *      pkNoPrototype (makes a function node wild)
 *
 * The "is_p x y" function returns true if x--cast-->y is from a polymorphic
 * function and should not be considered.
 *
 * Returns "true" if we should typecheck the result because we let some
 * user-annotated qualifier stand.
 *)
(*
 * How does the solver work?
 *
 * We treat every "void *" as a separate type variable and we keep
 * equivalence classes of void* nodes that are connected by ECast or
 * ECompat edges. ECast edges come from Markptr as part of our
 * precondition. We create ECompat edges.
 *
 * (1) We examine every CAST in the program. While scanning the
 *      types to see if the cast is valid we add ECompat edges between
 *      inner types that must be equal and mark as Wild types that
 *      do not match up. We also mark nodes as Not Safe in casts where
 *      the sizes are wrong.
 * (2) Check equivalence classes. All nodes joined by ECompat edges must
 *      have equal types. Make sure all nodes in all equiv classes have
 *      the same flags.
 * (3) We assign base-case flags. For example, we assign
 *      "pkString" to nodes that are of type string.
 * (4) We push those flags around using standard data-flow tricks. Nodes
 *      connected by ECompat edges have identical flags.
 * (5) Once we have all the flags in place we distinguish between all
 *      the kinds of sequences. For example, a node that cannot be safe
 *      and has an integer cast into it but does not reach a string becomes
 *      FSEQ.
 * (6) We turn all string-like nodes that lead only into ROString nodes
 *      into ROString nodes themselves. Note all nodes connected by ECompat
 *      edges must have the same kind.
 * (7) We push WILD as far as it can go. Generally WILD contaminates all
 *      outgoing edges and all points-to targets, however an edge from
 *      WILD to ROString is allowed.
 * (8) All otherwise unconstrainted nodes become SAFE.
 *
 * Compared to previous solvers, this solver is much stricter about
 * strings. No "safe -> string" or "safe -> rostring" casts should remain.
 *)

open Cil
open Ptrnode
open Pretty
open Trace
module E = Errormsg
module MU = Markutil

let markAllSplit = ref false

let interface_char_ptr_is_ROSTRING = false
  (* should all interface 'char *'s be made into ROSTRINGS? *)

let suggest_rtti_placement = false (* Suggest RTTI annotations on bad casts? *)
let rtti_placement_ht = Hashtbl.create 511

(* When enabled, this causes all bad casts (and bad SEQ-SEQ checks) to be
 * ignored and their locations printed out instead. *)
let noteAndIgnoreBadCasts = ref false

(* Set this to true and initialize the watch_which_nodes with a list of nodes
 * to be watched *)
let logUpdates = false
let logNodeUpdate =
  let which_nodes = [ 2; ] in
  let which_nodes =
    let h : (int, bool) Hashtbl.t = Hashtbl.create 13 in
    List.iter (fun nid -> Hashtbl.add h nid true) which_nodes;
    h
  in
  fun  (n: node) (k: opointerkind) (new_w : whykind) (old_w: whykind) ->
    if Hashtbl.mem which_nodes n.id then
      ignore (warnLoc n.loc
                "updating node %d (%a) to %a (%a). Old kind: %a (%a)"
                n.id d_place_nice n.where
                d_opointerkind k (d_whykind n) new_w
                d_opointerkind n.kind
                (d_whykind n) old_w)

(* helper function: does a node represent a pointer to a character? *)
let is_char_pointer n =
  match n.btype with
    TInt(IChar,_) -> true
  | TInt(ISChar,_) -> true
  | TInt(IUChar,_) -> true
  | _ -> false

(* helper function: is this node's kind some form of string? *)
let is_string k = (k = String || k = ROString)

(* was the node's kind set by some outside force? *)
let set_outside n = n.why_kind = UserSpec || n.why_kind = PrintfArg

(* go through the source code and find where tau was declared *)
class findTypeVisitor tau = object
  inherit nopCilVisitor
  val tau_sig = typeSig tau
  method vtype some_type =
    if tau_sig = typeSig some_type then
      ignore (warn "type %a was not given a node by markptr" d_type tau) ;
    DoChildren
end

(* equiv classes of nodes connected by ECompat edges. *)
module OrderedNode =
  struct
    type t = node
    let compare n1 n2 = n1.id - n2.id
    (* Avoid using Pervasives.compare, which is the same as "=", which may
     * loop forever because nodes contain "Cil.typ"s. *)
  end
module NodeSet = Set.Make(OrderedNode)
module NodeUF = Unionfind.Make(NodeSet)

(* George's new TrustedCast edge requires that the kinds be the same but
 * not the types. Since I cannot use the type to determine what will
 * happen, I'll just pick the "least safe" combination.
 *
 * Apparently the only valid results are Safe, Seq, FSeq and Wild. *)
let trusted_cast_join k1 k2 =
  if k1 = k2 then k1
  else if k1 = Safe then k2
  else if k2 = Safe then k1
  else if k1 = Wild || k2 = Wild then Wild
  else if k1 = Seq || k2 = Seq then Seq
  else if k1 = FSeq || k2 = FSeq then FSeq
  else E.s (E.bug "Solver: trusted cast between %a and %a"
    d_opointerkind k1 d_opointerkind k2)

(* Spread the RTTI flag, while checking that it only goes to void-ptr. The
 * node n has the rtti flag set *)
let rec spreadRTTI (n: node) =
  let orig, _, _ = trueSourceOfFlag n pkRtti in
  let spreadTo (ekind: edgekind) (isbackward: bool) (dest: node) (e: edge) =
    (* Do not spread if this is not backward or if this is not ECompat or the
     * destination base type is not void* *)
    let canspread =
      match ekind, isbackward (* || (isVoidType dest.btype) *) with
      | ECompat _, _ -> true
      | (ECast _ | ESameKind _), true -> true
      | _, _ -> false
    in
    (* Leave alone if dest is already RTTI,
       or if the user specified a kind for dest. *)
    if canspread && not (hasFlag dest pkRtti) && (dest.why_kind <> UserSpec)
    then begin
      (* Always spread to another extensible type. Never spread to a
       * non-extensible type. *)
      if fst (MU.typeCanHaveRtti dest.btype) then begin
        (* Make the chain *)
        let why_n_dest =
          let why1=
            match ekind with
              ECompat why -> why
            | _ -> mkRSingle e
          in
          if isbackward then mkRSym why1 else why1
        in
        setFlag dest pkRtti (FlagSpreadFromNode(n, why_n_dest, orig));
        (* Nodes that are RTTI do not participate in equivalence classes *)
        dest.rep <- None;

        (* And recurse depth first *)
        spreadRTTI dest
      end
    end
  in
  (* Spread only backwards or through ECompat edges *)
  List.iter (fun e -> spreadTo e.ekind false e.eto e) n.succ;
  List.iter (fun e -> spreadTo e.ekind true e.efrom e) n.pred

(*
 **
 *** The Solver!
 **
 *)
let solve (the_file : Cil.file) (node_ht : (int, node) Hashtbl.t) : bool = begin
  let node_eq = ref (NodeUF.empty) in (* ECompat equivalence classes *)

  let existsECompatEdge ~(start : node) ~(dest : node) =
    List.fold_left (fun acc e -> acc ||
     (e.eto.id = dest.id && match e.ekind with ECompat _ -> true | _ ->
     false)) false start.succ
  in

  (* Spread a flag from one node to another one *)
  let spreadFlag (f: int) (from: node) (why_from_to: chain) (nto: node) =
    if not (hasFlag nto f) then begin
      let orig, _, _ = trueSourceOfFlag from f in
      setFlag nto f (FlagSpreadFromNode(from, why_from_to, orig))
    end
  in

  (* Say that n1 and n2 (which are usually matching inner pointers) must
   * really be equal. This adds an ECompat edge between them and places
   * them in the same equivalence class. We avoid making duplicate edges.
   * We know if this edge is for inner pointers. Otherwise it is for void*
   * equivalence classes *)
  let rec addECompatEdge (isinner: bool) n1 n2 why_n1_n2 location =
    if existsECompatEdge n1 n2 ||
       existsECompatEdge n2 n1 ||
       n1.id = n2.id then
      ()
    else begin
      (* Sometimes it might be convenient to swap the nodes in order to keep
       * the explanations shorter. *)
      let n1, n2, why_n1_n2 =
        match isSym why_n1_n2 with
          Some why_n2_n1 -> n2, n1, why_n2_n1
        | _ -> n1, n2, why_n1_n2
      in
(*
      assert(Clist.fold_left (fun acc e -> acc && e.ekind = ECast)
        true ecast_edges) ;
*)
      if doCheckChains then
        checkChainEnds n1 n2 why_n1_n2;
      let _new_edge = addEdge n1 n2 (ECompat why_n1_n2) (Some(location))
      in

      (* If at least one of the two nodes has the RTTI flag set then we set
       * it on the other one as well. Note that we only allow RTTI flags on
       * extensible nodes.  *)
      let n1_is_rtti = hasFlag n1 pkRtti in
      let n2_is_rtti = hasFlag n2 pkRtti in
      if n1_is_rtti <> n2_is_rtti then begin
        let src, dest = if n1_is_rtti then n1, n2 else n2, n1 in
        (* Do not allow RTTI with non-RTTI compatible pointers at inner level
         *)
        if isinner then begin
          let canHaveRtti, why = MU.typeCanHaveRtti dest.btype in
          if not canHaveRtti then
            ignore (warnLoc dest.loc
                      "Solver: cannot have RTTI for type %a (%s). Yet edge %d->%d at %a requires it. Other type is %a"
                      d_type dest.btype why
                      src.id dest.id
                      d_loc location
                      d_type src.btype)
        end;
        (* We have already added the edge, so go ahead and spread *)
        spreadRTTI src
      end;

      (* We only join in the equivalence classes (maintained through the .rep
       * fields) if at least one is TPtr(void). OTherwise we use the NodeUF
       * equivalence classes  *)
      if (isVoidType n1.btype || isVoidType n2.btype) then begin
        join n1 n2 why_n1_n2
      end else
        node_eq := NodeUF.make_equal (!node_eq) n1 n2 why_n1_n2 ;
    end
  in

  (* whenever we have to "loop until things settle", we used
   * finished to keep track of our status *)
  let finished = ref false in

  (* should we force a typecheck later? *)
  let we_should_typecheck = ref false in

  (* update changes node "n"'s kind to "k" because of "w" and sets
   * finished to false. It also does logging and sanity checking. *)
  let update_warnings = ref 5 in
  let update n k w = begin
    if (k <> n.kind) then begin
      (* Check if the new kind is stronger than the old one *)
      let shouldUpdate: bool =
        match k, n.kind with
          _, Unknown -> true (* Unknown is weakest *)
        | _, Safe -> true (* Safe is weak *)
        | Safe, _ -> false (* this means Safe can only replace Unknown *)
        | _, Rtti -> true (* Then is RTTI *)
        | Rtti, _ -> false
        (* Prefer String if the user says so *)
        | (FSeqN|SeqN), (ROString|String) -> false
        | (FSeq|Seq|SeqN|FSeqN|Index), (FSeq|ROString|String) -> true
            (* the above clause is a bit permissive (allowing FSeqN ->
             * FSeq), but we'll leave it for now *)
        | SeqN, FSeqN -> true
        | (SeqN|Index), Seq -> true
        | Wild, _ -> true (* Wild is strongest *)
        | _, _ -> false
      in
      if shouldUpdate then begin
        (* The new kind is stronger. We must update. *)
        if logUpdates then logNodeUpdate n k w n.why_kind;
        (* Shouldn't this be an error ??? *)
        let trulyUpdate =
          if n.why_kind = UserSpec then
            if !allowOverride then begin
	      (* matth:  If the user annotates a node as __RTTI
	       * and we infer it to be FSeqR or SeqR, assume that that's what
	       * the user intended, and don't print a warning. *)
	      (match n.kind, k with
		Rtti, FSeqR
	      |	Rtti, SeqR -> ()
	      | _ -> ignore (warnLoc n.loc
                        "Solver: changing User Specified %a node %d (%a) to %a"
                        d_opointerkind n.kind n.id
                        d_place_nice n.where
                        d_opointerkind k));
              true
            end else begin
              (* Use "ignore" so that we do not stop here. But we'll stop
               * after solving *)
              E.hadErrors := true;
              ignore (errorLoc n.loc
                        "Solver: should change User Specified %a node %d (%a) to %a"
                        d_opointerkind n.kind n.id
                        d_place_nice n.where
                        d_opointerkind k);
              false
            end
          else
            true (* If it is not User_Spec then always update *)
        in
        if trulyUpdate then begin
          n.kind <- k ;
          n.why_kind <- w ;
          finished := false
        end
      end else begin
        (* The new kind is weaker. Leave it how the user said *)
        if !update_warnings > 0 then
          if n.why_kind = UserSpec then
            ignore (warnLoc n.loc "Solver: not changing User Specified %a node %d (%a) to %a"
                      d_opointerkind n.kind n.id
                      d_place_nice n.where
                      d_opointerkind k);
        decr update_warnings ;
        if !update_warnings = 0 then
          ignore (warnLoc n.loc "Solver: skipping further 'not changing User Specified' warnings")
      end
    end else (* Already have the same kind *)
      ()
  end
  in

  (* Help Function: find the attributes of a type *)
  let node_of_type tau =
    nodeOfAttrlist (typeAttrs tau)
  in

  (* Step 0
   * ~~~~~~
   * Our first pass over the set of nodes.
   * Set all of the flag starting conditions that we know about.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 0  (Base Case)\n") ;

  (* loop over all the nodes ... *)
  Hashtbl.iter (fun id n ->
    (* Mark interface character pointers as strings. *)
    if interface_char_ptr_is_ROSTRING then begin
      if hasFlag n pkInterface && is_char_pointer n then begin
        (* the user had something to say here *)
        if (set_outside n) then begin
          match n.kind with
            String | ROString -> ()
          | _ -> ignore (warnLoc n.loc
                  "Solver: %a annotation on interface (char *) node %d (%a)"
                  d_opointerkind n.kind n.id d_place_nice n.where)
        end else
          update n String (BoolFlag(pkInterface))
      end
    end ;

    (* calling a function without a prototype makes it wild *)
    if hasFlag n pkNoPrototype then begin
        update n Wild (BoolFlag pkNoPrototype)
    end ;

    (* Set initial flags based on the pointer kind *)
    if !useRTTI && isRTTI n.kind then begin
      let canHaveRtti, why = MU.typeCanHaveRtti n.btype in
      if not canHaveRtti then begin
        ignore (warnLoc n.loc
                  "Solver: RTTI annotation on a type (%a) that cannot have RTTI (%s).\nDid you forget to put the __NOUNROLL attribute on a typedef?"
                  d_type n.btype why);
      end;
      setFlag n pkRtti (RequiredByPointerKind n.kind);
      (* And spread it through the existing edges *)
      spreadRTTI n
    end;
    begin
    match n.kind with
    | String
    | ROString when !useStrings ->
        setFlag n pkString (RequiredByPointerKind n.kind);
        setFlag n pkOneWord (FlUserSpec n.loc)

    | FSeq | FSeqR
    | Seq  | SeqR    -> ()

    | FSeqN
    | SeqN     when !useStrings ->
        setFlag n pkString (RequiredByPointerKind n.kind)

    | Index    -> setFlag n pkReachIndex (RequiredByPointerKind n.kind)

    | Rtti     -> ()

    | Safe -> setFlag n pkOneWord (FlUserSpec n.loc)

    | _        -> ()
    end ;

    if hasAttribute "size" n.attr || hasAttribute "count" n.attr then
      setFlag n pkOneWord (FlUserSpec n.loc);

  ) node_ht ;

  (* Step 1
   * ~~~~~~
   * Consider every cast.
   *
   * Generate ECOMPAT edges between aligned sub-pointers.
   * Generate BADCAST constaints on failed pointers (make 'em WILD)
   * Generate ARITH constaints on upcasts (make 'em not SAFE).
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 1  (Casts)\n") ;

  (* try to find a node for this type *)
  let _pointer_with_no_node tau1 =
    match node_of_type tau1 with
      Some(n) -> ()
    | None -> begin

    end
  in

  let the_edge = ref None in

  (* Whenever we compare two types for equality we should mark all
   * matching inner pointers with ECOMPAT edges. This function is called
   * by the type-scanning phase on all pairs of pointers that should
   * match up. *)
  let handle_inner_pointers loc explanation tau1 tau2 =
    try begin
      match (node_of_type tau1),(node_of_type tau2) with
      | Some(n1),Some(n2) ->
          addECompatEdge true n1 n2 explanation loc;

      | Some(n),None
      | None,Some(n) when (isVoidType n.btype) -> begin
          (* Link a "void*" equivalence class with the scalars. *)
          setFlag n pkCompatWithScalars (FlagSpreadFromNode(n,explanation,n)) ;
          let (nr,why_n_nr) = get_rep_why n in
          setFlag nr pkCompatWithScalars (FlagSpreadFromNode(n,why_n_nr,n))
          end

      | _,_ -> (* in this unfortunate case, we don't know how to get
                * to the nodes of these types. Try to print a useful error
                * message  *)
        begin
        if node_of_type tau1 = None then
          ignore (visitCilFile (new findTypeVisitor tau1) the_file) ;
        if node_of_type tau2 = None then
          ignore (visitCilFile (new findTypeVisitor tau2) the_file) ;

        E.s (E.bug "Solver: cannot link inner pointers:@!%a@!%a@!%a\n"
          d_type tau1 d_type tau2
          (docOpt (fun e ->
            dprintf "%d->%d" e.efrom.id e.eto.id)) !the_edge)  ;
            E.hadErrors := true
        end
    end with e -> begin
      ignore (E.warn "handle_inner_pointers raises %s\n"
                (Printexc.to_string e))
    end
  in
  (* This function is called by type comparison functions in Type.ml when the
   * base types of two pointer types fails to compare properly. This function
   * should be called on representatives only. *)
  let handle_failure n1 why_n1_n2 n2 =
    if not !noteAndIgnoreBadCasts then begin
      if n1.rep != None then
        E.s (E.bug "handle_failure called on node %d which is not a representative"
               n1.id);
      if n2.rep != None then
        E.s (E.bug "handle_failure called on node %d which is not a representative"
               n2.id);
      let why_kind =
        match isOneEdge why_n1_n2 with
          Some e -> begin
            match e.ekind with
              ECast _ | ESameKind _ -> BadCast e
            | ECompat _ ->
                Incompat (n1, why_n1_n2, n2)
            | _ -> E.s (bug "handle_failure: unexpected edge kind")
          end
        | _ -> (* Otherwise, we have more than one cast involved. Use
            * Incompat *)
            Incompat (n1, why_n1_n2, n2)
      in
      update n1 Wild why_kind;
      update n2 Wild why_kind
    end
  in
  (*
   * Step 1 Loop : examine every cast
   *)
  (* Sometimes we might need to create new ECast edges for auto RTTI.
   * Remember them here *)
  let newAutoRttiEdges: edge list ref = ref [] in
  let step1_oneEdge e = (* look at every forward edge *)
    the_edge := Some(e) ;
    if isECast e &&
      (* If the cast edge is really a copytags pseudo-cast between two void*s,
         the src and dest nodes will have different values.  Unifying the
         equivalence classes would be too conservative for pkStack, etc.  So
         leave them as separate classes, and add inner pointers in step 2.*)
      e.ekind <> (ECast EEK_copytags)
    then begin
      if Type.debugType then
         ignore (E.log "Considering Edge %d->%d\n" e.efrom.id e.eto.id);

      let from_rep, why_efrom_frep = get_rep_why e.efrom in
      let to_rep, why_eto_trep = get_rep_why e.eto in
      let from_rep_t = from_rep.btype in
      let to_rep_t = to_rep.btype in
      (* explanation: from_rep -> e.efrom -> e.eto -> to_rep *)
      let why_frep_trep =
        mkRTrans (mkRSym why_efrom_frep)
          (mkRTrans (mkRSingle e) why_eto_trep) in

      (* If this edge involves a node that is RTTI then this cast is a RTTI
       * cast and we do not need to check the types involved. Note that the
       * RTTI flag can be set only for extended nodes.  *)
      if !useRTTI && (hasFlag e.efrom pkRtti || hasFlag e.eto pkRtti) then
        try
          ignore (MU.checkRttiCast
                    ~newedges:(Some newAutoRttiEdges)
                    (TPtr(e.efrom.btype, e.efrom.attr))
                    (hasFlag e.efrom pkRtti)
                    (TPtr(e.eto.btype, e.eto.attr))
                    (hasFlag e.eto pkRtti) e.eloc);
        with e -> begin
          ignore (E.warn "step1_edge RTTI raises %s\n"
                    (Printexc.to_string e));
          E.hadErrors := true;
          (* Continue *)
        end

      (* If one of the representatives types is void_ptr then we just add an
       * ECompat edge and join the classes *)
      else if (isVoidType from_rep_t || isVoidType to_rep_t) then
        addECompatEdge false from_rep to_rep why_frep_trep e.eloc

      (* Not a cast involving RTTI void*. Just go ahead and check the types *)
      else begin
        let from_size = try bitsSizeOf(from_rep_t) with SizeOfError _ -> 1 in
        let to_size = try bitsSizeOf(to_rep_t) with SizeOfError _ -> 1 in
        if from_size < to_size then begin
          setFlag e.efrom pkNotSafe (DownCast e.eto); (* ARITH constraint *)
        end ;

        Stats.time "subtype" (fun () ->
          if not (Type.subtype
              ~compat:(handle_inner_pointers e.eloc)
              ~failure:(handle_failure)
              ~why_small_big:(mkRSym why_frep_trep)
              ~small:to_rep_t
              ~big:from_rep_t)
            then begin (* they are not subtypes *)
              (* We do *NOT* pass polymorphic_replace to Type.all_scalars
               * because we have already replaced the top-level void*s
               * (with to_rep and from_rep). p_r would just replace any
               * void*s in to_rep_type and from_rep_type -- but if there
               * are any void*s in to_rep_type or from_rep_type then we
               * don't want to say that it was "all scalars" here. In
               * particular, this could happen in a case like:
               *   int i = 5 __1 ;
               *   void *__2 *__3 v = ( void *__4 *__5 )&i;
               * Between 3 and 5. 4 will have the pkCompatWithScalars flag,
               * but we don't to make 2 and 4 FSEQ here. *)
              if (Type.all_scalars to_rep_t) && (Type.all_scalars from_rep_t)
                 (* if it must be compatible with scalars and we failed the
                  * subtyping then it must be WILD! *)
              then begin
                (* ARITH constraint *)
                (* GN: Subtyping failed but they are all scalars. In that
                 * case all we need is the the origin node is not SAFE. I
                 * commented out the next line. *)
                (* setFlag e.eto pkNotSafe (SubtypeFailed e.efrom) ; *)
                setFlag e.efrom pkNotSafe (SubtypeFailed e.eto) ;
                (* In this one special case, we'll infer that the two
                 * types should be SEQ *)
              end else begin
                if suggest_rtti_placement then begin
                  if (Type.subtype
                      ~compat:(handle_inner_pointers e.eloc)
                      ~failure:(handle_failure)
                      ~why_small_big:(mkRSym why_frep_trep)
                      ~small:from_rep_t
                      ~big:to_rep_t) then
                    Hashtbl.add rtti_placement_ht to_rep_t from_rep_t
                end ;
                if !noteAndIgnoreBadCasts then begin
                  ignore (warnLoc e.eloc "Solver: BAD CAST@!   %a@!<- %a"
                    d_type to_rep_t d_type from_rep_t) ;
                end else begin
                  handle_failure from_rep why_frep_trep to_rep
                end
              end
            end
            ) ()
      end
    end else if e.ekind = EIndex then begin
      (* while we're here, these arrays cannot be safe *)
      setFlag e.eto pkNotSafe (RequiredByEdge e);
    end
  in
  Hashtbl.iter (fun id cur ->
    List.iter step1_oneEdge cur.succ ; (* look at every forward edge *)
    the_edge := None ;
    if !markAllSplit ||
       hasAttribute "split" cur.attr ||
       isC cur.kind then begin
      setFlag cur pkSplit (RequiredByPointerKind cur.kind) ;
      cur.kind <- stripC cur.kind
    end ;
    if cur.kind = Seq || cur.kind = SeqN then
      setFlag cur pkArith (RequiredByPointerKind cur.kind) ;
    if cur.kind = FSeq || cur.kind = FSeqN then
      setFlag cur pkPosArith (RequiredByPointerKind cur.kind) ;
  ) node_ht ;
  (* now do the newly created edges *)
  List.iter step1_oneEdge !newAutoRttiEdges;

  (* Step 2
   * ~~~~~~
   * Some wrapper helpers require that arguments and return values have the
   * same type, but we can't use ECast or ECompat for this because those would
   * spread kinds as well.  Check these "ESameType" constraints here.
   *
   * Also, the (ECast EEK_copytags) edge was skipped earlier.  Now that we
   * know what the equivalence classes are, add compat edges for inner
   * pointers and such.
   *
   * We do this after ECast edges have been handled so that every void* has a
   * proper representative (or, if the representative is still void*, the type
   * is truly unconstrained).
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 2  (helpers)\n") ;
  let doUnifyBaseTypes e =
    (* for ESameType and (ECast EEK_copytags) edges *)
    if e.ekind = ESameType || e.ekind = ECast EEK_copytags then begin
      let from_rep, why_efrom_frep = get_rep_why e.efrom in
      let to_rep, why_eto_trep = get_rep_why e.eto in
      let from_rep_t = from_rep.btype in
      let to_rep_t = to_rep.btype in
      let why_frep_trep =
        mkRTrans (mkRSym why_efrom_frep)
          (mkRTrans (mkRSingle e) why_eto_trep) in
	if (isVoidType from_rep_t) || (isVoidType to_rep_t) then begin
	  ()  (* A true void*, do nothing *)
	end else begin
          if (not (Stats.time "subtype"
                     (fun () -> Type.subtype
			(* handle_inner_pointers adds ECompat edges where
			 * neccessary. *)
                        ~compat:(handle_inner_pointers e.eloc)
                        ~failure:(handle_failure)
                        ~why_small_big: why_frep_trep
                        ~small:to_rep_t
                        ~big:from_rep_t) ())) then
	    begin
	      (* Note the bad cast *)
	      handle_failure to_rep why_frep_trep from_rep;
	    end
	end
    end
  in
    Hashtbl.iter
      (fun id cur -> List.iter doUnifyBaseTypes cur.succ)
      node_ht;

  (* Step 3
   * ~~~~~~
   * Check our equivalence classes for consistency.
   *
   * All "void *" equivalence class nodes should have an ECompat edge to
   * their rep. The rep has the flags for the whole class.
   *
   * All nodes in "void*" equivalence classes should link up everything
   * they point to in "void*" equivalence classes as well.
   *
   * All nodes in equiv classes should have the same flags.
   *)
  (* First we add transitive closure of the ECast edges on "void *" *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 3  (equiv)\n") ;

  let check_compat_fun e =
    match e.ekind with
      ECompat r ->
        let to_t = e.eto.btype in
        let from_t = e.efrom.btype in
        (* Leave alone the edges that have a void-ptr !! *)
        if isVoidType to_t || isVoidType from_t then
          ()
        else begin
          the_edge := Some(e) ;
          if (not (Stats.time "subtype"
                     (fun () -> Type.equal
                             ~compat:(fun _ _ _ -> ()) (* gn: why ? *)
                             ~failure:(handle_failure)
                             ~why_t1_t2: r
                             ~t1:from_t
                             ~t2:to_t) ())) then
            handle_failure e.eto r e.efrom;

          the_edge := None ;
        end;
    | _ -> ()

  in

  Stats.time "equiv-check"
  (Hashtbl.iter (fun id cur ->
    let rep, why_cur_rep = get_rep_why cur in

    (* Check to see if any equivalence classes must be compatible with
     * scalars AND ALSO with some non-void type. If so, that class becomes
     * WILD. *)
    if (     hasFlag cur pkCompatWithScalars &&
        not (hasFlag rep pkCompatWithScalars)) then begin
        E.s (E.bug "Solver: node %d has pkCompatWithScalars flag but its rep %d does not" cur.id rep.id)
    end ;

    if hasFlag rep pkCompatWithScalars && not (isVoidType rep.btype) then begin
      if !noteAndIgnoreBadCasts then
        ignore (warnLoc rep.loc "Solver: BAD CAST / EQ-SCALAR@!%a"
          d_type rep.btype)
      else
        update rep Wild (BoolFlag(pkCompatWithScalars))
    end ;

    if doCheckChains then
      checkChainEnds cur rep why_cur_rep;
    if rep != cur then begin
      for i = 0 to pkLastFlag do
        (* The RTTI flag is spread while the edges are being created *)
        if i <> pkRtti && hasFlag cur i then
          spreadFlag i cur why_cur_rep rep
      done ;
    end;
    (* Once for each edge *)
    List.iter check_compat_fun cur.succ ;
    (* List.iter check_compat_fun cur.pred ; *)
  )) node_ht ;

  (* Now we have equivalence classes of ECompat-joined nodes *)
  let compat_eq_classes = NodeUF.eq_classes !node_eq in

  (*
   * Step 3 Loop #2 : examine each "void *" equiv class
   *)

  (* share all flags within equivalence classes *)
  Stats.time "equiv-flags"
  List.iter (fun eq_class ->
    List.iter (fun from_elt ->
      List.iter (fun to_elt ->
        for i = 0 to pkLastFlag do
          (* The RTTI flag is spread while the edges are being created *)
          if i <> pkRtti && hasFlag from_elt i then
            if not (hasFlag to_elt i) then
              let why_from_to = NodeUF.why_equal !node_eq from_elt to_elt in
              if doCheckChains then
                checkChainEnds from_elt to_elt why_from_to;
              spreadFlag i from_elt why_from_to to_elt
        done ;
        if (to_elt.why_kind = UserSpec) then begin
           from_elt.kind <- to_elt.kind ;
           from_elt.why_kind <- to_elt.why_kind
        end ;
        if (from_elt.why_kind = UserSpec) then begin
           to_elt.kind <- from_elt.kind ;
           to_elt.why_kind <- from_elt.why_kind
        end ;
        if (to_elt.why_kind = Default && from_elt.why_kind <> Default) then
          to_elt.why_kind <- from_elt.why_kind
      ) eq_class
    ) eq_class
  ) compat_eq_classes ;

  (* Step 4
   * ~~~~~~
   * Push all of the boolean flags around.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 4  (Data-Flow)\n") ;
  (* loop over all the nodes ... *)
  finished := false ;

  let worklist = Queue.create () in

  (* Find edge chain *)
  let findEdgeChain (src: node) (e: edge) =
    (* Find the chain src -> dst *)
    let r1 =
      match e.ekind with
        ECompat r' -> r'
      | _ -> mkRSingle e
    in
    (* Check that this edge has src as one of its ends *)
    if doCheckChains && src.id <> e.efrom.id && src.id <> e.eto.id then
      ignore (E.warn "findEdgeChain for src=%d and edge %d->%d\n"
                src.id e.efrom.id e.eto.id);
    (* See if the edge is going in the right direction *)
    if e.efrom.id = src.id then r1 else mkRSym r1
  in

  let setFlagsFromListChain dst src r_src_dst lst =
    if doCheckChains then
      checkChainEnds src dst r_src_dst;
    List.iter (fun i ->
      (* The RTTI flag is spread while the edges are being created *)
      if i <> pkRtti && hasFlag src i && not (hasFlag dst i)
         (* Do not spread the intCast flag to RTTI pointer *)
         && (i <> pkIntCast || not (hasFlag dst pkRtti)) then begin
        Queue.add dst worklist ;
        spreadFlag i src r_src_dst dst
      end
    ) lst
  in

  let setFlagsFromList dst src e lst =
    let r_src_dst = findEdgeChain src e in
    setFlagsFromListChain dst src r_src_dst lst
  in

  let mkSpreadFromEdge (this: node) (e: edge) =
    let near = if e.efrom.id = this.id then e.eto else e.efrom in
    let r_near_this = findEdgeChain near e in
    let orig, _, _ = trueSourceOfKind near in
    if doCheckChains then
      checkChainEnds near this r_near_this;
    SpreadFromNode(near, r_near_this, orig)
  in

  let processDataFlow cur = begin
    let _id = cur.id in
    (* First consider all ECompat edges:
     * flags should be equal across them. This is motivated by
     * test/small1/apachebuf.c. Merely making ECompat-linked nodes have
     * the same kind does not suffice: a pred of an ecompat-linked node
     * may need to be made FSEQ because of a posarith on the other side
     * of the ecompat link. *)
    let inner_fun e =
      if isECompat e || isESameKind e then begin
        setFlagsFromList e.efrom e.eto e allFlags ;
        setFlagsFromList e.eto e.efrom e allFlags ;
      end
    in
    List.iter inner_fun cur.pred ;
    List.iter inner_fun cur.succ ;

    (* Consider all Successor Edges, do data-flow *)
    List.iter (fun e ->
      (match e.ekind with
         ECast EEK_copytags ->
           (* matth: A copytags pseudo-cast [e.g. memcpy(dest, src, n)]
              means that we want to push information backwards, so that
              the source of the cast has the right kind, but not forwards.
              Since the source and destination of the cast have different
              values, we don't push information such as "src may point to
              the stack" to dest. *)
           ()
      | ECast _ ->
          setFlagsFromList e.eto cur e pkCastSuccFlags ;
          (* If the successor node is referenced and we have the pkString
           * flag, we propagate pkPosArith and pkArith flag to successor. We
           * want to make sure that the accesses to these pointers will be
           * checked against the bound, not using the NULLTERM functions *)
          if hasFlag cur pkString && not (hasFlag e.eto pkOneWord) then
            setFlagsFromList e.eto cur e [ pkPosArith; pkArith ]

      | EPointsTo ->
          setFlagsFromList e.eto cur e pkPointsToSuccFlags ;
      | EOffset ->
          setFlagsFromList e.eto cur e pkOffsetSuccFlags ;
      | _ -> ()) ;
    ) cur.succ ;

    (* Consider all Predecessor Edges, do data-flow *)
    List.iter (fun e ->
      (match e.ekind with
         ECast _ ->  (* track [F]SEQ information *)
                   setFlagsFromList e.efrom cur e pkCastPredFlags ;
                   setFlagsFromList e.efrom cur e pkCNIPredFlags ;
       | EIndex -> setFlagsFromList e.efrom cur e pkCNIPredFlags ;
       | EPointsTo when e.efrom.is_array ->
                   (* Conservatively propagate to arrays to make up for
                    * the fact that arrays and their pointers are
                    * indistinguishable in this graph. *)
                   setFlagsFromList e.efrom cur e [pkSplit] ;
       | _ -> ()) ;
    ) cur.pred ;

  end
  in

  Stats.time "data-flow" (fun () ->
    (* data-flow can actually take some time, so we'll use a work-list *)
    Hashtbl.iter (fun id cur -> processDataFlow cur) node_ht;
    while (Queue.length worklist > 0) do
      (* first, run normal data-flow *)
      while (Queue.length worklist > 0) do
        let cur = Queue.take worklist in
        processDataFlow cur
      done ;
      (* If one array has been compared against another, they must share
       * the same flags. Notably, if you have:
       *   struct { int __INDEX a[8]; } *p;
       *   struct { int         b[8]; } *q = p;
       * we want b to end up being INDEX as well. *)
      Hashtbl.iter (fun (t1,t2) why ->
        let n1 = node_of_type t1 in
        let n2 = node_of_type t2 in
        match n1,n2 with
        | Some(n1),Some(n2) ->
          setFlagsFromListChain n1 n2 why [pkReachIndex] ;
          setFlagsFromListChain n2 n1 (mkRSym why) [pkReachIndex]
        | _ ->
          ignore (E.warn "solver: cannot set flags equal for arrays %a and %a"
          d_type t1 d_type t2)
      ) Type.arraysThatHaveBeenComparedWithArrays ;
      (* If this array step didn't update anything, we'll fall out of the
       * outer loop and be done with data-flow. Otherwise we do it all
       * again.  *)
    done
  ) () ;

  (* Step 5
   * ~~~~~~
   * Distinguish between sequences. We must do this after boolean flags
   * (otherwise we cannot tell what reaches what, etc.) but before we do
   * WILDs (because they interact with read-only strings).
   *
   * Also generate ARITH constraints: q != SAFE.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 5  (sequences)\n") ;

  (* n is a polymorphic "void *" node if it points to void* and its
   * representative points to void* as well. *)
  let is_polymorphic_voidstar n =
    match n.btype, (get_rep n).btype with
      TVoid _ , TVoid _->  true
    | _ -> false
  in

  Hashtbl.iter (fun id cur ->
    (* Generate "ARITH" style constraints: q != SAFE *)
    List.iter (fun f ->
      if hasFlag cur f then setFlag cur pkNotSafe (RequiredByFlag f)
    ) [pkArith ; pkPosArith ] ;

    if hasFlag cur pkIntCast && not !noteAndIgnoreBadCasts then
      setFlag cur pkNotSafe (RequiredByFlag pkIntCast) ;

    if interface_char_ptr_is_ROSTRING && hasFlag cur pkInterface &&
       is_char_pointer cur && cur.kind = Unknown then begin
        update cur String (BoolFlag pkInterface)
    end ;

    let isRtti =
      !useRTTI && hasFlag cur pkRtti
        && fst (MU.typeCanHaveRtti cur.btype)
    in
    if hasFlag cur pkString && not !useStrings then
      E.s (bug "we are not using strings but node %d has the pkString flag"
             cur.id);

    if cur.kind <> Wild &&
        (hasFlag cur pkNotSafe ||
         hasFlag cur pkString ||
         hasFlag cur pkReachIndex ||
         (* hasFlag cur pkIntCast ||   These are covered by pkNotSafe
            hasFlag cur pkPosArith ||
            hasFlag cur pkArith ||  *)
         isRtti) then
    begin
      let new_kind,why =
        if isRtti then begin
          if hasFlag cur pkArith then
            SeqR, BoolFlag pkRtti
          else if hasFlag cur pkPosArith then
            FSeqR, BoolFlag pkRtti
          else
            Rtti, BoolFlag pkRtti
        end else if (hasFlag cur pkReachIndex)   then
          Index, BoolFlag pkReachIndex
        else if hasFlag cur pkArith then
          (if hasFlag cur pkString then SeqN else Seq),BoolFlag pkArith

        else if hasFlag cur pkPosArith then
          (if  hasFlag cur pkString then
            (if !useFSEQ then FSeqN else SeqN)
          else
            (if !useFSEQ then FSeq else Seq)), BoolFlag pkPosArith

        (* NOT: pkReachIndex, pkReachSeq, pkPosArith, pkArith *)
        else if hasFlag cur pkIntCast && not
                !noteAndIgnoreBadCasts then
          if is_polymorphic_voidstar cur then begin
            Safe, PolyInt
          end else
            (if hasFlag cur pkString then FSeqN else FSeq),
            BoolFlag pkIntCast

        else if hasFlag cur pkString then
          if cur.kind = ROString then
            ROString, BoolFlag pkString
          else
            String, BoolFlag pkString

        (* NOT: pkString *)
        else if hasFlag cur pkNotSafe then
          (if !useFSEQ then FSeq else Seq), BoolFlag pkNotSafe

        else begin
          E.s (bug "Unexpected combination of flags for node %d: %a\n"
                 cur.id
                 (docArray ~sep:nil
                    (fun idx elm ->
                      match elm with
                        None -> nil
                      | Some _ -> text ("\n\t" ^ pkFlagName.(idx)))) cur.flags)
        end
      in
      update cur new_kind why
    end
  ) node_ht ;

(* At the end of solving, strip Rtti from the fields of tagged unions.
   RTTI info is stored separately, as the union's tag, so fields don't need
   the kind RTTI. *)
  Taggedunion.removeRttiFromFields ();

  (* Step 6
   * ~~~~~~
   * Determine which Strings/FSeqNs should be ROStrings.
   *
   * Note that nodes connected by ECompat edges must all agree.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 6  (ROString)\n") ;

  let any_wilds_in_graph = ref false in
  (* if not, we can skip step 9 *)

  (* helper function to determine if a node is ready to become ROString *)
  let ready_for_rostring cur = (* modulo edges *)
    (cur.kind = FSeqN || cur.kind = Safe || cur.kind = String) &&
    not (hasFlag cur pkUpdated) &&
    not (hasFlag cur pkIntCast) &&
    not (hasFlag cur pkArith) &&
    List.length cur.succ > 0 &&
    List.fold_left (fun acc e ->
      acc && (match e.ekind with
                ECompat _ -> true
              | ESameKind _ -> true
              | ECast _ when  e.eto.kind = ROString -> true
              | _ -> false)) true cur.succ
  in
  finished := false ;
  Stats.time "rostring" (fun () ->
  while not !finished do
    finished := true ;
    (*
     * Consider every node in the graph in two phases.
     *  (1) Consider all nodes w/o ECompat edges
     *  (2) Consider all Eq-Classes of ECompat nodes
     *)
    Hashtbl.iter (fun id cur ->
      if cur.kind = Wild then any_wilds_in_graph := true ;
      let any_ecompat =
        List.fold_left (fun acc e -> acc || isECompat e)
          false (cur.succ @ cur.pred) in
      if not any_ecompat &&
        ready_for_rostring cur
      then begin
        let e = List.hd cur.succ in
        update cur ROString (mkSpreadFromEdge cur e);
      end
    ) node_ht ;

    (* now look at an equivalence class of ECompat nodes *)
    List.iter (fun ecompat_node_list ->
      (* if every node in this list is ready, move every node in this
       * list to ROString *)
      let all_are_ready =
        List.fold_left (fun acc cur -> acc &&
           ready_for_rostring cur &&
           (cur.why_kind <> UserSpec || cur.kind = ROString))
           true ecompat_node_list
      in
      if all_are_ready then
        List.iter (fun cur ->
          let e = List.hd cur.succ in
          update cur ROString (mkSpreadFromEdge cur e);
          ) ecompat_node_list
    ) compat_eq_classes
  done ) () ;

  (* Step 7
   * ~~~~~~
   * Verify that SEQ-SEQ casts have the correct tiling. For example:
   *  struct A { int f1; } * __SEQ p1;
   *  struct B { int f2; int *f3; } * __SEQ p2;
   *  p1 = p2 ;
   * This must result in WILD pointers, otherwise (p1++)->f1=5, *p2->f3 = 6
   * causes a crash.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 7  (SEQ-SEQ Tiling)\n") ;
  let isSeqish n = match n.kind with
    Seq | SeqN | FSeq | FSeqN -> true
  | _ -> false
  in
  Stats.time "seq-seq checking" (fun () ->
  Hashtbl.iter (fun id cur ->
    List.iter (fun e ->
      if isECast e && isSeqish cur && isSeqish e.eto then begin
        let from_target = (get_rep cur).btype in
        let to_target = (get_rep e.eto).btype in
        if isVoidType from_target || isVoidType to_target then
          ()
        else begin
          (* check for tiling! *)
          let okay =
            match Typecheck.bitsSizeOfOpt from_target,
                  Typecheck.bitsSizeOfOpt to_target with
              Some(from_size)  ,Some(to_size) ->
                let the_gcd = Typecheck.gcd from_size to_size in
                let from_factor = to_size / the_gcd in
                let to_factor = from_size / the_gcd in
                Type.equal
                  ~compat:(fun _ _ _ -> ())
                  ~failure:(fun _ _ _ -> ())
                  ~why_t1_t2: mkRIdent
                  ~t1:(TArray(from_target, Some(integer from_factor), []))
                  ~t2:(TArray(to_target, Some(integer to_factor), []))
            | _ ->
                Type.equal
                  ~compat:(fun _ _ _ -> ())
                  ~failure: (fun _ _ _ -> ())
                  ~why_t1_t2: mkRIdent
                  ~t1:from_target
                  ~t2:to_target
          in
          if not okay then begin
            if !noteAndIgnoreBadCasts then begin
              ignore (warnLoc e.eloc "Solver: BAD CAST / SEQ-SEQ@!   %a@!<- %a"
                d_type to_target d_type from_target)
            end else begin
              update cur Wild (BadSequenceCast e) ;
              any_wilds_in_graph := true ;
            end
          end
        end
      end
    ) cur.succ
  ) node_ht) () ;

  (*
   * Step 8
   * ~~~~~~
   * Examine all arrays that were compared with non-arrays. If any such
   * array is INDEX, die.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 8  (Index)\n") ;
  Hashtbl.iter (fun tau why ->
    let n = node_of_type tau in
    match n with
      Some(n) ->
        List.iter (fun e ->
          if e.ekind = EPointsTo then begin
            if e.efrom.kind = Ptrnode.Index then begin
              E.s (E.bug "Solver: array node %a was compared with a non-array but ended up with kind INDEX" d_node n )
            end
          end ) n.pred

    | None -> ignore (E.warn "solver: array %a was compared with a non-array but does not have a node\n" d_type tau )
  ) Type.arraysThatHaveBeenComparedWithNonArrays ;

  (* Step 9
   * ~~~~~~
   * Spread WILD as far as it will go.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 9  (Wild)\n") ;
  let worklist = Queue.create () in

  let pushWILD cur =
    if cur.kind = Wild then begin
      (* consider all of the successor edges, including EPointsTo. If the
       * edge is PointsTo we propagate Wild unconditionally. Otherwise,
       * only if the node is not requested already to be ROString.
       * However, do not propagate WILD accross ESameType*)
      List.iter (fun e ->
        if e.eto.kind <> Wild && e.ekind <> ESameType &&
          (e.ekind = EPointsTo || e.eto.kind <> ROString) then begin
          Queue.add e.eto worklist ;
          update e.eto Wild (mkSpreadFromEdge e.eto e)
        end
      ) cur.succ ;

      (* consider all of the predecessor edges, except EPointsTo (we do
       * not propagate Wild backwards through EPointsTo or ESameType edges). *)
      List.iter (fun e ->
        if e.efrom.kind <> Wild && e.ekind <> EArgs && e.ekind <> ESameType &&
           (e.efrom.kind <> ROString && e.ekind <> EPointsTo) then begin
          Queue.add e.efrom worklist ;
          update e.efrom Wild (mkSpreadFromEdge e.efrom e)
        end
      ) cur.pred ;
    end
  in

  if (!any_wilds_in_graph) then begin
    Hashtbl.iter (fun id cur -> pushWILD cur) node_ht ;
    while (Queue.length worklist > 0) do
      let cur = Queue.take worklist in
      pushWILD cur
    done
  end ;

  (* Step 10
   * ~~~~~~~
   * All other nodes are safe.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 10  (Safe)\n") ;
  let _ecompat_warnings = false in
  Hashtbl.iter (fun id n ->
    if n.kind = Unknown then begin
      update n Safe Unconstrained
    end ;

    (* Sanity Check! Typecheck.ml does much more than this. *)
    if n.kind = Safe &&
      (hasFlag n pkNotSafe ||
       hasFlag n pkString ||
       hasFlag n pkReachIndex ||
       hasFlag n pkIntCast) &&
      not (n.why_kind = UserSpec) &&
      not (is_polymorphic_voidstar n) &&
      not !noteAndIgnoreBadCasts then begin
      E.s (E.bug "Solver: botched node (left/made it safe) %d (%a)"
        n.id d_place_nice n.where) ; E.hadErrors := true
    end ;

    if (!noteAndIgnoreBadCasts && (match n.btype with
      TFun _ -> true | _ -> false) &&
      n.kind <> Safe) then begin
      ignore (E.log "Solver: BAD CAST (%a Function Pointer) %a\n"
                d_opointerkind n.kind d_type n.btype) ;
      n.kind <- Safe;
    end ;

  ) node_ht ;

  if suggest_rtti_placement then begin
    iterGlobals the_file (fun g -> match g with
      GType(tau,loc) ->
        if Hashtbl.mem rtti_placement_ht tau.ttype then
          let other_tau = Hashtbl.find rtti_placement_ht tau.ttype in
          ignore (warnLoc loc "Solver: Suggest RTTI annotation for %s with@!%a"
            tau.tname d_type other_tau)
    | _ -> ()
    ) ;
    Hashtbl.clear rtti_placement_ht
  end ;

  (* Step 11
   * ~~~~~~~
   * Determine which types require a metadata pointer, which
   * can occur for two reasons:
   *
   * 1. A type requires a metadata pointer if it points to or is composed
   * of a split type.
   *
   * 2. A type also requires a metadata pointer if it is in the middle of
   * a sequence of casts between two types that require a metadata
   * pointer.  For example, int * SEQ * requires a metadata pointer.  Thus
   * if we have int * SEQ * -> void * -> int * SEQ *, the void* needs a
   * metadata pointer.
   *
   * This latter requirement makes it difficult to determine whether a
   * type needs a metadata pointer, even when using void* representatives.
   * In particular, trusted casts make life difficult.
   *
   * Thus, we take a bottom-up approach instead.  We determine types that
   * have metadata (i.e., pointers (not arrays!) that aren't safe) and set
   * pkNeedsMetaPtr on all pointers thereto.  This flag then flows
   * backwards along pointers (reason #1), backwards along casts (reason
   * #2, conservatively), and across compat edges.
   *
   * We then do the same thing with pkNeedsMetaPtrBkwd, but flowing
   * across casts in the other direction.  Any node that has both meta
   * pointer flags needs a metadata pointer, since metadata exists
   * before a sequence of casts and is expected on the other end.
   *
   * Once all pointers are marked, we mark composite types as compatible
   * by examining composites that are pointed to by the pointers we've
   * flagged.
   *)
  if !E.verboseFlag then ignore (E.log "Solver: Step 11 (MetaPtr)\n") ;

  (* This function determines whether a type has metadata; if so, pointers
   * to it need a metadata pointer.  A type has metadata if it's a
   * non-safe pointer (not array) node.  As an optimization, we also check
   * to see if the metadata pointer flag is already set, which means that
   * the type (array or pointer) needs metadata. *)
  let needsMetadata (n: node) : bool =
    (hasFlag n pkNeedsMetaPtr &&
     hasFlag n pkNeedsMetaPtrBkwd) ||
    (not n.is_array &&
     match n.kind with
       Seq | FSeq | SeqN | FSeqN | SeqR | FSeqR | Rtti -> true
     | Safe | Scalar | String | ROString -> false
     | _ -> E.s (E.bug "Solver: Does %a need metadata?" d_opointerkind n.kind))
  in

  (* First, we push the pkNeedsMetaPtr flag around the pointer graph for
   * reasons discussed above. *)
  let rec setMetaFlag (n: node) (flag: int) (why: whyflag) : unit =
    if not (hasFlag n flag) then begin
      (* First set the flag. *)
      setFlag n flag why;
      (* Now propagate it. *)
      let getReason (e: edge) (dst: node) : whyflag =
        let orig, _, _ = trueSourceOfFlag n flag in
        FlagSpreadFromNode (orig, findEdgeChain n e, dst)
      in
      List.iter (fun e ->
        let setPredFlag () = setMetaFlag e.efrom flag (getReason e e.efrom) in
        match e.ekind with
          EPointsTo | EOffset ->
            if hasFlag n pkSplit then
              setPredFlag ()
        | ECompat _ ->
            setPredFlag ()
        | ECast _ | ESameKind _ ->
            if flag = pkNeedsMetaPtrBkwd then setPredFlag ()
        | _ -> ()
      ) n.pred ;
      List.iter (fun e ->
        let setSuccFlag () = setMetaFlag e.eto flag (getReason e e.eto) in
        match e.ekind with
          ECompat _ ->
            setSuccFlag ()
        | ECast _ | ESameKind _ ->
            if flag = pkNeedsMetaPtr then setSuccFlag ()
        | _ -> ()
      ) n.succ ;
    end
  in
  Hashtbl.iter (fun id cur ->
    if hasFlag cur pkSplit && needsMetadata cur then
      List.iter (fun e ->
        match e.ekind with
          EPointsTo ->
            setMetaFlag e.efrom pkNeedsMetaPtr (RequiredByEdge e) ;
            setMetaFlag e.efrom pkNeedsMetaPtrBkwd (RequiredByEdge e) ;
        | _ -> ()
      ) cur.pred ;
  ) node_ht ;

  (* Two tasks remain:
   * 1. Add a C to the kind of all pointers that need metadata pointers.
   * 2. Mark all structures that have metadata as compatible.  We find all
   * pointers that need a metadata pointer and look at structures
   * contained in their base type.  For each such structure, we look
   * deeper to find a type that needs metadata; if found, we mark it as
   * compatible. *)
  Hashtbl.iter (fun id cur ->
    if hasFlag cur pkNeedsMetaPtr &&
       hasFlag cur pkNeedsMetaPtrBkwd then begin
      cur.kind <- addC cur.kind ;
      (* TODO: This could be more efficient if we combined findMetaType
       * and markSplitComps into one function. *)
      let findMetaType (t: typ) =
        (* Determine whether a type that needs metadata is a descendant
         * of this type. *)
        match t with
          TPtr (_, attr) (*| TArray (_, _, attr)*) ->
            begin
            match nodeOfAttrlist attr with
              Some n when needsMetadata n -> ExistsTrue
            | _ -> ExistsFalse
            end
        | _ -> ExistsMaybe
      in
      (* This function marks all composite types that require metadata. *)
      let markSplitComps (t: typ) =
        match t with
          TComp (comp, _) ->
            (* If we haven't already marked it and there's some type
             * with metadata below it, mark it. *)
            if not (hasAttribute "split" comp.cattr) &&
               existsType findMetaType t then begin
              comp.cattr <- addAttribute (Attr ("split", [])) comp.cattr ;
              ExistsMaybe (* New territory; keep digging. *)
            end else
              ExistsFalse (* We've already processed this comp. *)
        | TPtr _ | TArray _ ->
            (* We stop searching at pointers and arrays, because we'll
             * do this search when we hit the associated nodes. *)
            ExistsFalse
        | _ -> ExistsMaybe
      in
      if hasFlag cur pkSplit then
        ignore (existsType markSplitComps cur.btype)
    end ;
  ) node_ht ;

  !we_should_typecheck
end

(*
 * TODO (The Wishlist of Wes):
 * (1) change markptr so that ENULL is never used, use ECAST instead
 *     1/1/03 Done (gn)
 * (2) shrink the graph instead of using ECompat edges
 *)
