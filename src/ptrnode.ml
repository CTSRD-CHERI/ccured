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

(* Implements nodes in a graph representing the pointer locations in a
 * program *)
open Cil
open Pretty
open Trace

module H = Hashtbl
module E = Errormsg

(* If defaultIsNotWild then pointers without a qualifier are SAFE and only
 * the arrays that are specfically SIZED contain a size field and only the
 * variables that are specifically TAGGED contain tags *)
let defaultIsWild  = ref false

let useRTTI = ref true
let useFSEQ = ref true
let useStrings = ref true
let extendStringBuffers = ref false

let allowOverride = ref true

let allowInlineAssembly = ref false

let useOffsetNodes = true

let printVerboseOutput = ref false

(* Whether to check the chains *)
let doCheckChains = false

(* This function will be set by the Type module *)
let isSubtype: (typ -> typ -> bool) ref = ref (fun _ _ -> false)
let origSubtype = !isSubtype

let inferFile = ref None

(* flag to force functions to never be tagged *)
let wild_solve_untagged_functions = ref false

(* force functions to always be tagged *)
let wild_solve_tag_all_functions = ref false

(* True if the wild solver is used. *)
let use_wild_solver = ref false

(* The name of the file to save the browser information to *)
let browserFile = ref None

(* The size of the browser source-file fragment (in statements) *)
let browserSourceFileSize = ref 2000

(* The size of the browser node info file fragment (in nodes) *)
let browserNodeFileSize = ref 2000

(** How much detail to print *)
let emitGraphDetailLevel = ref 0

let graphDetailLevelLegend =
"the level of detail in the .infer files:\n" ^
"\t 0 - just the nodes, kind and the chains\n" ^
"\t 1 - also the types, location, name and flags\n" ^
"\t 2 - also the edges (without) justification\n" ^
"\t 3 - everything"

let keepDetails () =
  !browserFile <> None ||
  !emitGraphDetailLevel > 0

(* A marker that the solver places, if we use lean fats *)
let useLeanFats = ref false

let allowPartialElementsInSequence = ref false

let hasPrefix p s =
  let pl = String.length p in
  (String.length s >= pl) && String.sub s 0 pl = p

let hasSuffix suff s =
  let ls = String.length s in
  let lsuff = String.length suff in
  ls >= lsuff && suff = String.sub s (ls - lsuff) lsuff

(* A place where a pointer type can occur *)
type place =
    PGlob of string  (* A global variable or a global function *)
  | PType of string  (* A global typedef *)
  | PStatic of string * string (* A static variable or function. First is
                                * the filename in which it occurs *)
  | PLocal of string * string * string  (* A local variable. The name of the
                                         * file, the function and the name of
                                         * the local itself *)
  | POffset of int * string             (* An offset node, give the host node
                                         * id and a field name *)
  | PField of fieldinfo                 (* A field of a composite type *)

  | PAnon of int                        (* Anonymous. This one must use a
                                         * fresh int every time. Use
                                         * anonPlace() to create one of these
                                         * *)

let anonId = ref (-1)
let anonPlace () : place =
  incr anonId;
  PAnon !anonId

(* Each node corresponds to a place in the program where a qualifier for a
 * pointer type could occur. As a special case we also add qualifiers for
 * variables in expectation that their address might be taken *)
type node =
    {         id: int;                  (* A program-wide unique identifier *)
              where: place * int;       (* A way to identify where is this
                                         * coming from. We use this to make
                                         * sure we do not create duplicate
                                         * nodes. The integer is an index
                                         * within a place, such as if the
                                         * type of a global contains several
                                         * pointer types (nested) *)

              btype: typ;               (* The base type of this pointer *)
      mutable attr: attributes;         (* The attributes of this pointer
                                         * type *)
      mutable is_array: bool;           (* This node is associated with an
                                         * array, not with a pointer. *)

      mutable flags: (whyflag option) array;

      mutable succ: edge list;          (* All edges with "from" = this node *)
      mutable pred: edge list;          (* All edges with "to" = this node *)


      (* The rest are the computed results of constraint resolution *)
      mutable kind: opointerkind;
      mutable why_kind: whykind;

      mutable locked: bool;             (* do not change this kind later *)
      mutable mark: bool;               (* For mark-and-sweep GC of nodes.
                                         * Most of the time is false *)
      mutable rep : (node * chain ) option;
        (* the next node in the chain to the representative of this class.
         * use get_rep to get the final representative *)
      mutable loc : Cil.location;       (* where did this node come from? *)
    }

and opointerkind =
    Safe
  | Scalar (* not actually a pointer *)
  | Seq    (* A three word pointer, like Index but with the length in the
            * pointer itself *)
  | FSeq

  | SeqN   (* A sequence in a null-terminated char array *)
  | FSeqN  (* A FSeq in a null-terminated char array *)

  | SeqR   (* A sequence with RTTI *)
  | FSeqR  (* A FSeq with RTTI *)

  | String (* fseq <= string <= fseq *)
  | ROString (* string->rostring *)

  | Index
  | Wild

  | WildT
  | SeqT
  | FSeqT
  | SeqNT
  | FSeqNT
  | IndexT

  | SafeC
  | WildC
  | SeqC
  | FSeqC
  | SeqNC
  | FSeqNC
  | SeqRC
  | FSeqRC
  | RttiC

  | Rtti

  | Unknown

and whyflag = (* why is this flag set for this node? *)
  | ProgramSyntax of Cil.location

  (* This flag is set because it is set on some other node (node1 + the
   * chain:node1->this). We also give the original source of the flag.  *)
  | FlagSpreadFromNode of node * chain * node

  | DownCast of node
  | SubtypeFailed of node
  | RequiredByEdge of edge
  | RequiredByPointerKind of opointerkind
  | RequiredByFlag of int
  | FlUserSpec of Cil.location  (* Annotated by a user *)

and whykind = (* why did we give it this kind? *)
    BadCast of edge (* always attach to ECast edges *)
  | BadSequenceCast of edge
  | Incompat of node * chain * node (* Two nodes that should be in the same
                                     * equivalence class are incompatible *)

  | BoolFlag of int
  | PolyInt (* This is a void* connected only to scalars *)
  | Default
  | UserSpec
  | Unconstrained
  | PrintfArg (* printf inference *)
  | Special of string * location

  (* This kind is set because it is set on some other node (node1 + the
   * chain:node1->this). We also give the original source of the kind.  *)
  | SpreadFromNode of node * chain * node


and edge =
    {         eid:      int;
      mutable efrom:    node;
      mutable eto:      node;
      mutable ekind:    edgekind;
      mutable eloc:     location;
    }


and edgekind =
    ECast of extra_edge_kind (* T_from ref q_from <= T_to ref q_to. We also
                              * cary some additional explanation for this
                              * edge. *)
  | EOffset                  (* From a pointer to struct to a pointer to
                              * field *)
  | EIndex                   (* q_to = if q_from = wild then wild else index *)
(*  | ENull  *)                  (* a NULL flows in the direction of the edge *)
  | ECompat                  (* the kinds of these two nodes must be
                              * compatible: either both wild, index or
                              * safe. This edge type is added by the solver
                              * for its convenience. In cases like
                              * int * 1 * 2 x;
                              * int * 3 * 4 y;
                              * We will connect 1 and 3 with ECompat. *)
    of chain                 (* An ECompat edge can always be explained
                              * using a list of ECast edges *)
  | ESameKind                (* Special edge that does not require
                              * compatibility of the types involved, but does
                              * require that they be of the same KIND. *)
    of extra_edge_kind_sk    (* See below for uses of ESameKind *)
  | EPointsTo                (* from's base type included to *)
  | EArgs                    (* From the pointer to the function to the
                              * actual arguments and result values. Before we
                              * added this edge we relied on WILDness to
                              * spread from the function pointer to the
                              * actual argument by means of EPoints to edge
                              * to the formals and then ECast edges. But that
                              * did not work when there were no formals
                              * declared ! *)
  | ESameType                (* An edge between two void* nodes that indicates
                              * that the nodes should have the same type, but
                              * not necessarily the same kind.  This edge is a
                              * lighter form of ECast.  It is only used for
                              * helper functions such as ptrof. *)

(* More info about ECast edges *)
and extra_edge_kind =
    EEK_cast                 (* A true cast *)
  | EEK_cxxOverride          (* Due to the Cxx inheritance. See markcxx *)
  | EEK_extends              (* Due to an extends relationship *)
  | EEK_mkptr                (* Due to a mkptr or alignseq *)
  | EEK_copytags             (* Due to a copytags *)
  | EEK_union                (* Edges added between union fields *)
  | EEK_rtti                 (* Edges due to auto RTTI *)

(* More info about ESameKind edges *)
and extra_edge_kind_sk =
  | EEK_trustedCast          (* This edge is added between the formal
                              * argument and the result value in an instance
                              * of trusted_cast function. This does not
                              * require compatibility of the types involved
                              * but does require that the two types be of the
                              * same KIND *)
  | EEK_taggedUnion          (* Behaves like an trustedCast, but is sound.
                              * We use this to connect union fields that must
                              * have the same kind in case we cast from one to
                              * another, but we can ignore types on these edges
                              * since those are checked dynamically. *)

(************** CHAINS ********************)

(** An implementation of chains using constructors for sym and trans *)
and chain =
        (* The chain why a node has a certain representative or why a
         * ECompat edge exists *)
    RIdent          (* Identity: a relationship between identical nodes *)

  | RSingle of edge
        (* This is an ECast edge. This chain is used for
         * ECompat edges that arise "below" a ECast edge. *)

  | RSym of chain  (* If "chain" explains ECompat(n1-n2) then,
        * "RSym(chain)" explains ECompat(n2-n1). *)

         (* Transitivity *)
  | RTrans of node * chain * chain * node * int
          (* Remember the first and the last nodes, and the length *)


  | RList of node * (bool * edge) list * node * int
        (* A list of elements along with the information whether they are
         * reversed. Remember the first and the last node and the length. *)

(** Keep a table with the shortest path *)
type pathEntry =
    { mutable peLen: int; (* Nr of RSingle *)
      mutable peChain: chain
    }

let inftyLen = 1000000 (* A very large length *)
let idPathEntry = { peLen = 0; peChain = RIdent }

let shortestPath: (int * int,  pathEntry) H.t = H.create 11111

let getShortestChain (nfrom: node) (nto: node) : pathEntry * bool =
  if nfrom.id = nto.id then
    idPathEntry, false
  else
    let from', to', sym =
      if nfrom.id < nto.id then
        nfrom.id, nto.id, false
      else
        nto.id, nfrom.id, true
    in
    let pe =
      Ccutil.findOrAdd shortestPath (from', to')
        (fun _ -> { peLen = inftyLen; peChain = RIdent }) in
    pe, sym

let d_edge (e: edge) =  dprintf "%d->%d" e.efrom.id e.eto.id

let rec d_chain () (r: chain) =
  match r with
    RIdent -> nil
  | RSingle e -> d_edge e (* dprintf "%d->%d" e.efrom.id e.eto.id *)
  | RSym r -> text "sym(" ++ d_chain () r ++ text ")"
  | RTrans (_, r1, r2, _, _) ->
      if !emitGraphDetailLevel > 2 then
        d_chain () r1 ++ text "," ++ d_chain () r2
      else text "..."
  | RList (_, l, _, _) ->
      dprintf "list(%a)"
        (docList
           (fun (isrev, a) ->
             if isrev then text "sym(" ++ d_edge a ++ text ")"
             else d_edge a))
           l

let rec dumpChain = function
    RIdent -> ignore (E.log "RID\n")
  | RSingle e -> ignore (E.log "Edge %a\n" insert (d_edge e))
  | RSym r ->
      ignore (E.log "(RSym \n");
      dumpChain r;
      ignore (E.log ")\n")

  | RTrans (_, r1, r2, _, _) ->
      ignore (E.log "(RTrans \n");
      dumpChain r1;
      ignore (E.log ") and (\n");
      dumpChain r2;
      ignore (E.log ")\n")
  | RList (_, l, _, _) ->
      ignore (E.log "list(\n");
      List.iter
        (fun (isrev, a) ->
          if isrev then
            ignore (E.log "sym(%a)" insert (d_edge a))
          else
            ignore (E.log "Edge %a," insert (d_edge a)))
        l

let debugChains = false

let mkRIdent = RIdent
let mkRSingle e = RSingle e

    (* A few helper functions for manipulating chains *)
let mkRSym (r: chain) =
  match r with
    RIdent -> RIdent
  | RSym r1 -> r1
  | _ -> RSym r

let isSym (r: chain) =
  match r with
    RSym r1 -> Some r1
  | _ -> None

(* Get one edge from the chain *)
let rec getOneEdge (r: chain) : edge option =
  match r with
    RSingle e' -> Some e'
  | RSym r -> getOneEdge r
  | RTrans (_, r1, r2, _, _) -> getOneEdge r1
  | RList (_, ((_, h) :: _), _, _) -> Some h
  | RIdent -> None
  | RList _ -> None

let rec isOneEdge (r: chain) : edge option =
  match r with
    RSingle e' -> Some e'
  | RSym r -> isOneEdge r
  | RList (_, [(_, e)], _, _) -> Some e
  | _ -> None

        (* Return a list of elements in a chain. The boolean value says
         * whether the edge is reversed *)
let rec chainToList (c: chain) : (bool * edge) list =
  (* We have the tail already. We have to cons on the beginning of it the
   * argument, possibly symmetric *)

  (* Remember all the tails, indexed by the node number *)
  let tails: (int, (bool * edge) list) H.t = H.create 19 in
  let rec loop (sym: bool) (c: chain)
               (tail: (bool * edge) list) =
    match c with
      RIdent -> tail
    | RSingle e -> begin
        (* Maybe this cancels out with something in the tail *)
        match tail with
          (sym', e') :: tail' when e == e' ->
            if sym <> sym' then
              tail'
            else begin
              ignore (E.warn "duplicate edge in chain");
              (* (sym, e) :: *) tail
            end
        | _ -> begin
            (* This is the place where we extend the tail. Check if we can
             * use a shorter tail *)
            let f = if sym then e.eto.id else e.efrom.id in
            let res = (sym, e) :: tail in
            Ccutil.findOrAdd tails f (fun _ -> res)
        end
    end
    | RSym c -> loop (not sym) c tail
    | RTrans (_, r1, r2, _, _) ->
        (* ignore (E.log "chainToList(%x)\n" (Obj.magic c)); *)
        if sym then
          loop sym r2 (loop sym r1 tail)
        else
          loop sym r1 (loop sym r2 tail)
    | RList (_, l, _, _) ->
        if sym then (* Must reverse the list as well *)
          List.fold_left
            (fun acc (isrev, h) ->
              loop (sym <> isrev) (RSingle h) acc)
            tail
            l
        else if tail = [] then
          l (* since sym = false && tail = [] *)
        else
        ( try
          List.fold_right
            (fun (isrev, h) acc ->
              loop (sym <> isrev) (RSingle h) acc)
            l
            tail
          with e ->
            (ignore (E.warn "List.fold_right raises %s"
              (Printexc.to_string e)) ; raise e)
        )
  in
  loop false c []

let rec getFirstAndLastNode (sym: bool) (c: chain) : node * node * int =
  match c with
    RSingle e ->
      let fn, ln = if sym then e.eto, e.efrom else e.efrom, e.eto in
      fn, ln, 1

  | RSym c -> getFirstAndLastNode (not sym) c
  | RTrans (fn, _, _, ln, len)
  | RList (fn, _, ln, len) ->
      if sym then ln,fn,len else fn,ln,len
  | _ -> E.s (E.bug "getFirstAndLastEdge: %a" d_chain c)

(* A helper function for concatenating chains. Call when both of the chains
 * are non-empty. *)
let mkRTransHelper (r1: chain) (r2: chain) : chain =
  let fn1, ln1, len1 = getFirstAndLastNode false r1 in
  let fn2, ln2, len2 = getFirstAndLastNode false r2 in
  (* Get the data about this whole path *)
  let pe, sym = getShortestChain fn1 ln2 in
  (* See if the new one has any chance of being better *)
  if pe.peLen <= len1 + len2 then
    if sym then mkRSym pe.peChain else pe.peChain (* Keep the old one *)
  else begin
    (* Prepare the possible result *)
    let res = RTrans(fn1, r1, r2, ln2, len1 + len2) in
    (* The new one is better. See how small it can get *)
    if debugChains then
      ignore (E.log "Finding best chain from %d->%d. Right now %d->%d(%d) + %d->%d(%d)\n"
                fn1.id ln2.id fn1.id ln1.id len1 fn2.id ln2.id len2);
    let l = chainToList res in
    let l_len = List.length l in
    if debugChains && l_len > 40 then begin
      ignore (E.log "  res=%a@!"
                (docList
                   (fun (sym, e) ->
                     if sym then dprintf "<-%d" e.efrom.id
                     else dprintf "->%d" e.eto.id))
                l);
    end;
    let bestLen, bestChain =
      if l_len < len1 + len2 then
        l_len, (if l_len = 0 then RIdent else RList (fn1, l, ln2, l_len))
      else
        len1+len2, res
    in
    (* Update the entry *)
    if debugChains then
      ignore (E.log "Setting best chain from %d->%d of length %d %s\n"
                fn1.id ln2.id bestLen
                (if bestLen < len1 + len2 then "(compressed)" else ""));
    pe.peLen <- bestLen;
    pe.peChain <- if sym then mkRSym bestChain else bestChain;
    bestChain
  end

let mkRTransChain (r1: chain) (r2: chain) =
  let isSymOf (r1: chain) (r2: chain) =
    match r1, r2 with
    | r1, RSym r1' when r1 == r1' -> true
    | RSym r2', r2 when r2 == r2' -> true
    | _, _ -> false
  in
  if not (keepDetails ()) then
    RIdent
  else begin
    match r1, r2 with
      RIdent, r2 -> r2
    | r1, RIdent -> r1
          (* It is important to recognize some special cases that lead to
          * exponential explosion *)
    | r1, r2 when isSymOf r1 r2 -> RIdent
    | r1, RTrans (_, r1', r2, _, _) when isSymOf r1 r1' -> r2
    | RTrans (_, r1, r2, _, _), r2' when isSymOf r2 r2' -> r1
    | _, _ -> mkRTransHelper r1 r2
  end

(* A mapping from place , index to ids. This will help us avoid creating
 * duplicate nodes *)
let placeId: (place * int, node) H.t = H.create 1111

(* A mapping from ids to nodes. Rarely we need to find a node based on its
 * index. *)
let idNode: (int, node) H.t = H.create 1111

(* Next identifier *)
let lastNodeId = ref (-1)

let pkInterface = 0          (* this is an interface node *)
let pkUpdated = 1            (* we write through this pointer *)
let pkIntCast = 2           (* can contain an integer *)
let pkPosArith = 3          (* subject to positive pointer arithmetic *)
let pkArith = 4             (* subject to arbitrary pointer arithmetic *)
let pkString = 5            (* A String node. The value at the end of the
                               buffer is a nul.  matth, sept05: This
                               flows forwards and backwards now.*)
let pkReachIndex = 6       (* can reach an Index node *)
let pkNoPrototype = 7     (* Used as actual argument in a function without
                              * prototype *)
let pkEscape = 8          (* value may be assigned thru a pointer and
                           * escape  to the heap *)
let pkNotSafe = 9    (* constraint used by solvers: node must not be Safe *)

let pkReferenced = 10 (* might be eventually referenced *)

let pkRtti = 11

let pkCompatWithScalars = 12
  (* This flag means that a void* node (or its equivalence class) must be
   * compatible with a scalar. Example:
   *   void *1 *2 v;
   *   int *3 x;
   *   v = x;
   * In this case, node 1 should have this flag.
   * (1) This flag is only valid on "void*" nodes. If a non-"void*" node
   * has this flag, that node should be WILD by the end of solving.
   * (2) This flag will always be present on the rep of a class if any node
   * in that class has it.
   * (3) If a node (or its rep) has this flag, then polymorphic_replace
   * will return Int for the type of that node.
   * (4) This flag is propagated whenever new reps are created.
   *)

let pkSplit = 13
let pkNeedsMetaPtr = 14
let pkNeedsMetaPtrBkwd = 15

(* Could point to the stack; CHECK_STORE_PTR and CHECK_RETURN needed.
 * This is too conservative, since we flow this flag through globals and the
 * heap, even though we know the checks will prevent that at runtime.  But
 * it's good enough for now. *)
let pkStack = 16

let pkOneWord = 17 (** Specified by user to be one word *)

let pkFlagName = (* should match up with the order above *)
  [| "Interface Node" ;
     "Updated" ;
     "Contains an Integer" ;
     "Positive Arithmetic" ;
     "Arithmetic" ;
     "Reaches String" ;
     "Reaches Index" ;
     "No Prototype" ;
     "Value Escapes to the Heap" ;
     "Cannot be SAFE" ;
     "Referenced";
     "Has RTTI" ;
     "Compatible with Scalars";
     "Split Metadata";
     "Needs Metadata Pointer";
     "Needs Metadata Pointer (Backward)";
     "Might Point To Stack";
     "One Word" |]

let pkNumberOfFlags = Array.length pkFlagName
let pkLastFlag = pkNumberOfFlags - 1

(* These are bitmasks of flags. *)
let pkCastPredFlags = [pkUpdated ; pkPosArith ; pkArith ; pkEscape ;
                       pkReferenced]
let pkCNIPredFlags =  [pkString ; pkReachIndex ]
let pkCastSuccFlags = [pkIntCast ; pkStack ; pkString]  (* all ECasts except copytags *)
let pkOffsetSuccFlags = [pkEscape ; pkSplit]
let pkPointsToSuccFlags = [pkSplit]

(* A list of all indices into the array *)
let allFlags =
  let rec allIndices (n: int) : int list =
    if n > pkLastFlag then [] else n :: allIndices (n + 1)
  in
  allIndices 0

let emptyFlags () = Array.make pkNumberOfFlags None

(* set a boolean bitflag *)
let setFlag n f why =
  if n.flags.(f) = None then n.flags.(f) <- Some(why)
(* check a boolean bitflag *)
let hasFlag n f = n.flags.(f) <> None

let canHaveRtti (t: typ) : bool = isVoidType t

let allKinds =
    [ Safe; Scalar; Seq;
      FSeq; SeqN; FSeqN;
      SeqR; FSeqR;
      String; ROString;
      Index; Wild;
      WildT; SeqT;
      FSeqT; SeqNT;
      FSeqNT; IndexT;
      SafeC; WildC; SeqC; FSeqC; SeqNC; FSeqNC;
      SeqRC; FSeqRC; RttiC;

      Rtti; Unknown ]

(* Just some code to check that we have added all pointer kinds to allKinds.
 * If the compiler complains about an inexhaustive pattern then you have
 * probalby added new pointer kinds. Add them to the pattern AND TO allKinds
 * above. *)
let _ =
  List.iter
    (function
      | Safe | SafeC | Scalar
      | String | ROString
      | Seq | SeqR | SeqC | SeqN | SeqT | SeqNT | SeqNC | SeqRC
      | FSeq | FSeqR | FSeqC | FSeqN | FSeqT | FSeqNT | FSeqNC | FSeqRC
      | Wild | WildT | WildC
      | Index | IndexT
      | Rtti | RttiC | Unknown -> ())
    allKinds

(* Print the graph *)
let d_place () = function
    PGlob s -> dprintf "Glob(%s)" s
  | PType s -> dprintf "Type(%s)" s
  | PStatic (f, s) -> dprintf "Static(%s.%s)" f s
  | PLocal (f, func, s) -> dprintf "Local(%s.%s.%s)" f func s
  | POffset (nid, fld) -> dprintf "Offset(%d, %s)" nid fld
  | PField(fi) -> dprintf "Field(%s.%s)" fi.fcomp.cname fi.fname
  | PAnon id -> dprintf "Anon(%d)" id

(* Print the place "nicely", in a human-readable format *)
let d_place_nice () (p,i) = match p with
    PGlob s -> dprintf "the global %s" s
  | PType s -> dprintf "the type %s" s
  | PStatic (f, s) -> dprintf "the static variable %s" s
  | PLocal (f, func, s) -> dprintf "the local variable %s" s
  | POffset (nid, fld) -> dprintf "the field %s of node %d" fld nid
  | PField(fi) -> dprintf "the field %s" fi.fname
  | PAnon id -> text "an unnamed location (often an inserted cast)"

let d_placeidx () (p, idx) =
  dprintf "%a.%d" d_place p idx

let d_opointerkind () = function
    Safe -> text "SAFE"
  | Scalar -> text "SCALAR"
  | FSeq -> text "FSEQ"
  | FSeqN -> text "FSEQN"
  | FSeqR -> text "FSEQR"
  | String -> text "NULLTERM"
  | ROString -> text "ROSTRING"
  | Index -> text "INDEX"
  | Seq -> text "SEQ"
  | SeqN -> text "SEQN"
  | SeqR -> text "SEQR"
  | Wild -> text "WILD"
  | WildT -> text "WILDT"
  | SeqT -> text "SEQT"
  | FSeqT -> text "FSEQT"
  | SeqNT -> text "SEQNT"
  | FSeqNT -> text "FSEQNT"
  | IndexT -> text "INDEXT"
  | SafeC -> text "SAFEC"
  | WildC -> text "WILDC"
  | SeqC -> text "SEQC"
  | FSeqC -> text "FSEQC"
  | SeqNC -> text "SEQNC"
  | FSeqNC -> text "FSEQNC"
  | SeqRC -> text "SEQRC"
  | FSeqRC -> text "FSEQRC"
  | Rtti -> text "RTTI"
  | RttiC -> text "RTTIC"
  | Unknown -> text "UNKNOWN"

let d_eekind () = function
    EEK_cast -> nil
  | EEK_cxxOverride -> text "(cxx_override)"
  | EEK_extends -> text "(extends)"
  | EEK_mkptr -> text "(mkptr)"
  | EEK_copytags -> text "(copytags)"
  | EEK_union -> text "(union)"
  | EEK_rtti -> text "(rtti)"

let d_ekind () = function
    ECast eek -> text "Cast" ++ d_eekind () eek
  | EOffset -> text "Offset"
  | EIndex -> text "Index"
  | ECompat(r) -> dprintf "Compat(%a)" d_chain r
  | ESameKind EEK_trustedCast -> text "TCast"
  | ESameKind EEK_taggedUnion -> text "Union"
  | EPointsTo -> text "Points"
  | EArgs -> text "Args"
  | ESameType -> text "SameClass"

let d_whyflag (n: node) () = function
  | ProgramSyntax(l) -> dprintf "Syntax at %a" d_loc l
  | DownCast(n) -> dprintf "Downcast With Node %d" n.id
  | SubtypeFailed(n) -> dprintf "Subtyping Failed With Node %d" n.id
  | RequiredByEdge(e) -> dprintf "Required By %a Edge %d->%d"
      d_ekind e.ekind e.efrom.id e.eto.id
  | RequiredByPointerKind(o) -> dprintf "Required For %a Nodes"
      d_opointerkind o
  | RequiredByFlag(i) -> dprintf "Required By Flag [%s]"
      pkFlagName.(i)
  | FlagSpreadFromNode(near,r_near_this,orig) ->
      dprintf "Spread from %d (%a). Transitive from %d"
        near.id d_chain r_near_this orig.id
  | FlUserSpec l -> text "User-specified at " ++ d_loc () l

let ptrAttrCustom =
  (* Define a hash table for printing the attributes *)
  let ptrAttrCustomTable: (string, string * (attrparam list -> doc)) H.t =
    let h: (string, string * (attrparam list -> doc)) H.t  = H.create 31 in
    let noArgs (al: attrparam list) : doc =
      match al with
        [] -> nil
      | _ -> raise Not_found
    in
    let doArgs (al: attrparam list) : doc =
      dprintf "(@[%a@])"
        (docList (d_attrparam ())) al
    in
    let addSimple (n: string) =
      H.add h n ("__" ^ String.uppercase n, noArgs)
    in
    List.iter addSimple
      ["ronly"; "seq"; "fseq"; "seqn"; "fseqn" ];
    H.add h "selector" ("__SELECTOR", doArgs);
    H.add h "selectedwhen" ("__SELECTEDWHEN", doArgs);
    H.add h "size" ("__SIZE", doArgs);
    H.add h "count" ("__COUNT", doArgs);
    h
  in
  fun ~(printnode: bool) (a: attribute) ->
    match a with
      Attr("_ptrnode", [AInt n]) ->
        if printnode then
          Some (dprintf "__NODE(%d)" n)
        else begin
          Some nil
        end
    | Attr("safe", []) ->
        if printnode then Some (text "__SAFE") else Some nil
    | Attr("discriminated_union", []) -> Some nil
    | Attr("seqr", []) -> Some (text "__SEQR")
    | Attr("fseqr", []) -> Some (text "__FSEQR")
    | Attr("index", []) -> Some (text "__INDEX")
    | Attr("wild", []) -> Some (text "__WILD")
    | Attr("seqt", []) -> Some (text "__SEQT")
    | Attr("fseqt", []) -> Some (text "__FSEQT")
    | Attr("seqnt", []) -> Some (text "__SEQNT")
    | Attr("fseqnt", []) -> Some (text "__FSEQNT")
    | Attr("indext", []) -> Some (text "__INDEXT")
    | Attr("wildt", []) -> Some (text "__WILDT")
    | Attr("safec", []) -> Some (text "__SAFEC")
    | Attr("wildc", []) -> Some (text "__WILDC")
    | Attr("seqc", []) -> Some (text "__SEQC")
    | Attr("fseqc", []) -> Some (text "__FSEQC")
    | Attr("seqnc", []) -> Some (text "__SEQNC")
    | Attr("fseqnc", []) -> Some (text "__FSEQNC")
    | Attr("seqrc", []) -> Some (text "__SEQRC")
    | Attr("fseqrc", []) -> Some (text "__FSEQRC")
    | Attr("stack", []) -> Some (text "__STACK")
    | Attr("opt", []) -> Some (text "__OPT")
    | Attr("string", []) -> Some (text "__NULLTERM")
    | Attr("rostring", []) -> Some (text "__ROSTRING")
    | Attr("sized", []) -> Some (text "__SIZED")
    | Attr("tagged", []) -> Some (text "__TAGGED")
    | Attr("trustedunion", []) -> Some (text "__TRUSTEDUNION")
    | Attr("safeunion", []) -> Some (text "__SAFEUNION")
    | Attr("nullterm", []) -> Some (text "__NULLTERM_BUFFER")
    | Attr("heapify", []) -> Some (text "__HEAPIFY")
    | Attr("nocure", []) -> Some (text "__NOCURE")
    | Attr("rtti",[]) -> Some (text "__RTTI")
    | Attr("rttic",[]) -> Some (text "__RTTIC")
    | Attr("split",[]) -> Some (text "__SPLIT")
    | Attr("compat",[]) -> Some (text "__COMPAT")
    | Attr("nounroll",[]) -> Some (text "__NOUNROLL")
    | Attr("lean",[]) -> Some (text "__LEAN")
    | Attr("noescape", []) -> Some (text "__NOESCAPE")
    | Attr("ccuredvararg", [ASizeOf t]) -> Some (text "__CCUREDVARARG(" ++
                                                d_type () t ++ text ")")
    | Attr("ccuredformat", [AInt fidx]) -> Some (text "__CCUREDFORMAT(" ++
                                                num fidx ++ text ")")
    | Attr("override", [AStr s]) -> Some (text ("__OVERRIDE(\"" ^ s ^ "\")"))
    | Attr("main_input", []) -> Some (text (""))
    | Attr("metacomp", []) -> Some (text "")
    | Attr("mergecomp", []) -> Some (text "")
    | Attr("mdsize", _) -> Some (text "")
    | Attr("annotated", _) -> Some (text "")
    | Attr (n, args) -> begin
        try
          let n', args' = H.find ptrAttrCustomTable n in
          Some (text n' ++ (args' args))
        with Not_found -> None
    end

(* Now define a special way of printing the infer file *)
class ccuredInferPrinterClass = object
  inherit defaultCilPrinterClass as super

  method pAttr (a: attribute) : doc * bool =
    match ptrAttrCustom ~printnode:true a with
      Some d -> d, false
    | None -> super#pAttr a

  (* We do not print some pragmas *)
  method dGlobal (out: out_channel) (g: global) : unit =
    match g with
    | GPragma(Attr(n, _), _) ->
        if hasPrefix "ccured" n || hasPrefix "cil" n then
          if !printVerboseOutput then begin
            fprint out 80 (text "// ");
            super#dGlobal out g
          end else
            ()
        else
          ()

    | GText t ->
        if !printVerboseOutput || not (t = "//\n") then
          super#dGlobal out g

    | g -> super#dGlobal out g

end
let ccuredInferPrinter = new ccuredInferPrinterClass

(* And a way of printing the file after curing. Like the INFER file but
 * without the nodes. *)
class ccuredPrinterClass = object (self)
  inherit ccuredInferPrinterClass as super
  val mutable currentFormals : varinfo list = []
  method private getLastNamedArgument (s: string) : exp =
    match List.rev currentFormals with
      f :: _ -> Lval (var f)
    | [] -> (* zero *)
        E.s (bug "Cannot find the last named argument when printing call to %s\n" s)

  method pAttr (a: attribute) : doc * bool =
    match ptrAttrCustom ~printnode:false a with
      Some d -> d, false
    | None -> super#pAttr a

  (* Do not print the prototype for "_setjmp_w" because we have a macro with
   * the same name *)
  method pGlobal () (g: global) : doc =
    match g with
      GVarDecl (v, _) when (v.vname = "_setjmp_w" ||
                            v.vname = "setjmp_w") -> nil
    | _ -> super#pGlobal () g

  (* When you print GCC_STDARG_START we must print the last argument of the
   * current function *)
  method pInstr () (i: instr) =
    match i with
    | Call(dest, Lval(Var vi, NoOffset), [], l)
        when vi.vname = "GCC_STDARG_START" && not !printCilAsIs -> begin
          let last = self#getLastNamedArgument vi.vname in
          super#pInstr () (Call(dest,Lval(Var vi,NoOffset),[last],l))
        end
    | _ -> super#pInstr () i

  method dGlobal out (g: global) =
    (match g with GFun(f, _) -> currentFormals <- f.sformals | _ -> ());
    super#dGlobal out g
end

let ccuredPrinter = new ccuredPrinterClass

let d_type = printType ccuredInferPrinter

let d_whykind (n: node) () = function
  | BadCast e ->
      dprintf "cast(%a(%d) <= %a(%d)) at %a"
        d_type e.eto.btype e.eto.id d_type e.efrom.btype e.efrom.id
        d_loc e.eloc
  | BadSequenceCast e ->
      dprintf "cast(%a(%d) <= %a(%d)) at %a (and cannot be sequence)"
        d_type e.eto.btype e.eto.id d_type e.efrom.btype e.efrom.id
        d_loc e.eloc
  | Incompat (n1, why_n1_n2, n2) ->
      dprintf "Incompat %d and %d (%a)"
        n1.id n2.id d_chain why_n1_n2
(*
  | UnsafeUnion ci ->
      dprintf "unsafe_union(%s)" ci.cname
*)

  | BoolFlag(i) -> dprintf "from_flag(%s)" pkFlagName.(i)
  | PolyInt -> dprintf "void* equivalent to scalar"
  | Default -> text "by_default"
  | UserSpec -> text "user_spec"
  | Unconstrained -> text "unconstrained"
  | PrintfArg -> text "printf_arg"
  | Special (s, l) -> text (s ^ " at ") ++ d_loc () l
  | SpreadFromNode(near,r_near_this,orig) ->
      dprintf "Spread from %d (%a). Transitive from %d\n"
        near.id d_chain r_near_this orig.id

let d_node () n =
    num n.id
     ++ text " : "
     ++ (match n.rep with
          None -> nil
        | Some (nrep, _) -> dprintf "(rep is %d) " nrep.id)
     ++ (if !emitGraphDetailLevel > 1 then d_placeidx () n.where  else nil)
     ++ (if !emitGraphDetailLevel > 1 then text " L=" ++ Cil.d_loc () n.loc else nil)
     ++ line
     ++ text " K="  ++ d_opointerkind () n.kind
     ++ text "/"  ++ (d_whykind n) () n.why_kind
     ++ (if !emitGraphDetailLevel > 0 then text " T="  ++ d_type () n.btype else nil)
     ++
     (if !emitGraphDetailLevel > 0 &&
       (Array.fold_left (fun acc elt -> acc || elt <> None) false n.flags)
     then begin
       line ++ text "Flags: "
         ++ (align
               ++ (docArray ~sep:(text "")
                     (fun i flag_opt -> match flag_opt with
                       (* Do not print the pkNotSafe flag. It is for internal
                        * use and in the case of polymorphic_void* we
                        * actuallly may make such nodes SAFE, creating
                        * confusion *)
                     | Some(why) when i <> pkNotSafe ->
                         dprintf "@![%s]: %a" pkFlagName.(i) (d_whyflag n) why
                     | _ -> nil
                           ) () n.flags)
               ++ unalign ++ line)
     end else begin
       nil
     end)
    ++
    (if !emitGraphDetailLevel > 1 then
      line
        ++ text "  S="
        ++ (align
              ++ (docList ~sep:(chr ',' ++ break)
                    (fun e ->
                      num e.eto.id
                        ++ text ":"
                        ++ d_ekind () e.ekind
                        ++ text "@" ++ d_loc () e.eloc)
                    ()
                    n.succ)
              ++ unalign)
        ++ line
        ++ text "  P="
        ++ (align
              ++ (docList ~sep:(chr ',' ++ break)
                    (fun e ->
                      num e.efrom.id
                        ++ text ":"
                        ++ d_ekind () e.ekind)
                    ()
                    n.pred)
              ++ unalign)
     else nil)

    ++ line

let nodeOfAttrlist al =
  let findnode n =
    try Some (H.find idNode n)
    with Not_found -> E.s (E.bug "Cannot find node with id = %d\n" n)
  in
  match filterAttributes "_ptrnode" al with
    [] -> None
  | [Attr(_, [AInt n])] -> findnode n
  | (Attr(_, [AInt n]) :: _) as filtered ->
      ignore (E.warn "nodeOfAttrlist(%a)" d_attrlist filtered);
      findnode n
  | _ -> E.s (E.bug "nodeOfAttrlist")

let nodeOfType (t: typ) : node option =  nodeOfAttrlist (typeAttrs t)

(* weimer: find the node that points to this one *)
let nodeThatPointsTo (child : node) =
  try
    let e = List.find (fun e -> e.ekind = EPointsTo) child.pred in
    Some e.efrom
  with Not_found -> None

let stripT = function
  | WildT -> Wild
  | SeqT -> Seq
  | FSeqT -> FSeq
  | SeqNT -> SeqN
  | FSeqNT -> FSeqN
  | IndexT -> Index
  | x -> x

let addT = function
  | Wild -> WildT
  | Seq -> SeqT
  | FSeq -> FSeqT
  | SeqN -> SeqNT
  | FSeqN -> FSeqNT
  | Index -> IndexT
  | x -> x

let isT k = stripT k <> k

let stripRTTI = function
  | Rtti -> Safe
  | FSeqR -> FSeq
  | SeqR -> Seq
  | RttiC -> SafeC
  | FSeqRC -> FSeqC
  | SeqRC -> SeqC
  | x -> x

let addRTTI = function
  | Safe -> Rtti
  | FSeq -> FSeqR
  | Seq -> SeqR
  | SafeC -> RttiC
  | FSeqC -> FSeqRC
  | SeqC -> SeqRC
  | x -> x

let isRTTI k = stripRTTI k <> k

let stripC = function
  | SafeC -> Safe
  | WildC -> Wild
  | SeqC -> Seq
  | FSeqC -> FSeq
  | SeqNC -> SeqN
  | FSeqNC -> FSeqN
  | SeqRC -> SeqR
  | FSeqRC -> FSeqR
  | RttiC -> Rtti
  | x -> x

let addC = function
  | Safe -> SafeC
  | Wild -> WildC
  | Seq -> SeqC
  | FSeq -> FSeqC
  | SeqN -> SeqNC
  | FSeqN -> FSeqNC
  | SeqR -> SeqRC
  | FSeqR -> FSeqRC
  | Rtti -> RttiC
  | x -> x

let isC k = stripC k <> k

let k2attr = function
    Safe -> Attr("safe", [])
  | Index -> Attr("index", [])
  | Wild -> Attr("wild", [])
  | Seq -> Attr("seq", [])
  | FSeq -> Attr("fseq", [])
  | SeqN -> Attr("seqn", [])
  | FSeqN -> Attr("fseqn", [])
  | SeqR -> Attr("seqr", [])
  | FSeqR -> Attr("fseqr", [])
  | IndexT -> Attr("indext", [])
  | WildT -> Attr("wildt", [])
  | SeqT -> Attr("seqt", [])
  | FSeqT -> Attr("fseqt", [])
  | SeqNT -> Attr("seqnt", [])
  | FSeqNT -> Attr("fseqnt", [])
  | SafeC -> Attr("safec", [])
  | WildC -> Attr("wildc", [])
  | SeqC -> Attr("seqc", [])
  | FSeqC -> Attr("fseqc", [])
  | SeqNC -> Attr("seqnc", [])
  | FSeqNC -> Attr("fseqnc", [])
  | SeqRC -> Attr("seqrc", [])
  | FSeqRC -> Attr("fseqrc", [])
  | String -> Attr("string", [])
  | ROString -> Attr("rostring", [])
  | Rtti -> Attr("rtti", [])
  | RttiC -> Attr("rttic", [])
  | k -> E.s (E.unimp "k2attr:%a" d_opointerkind k)

let metaptr_kind      = 256
let dynamic_type_kind = 128
let nullterm_kind     =  64
let table_kind        =  32
let rtti_kind         =  16
let rec k2number = function
  | Scalar -> 0
  | Safe -> 1
  | Seq ->  2
  | FSeq -> 3
  | Index -> 4
  | ROString -> 5
  | String ->  6
  | Rtti -> 0 + rtti_kind
  | Wild -> 0 + dynamic_type_kind
  | SeqN -> nullterm_kind + k2number Seq
  | FSeqN -> nullterm_kind + k2number FSeq
  | SeqR -> rtti_kind + k2number Seq
  | FSeqR -> rtti_kind + k2number FSeq
  | IndexT -> table_kind + k2number Index
  | WildT -> table_kind + k2number Wild
  | SeqT -> table_kind + k2number Seq
  | FSeqT -> table_kind + k2number FSeq
  | SeqNT -> table_kind + nullterm_kind + k2number Seq
  | FSeqNT -> table_kind + nullterm_kind + k2number Seq
  | SafeC -> metaptr_kind + k2number Safe
  | SeqC -> metaptr_kind + k2number Seq
  | FSeqC -> metaptr_kind + k2number FSeq
  | SeqNC -> metaptr_kind + k2number SeqN
  | FSeqNC -> metaptr_kind + k2number FSeqN
  | SeqRC -> metaptr_kind + k2number SeqR
  | FSeqRC -> metaptr_kind + k2number FSeqR
  | RttiC -> metaptr_kind + k2number Rtti
  | k -> E.s (E.unimp "k2number:%a" d_opointerkind k)

(*
let pk2attr (pk: pkind) : attribute =
  k2attr (pk2okind pk)
  *)

let kindOfAttrlist al =
  let rec loop = function
      [] -> Unknown, Default
    | a :: al -> begin
        match a with
          Attr ("safe", []) -> Safe, UserSpec
        | Attr ("index", []) -> Index, UserSpec
        | Attr ("seq", []) -> Seq, UserSpec
        | Attr ("fseq", []) -> (if !useFSEQ then FSeq else Seq), UserSpec
        | Attr ("seqn", []) -> (if !useStrings then SeqN else Seq), UserSpec
        | Attr ("fseqn", []) ->
            (if !useFSEQ
             then (if !useStrings then FSeqN else FSeq)
             else (if !useStrings then SeqN else Seq)), UserSpec
        | Attr ("fseqr", []) ->
            (if !useFSEQ
            then (if !useRTTI then FSeqR else FSeq)
            else (if !useRTTI then SeqR else Seq)), UserSpec
        | Attr ("seqr", []) ->
            (if !useRTTI then SeqR else Seq), UserSpec
        | Attr ("fseqrc", []) ->
            (if !useFSEQ
            then (if !useRTTI then FSeqRC else FSeqC)
            else (if !useRTTI then SeqRC else SeqC)), UserSpec
        | Attr ("seqrc", []) ->
            (if !useRTTI then SeqRC else SeqC), UserSpec

        | Attr ("wild", []) -> Wild, UserSpec
        | Attr ("wildt", []) -> WildT, UserSpec
        | Attr ("seqt", []) -> SeqT, UserSpec
        | Attr ("fseqt", []) -> FSeqT, UserSpec
        | Attr ("seqnt", []) -> SeqNT, UserSpec
        | Attr ("fseqnt", []) -> FSeqNT, UserSpec
        | Attr ("safec", []) -> SafeC, UserSpec
        | Attr ("wildc", []) -> WildC, UserSpec
        | Attr ("seqc", []) -> SeqC, UserSpec
        | Attr ("fseqc", []) -> FSeqC, UserSpec
        | Attr ("seqnc", []) -> SeqNC, UserSpec
        | Attr ("fseqnc", []) -> FSeqNC, UserSpec
        | Attr ("sized", []) -> Index, UserSpec
        | Attr ("tagged", []) -> Wild, UserSpec
        | Attr ("string", []) when !useStrings -> String, UserSpec
        | Attr ("rostring", [])
            when !useStrings -> ROString, UserSpec
        | Attr ("rtti",[]) when !useRTTI -> Rtti, UserSpec
        | Attr ("rttic",[]) when !useRTTI -> RttiC, UserSpec
        | Attr ("nullterm", []) when !useStrings ->
            (* You might say "nullterm rostring", so we have to look
             * at the rest of the list to find this. *)
            begin
              let rest_kind, _ = loop al in
              match rest_kind with
                Unknown -> String, UserSpec
              | k -> k, UserSpec
            end
        (* weimer: also look in "nodes" to find the kind *)
        | Attr ("_ptrnode", [AInt n]) -> begin
              let nd = H.find idNode n in
              if nd.kind = Unknown then (* not useful *)
                loop al
              else
                nd.kind, nd.why_kind
            end
        | _ -> loop al
    end
  in
  loop al

(* Replace the ptrnode attribute with the actual qualifier attribute *)
type whichAttr =
    AtPtr  (* In a pointer type *)
  | AtArray  (* In an array type *)
  | AtOpenArray (* In an array type without a size *)
  | AtVar (* For a variable *)
  | AtOther (* Anything else *)


let replacePtrNodeAttrList ~(which:whichAttr) al =
(*  ignore (E.log "replacePtrNode: %a\n"
            (d_attrlist true) al); *)
  let foundKind : string ref = ref "" in
  let foundInNode : bool ref = ref false in
  let foundAnother (innode: bool) (s: string) =
    if innode then begin
      foundInNode := true;
      foundKind := s (* Discard all others *)
    end else
      (* Look at non-node ones only if we haven't found a node *)
      if not !foundInNode then foundKind := s
  in
  (* Scan the attributes and look at pointer kind attributes and at node
   * attributes. Remove all pointer-kind attributes and set foundKind and
   * foundInNode if it was found in a node. *)
  let rec loop = function
      [] -> []
    | a :: al -> begin
        match a with
          Attr("_ptrnode", [AInt n]) -> begin
            try
              let nd = H.find idNode n in
              let found =
                if nd.kind = Unknown then begin
                  ignore (E.warn "Found node %d with kind Unknown\n" n);
                  ""
                end else
                  match k2attr nd.kind with
                    Attr(s, _)  -> s
              in
              foundAnother true found;
              a :: loop al
            with Not_found -> begin
              ignore (E.warn "Cannot find node %d\n" n);
              a :: loop al
            end
          end
        | Attr("safe", []) -> foundAnother false "safe"; loop al
        | Attr("index", []) -> foundAnother false "index"; loop al
        | Attr("seq", []) -> foundAnother false "seq"; loop al
        | Attr("fseq", []) ->
            foundAnother false (if !useFSEQ then "fseq" else "seq"); loop al
        | Attr("seqn", []) ->
            foundAnother false (if !useStrings then "seqn" else "seq"); loop al
        | Attr("fseqn", []) ->
            foundAnother false
              (if !useFSEQ then
                (if !useStrings then "fseqn" else "fseq")
              else (if !useStrings then "seqn" else "seq")); loop al
        | Attr("seqr", []) ->
            foundAnother false (if !useRTTI then "seqr" else "seq"); loop al
        | Attr("fseqr", []) ->
            foundAnother false
              (if !useFSEQ then
                (if !useRTTI then "fseqr" else "fseq")
              else (if !useRTTI then "seqr" else "seq")); loop al
        | Attr("seqrc", []) ->
            foundAnother false (if !useRTTI then "seqrc" else "seqc"); loop al
        | Attr("fseqrc", []) ->
            foundAnother false
              (if !useFSEQ then
                (if !useRTTI then "fseqrc" else "fseqc")
              else (if !useRTTI then "seqrc" else "seqc")); loop al
        | Attr("wild", []) -> foundAnother false "wild"; loop al
        | Attr("indext", []) -> foundAnother false "indext"; loop al
        | Attr("seqt", []) -> foundAnother false "seqt"; loop al
        | Attr("fseqt", []) -> foundAnother false "fseqt"; loop al
        | Attr("seqnt", []) -> foundAnother false "seqnt"; loop al
        | Attr("fseqnt", []) -> foundAnother false "fseqnt"; loop al
        | Attr("wildt", []) -> foundAnother false "wildt"; loop al
        | Attr("safec", []) -> foundAnother false "safec"; loop al
        | Attr("wildc", []) -> foundAnother false "wildc"; loop al
        | Attr("seqc", []) -> foundAnother false "seqc"; loop al
        | Attr("fseqc", []) -> foundAnother false "fseqc"; loop al
        | Attr("seqnc", []) -> foundAnother false "seqnc"; loop al
        | Attr("fseqnc", []) -> foundAnother false "fseqnc"; loop al
        | Attr("sized", []) -> foundAnother false "sized"; loop al
        | Attr("tagged", []) -> foundAnother false "tagged"; loop al
        | Attr("rtti", []) when !useRTTI -> foundAnother false "rtti"; loop al
        | Attr("rttic", []) when !useRTTI -> foundAnother false "rttic"; loop al
        | Attr("string", []) when !useStrings ->
            foundAnother false "string"; loop al
        | Attr("rostring", []) when !useStrings ->
            foundAnother false "rostring"; loop al
        | _ -> a :: loop al
    end
  in
  let al' = loop al in (* Get the filtered attributes *)
  let kres =
    match which with
      AtPtr ->
        if !foundKind <> "" then !foundKind
        else if !defaultIsWild then "wild" else "safe"
    | (AtArray | AtOpenArray) ->
        if !foundKind = "index" then "sized"
        else if !foundKind = "indext" then "sized"
        else if !foundKind = "seqn" then "nullterm"
        else if !foundKind = "fseqn" then "nullterm"
        else if !foundKind = "seqnt" then "nullterm"
        else if !foundKind = "fseqnt" then "nullterm"
        else if !foundKind = "string" then "nullterm"
        else if !foundKind = "rostring" then "nullterm"
        else if !foundKind = "wild" then "wild"
        else if !foundKind = "wildt" then "wild"
        else if which = AtOpenArray then
          if !defaultIsWild then "wild" else "sized"
        else !foundKind
    | AtVar ->
        if !foundKind = "wild" then "tagged"
        else if !foundKind = "wildt" then "tagged"
        else !foundKind
    | AtOther -> !foundKind
  in
  if kres <> "" then
    addAttribute (Attr(kres,[])) al'
  else
    al'

let nodeExists (p: place) (idx: int) =
  H.mem placeId (p, idx)

let existsEdge ~(start : node) ~(dest : node) ~(kind : edgekind) =
  List.fold_left (fun acc e -> acc ||
   (e.eto.id = dest.id && e.ekind = kind)) false start.succ

let isECompat e =
  match e.ekind with
    ECompat _ -> true
  | _ -> false

let isECast e =
  match e.ekind with
    ECast _ -> true
  | _ -> false

let isESameKind e =
  match e.ekind with
    ESameKind _ -> true
  | _ -> false

let lastEdgeIdx = ref 0 (* 0 is reserved for the union edge *)
let addEdge ~(start: node) ~(dest: node) ~(kind: edgekind)
            ~(eloc : Cil.location option) =

  incr lastEdgeIdx;
  let nedge =
    { eid = !lastEdgeIdx;
      efrom = start; eto= dest; ekind = kind;
      eloc = match eloc with
              Some(loc) -> loc
            | None -> !currentLoc } in
  start.succ <- nedge :: start.succ;
  dest.pred <- nedge :: dest.pred ;
  nedge

let removeSucc n sid =
  n.succ <- List.filter (fun e -> e.eto.id <> sid) n.succ

let removePred n pid =
  n.pred <- List.filter (fun e -> e.efrom.id <> pid) n.pred

(** Set the EPointsTo edges for a node. *)
let setNodePointsTo (n: node) =
  let doOneType = function
      (* This will add points to to pointers embedded in structures or in
       * functions (function return or arguments) *)
      TPtr (bt, a) -> begin
        (match nodeOfAttrlist a with
        | Some n' -> ignore (addEdge n n' EPointsTo (Some n.loc))
        | _ -> (*
           ignore
              (warn "Node %d points to a pointer of type %a without a node"
                 n.id d_type bt); *)
            ());
        ExistsFalse
      end
    | _ -> ExistsMaybe
  in
  ignore (existsType doOneType n.btype);


  (* If a structure contains an array, a pointer to that structure also
   * contains a pointer to the array. We need this information to
   * properly handle wild pointers. *)
  let lookForInternalArrays = function
      TArray(bt,len,al) -> begin
        (match nodeOfAttrlist al with
        | Some n' -> ignore (addEdge n n' EPointsTo (Some !currentLoc))
        | _ -> ());
        ExistsFalse
      end

    | _ -> ExistsMaybe
  in
  ignore (existsType lookForInternalArrays n.btype)

(* Make a new node *)
let newNode ~(p: place) ~(idx: int) ~(bt: typ) ~(al: attributes) : node =
  let where = p, idx in
  incr lastNodeId;
  (* Maybe it has a kind specified by the user *)
  let kind,why_kind = kindOfAttrlist al in
(*  if !lastNodeId = 1 then
    ignore (E.log "newNode: %a\n" d_opointerkind kind); *)
  let n = { id = !lastNodeId;
            btype   = bt;
            attr    = addAttribute (Attr("_ptrnode", [AInt !lastNodeId])) al;
            is_array = false;
            where   = where;
            flags   = emptyFlags () ;
            locked = false;
            succ = [];
            kind = kind;
            why_kind = why_kind;
            mark = false;
            pred = [];
            rep = None;
            loc = !Cil.currentLoc; }
  in
  if hasAttribute "noescape" al then
    setFlag n pkStack (FlUserSpec !Cil.currentLoc);
(*  ignore (E.log "Created new node(%d) at %a\n" n.id d_placeidx where); *)
  H.add placeId where n;
  H.add idNode n.id n;
  (* We do not yet set the EPointsTo edges because we might have forward
   * references. But once we have created all the nodes, we should call the
   * setNodePointsTo *)
  setNodePointsTo n;
  n

(** Dummy node is a node with the ID=0 *)
let dummyNode = newNode (PGlob "@dummy") 0 voidType []

(* Get a node for a place and an index. Give also the base type and the
 * attributes *)
let getNode ~(p: place) ~(idx: int) ~(bt: typ) ~(al: attributes) : node =
  (* See if exists already *)
  let where = (p, idx) in
  try
    H.find placeId where
  with Not_found -> newNode p idx bt al

            (** Check that a node points to another node *)
let rec checkPointsTo (seen: int list) (* To prevent recursion *)
    (nstart: node)
    (nend_id: int) : bool =
  (* Scan all EPoints successors of nstart *)
  if nstart.id = nend_id then true
  else begin
    if List.exists (fun s -> s = nstart.id) seen then begin
      ignore (E.log "checkPointsTo: circularity at %d\n" nstart.id);
      false
    end else begin
      let seen' = nstart.id :: seen in
      List.exists (fun e ->
        e.ekind = EPointsTo &&
        checkPointsTo seen' e.eto nend_id) nstart.succ
    end
  end

            (* Check that a node does not occur twice in a chain. We use
             * this function to debug circular chains *)
let rec checkChain
        (start: node) (* The node that we think the edge should
                       * be starting from *)
        (r: chain) : node * int list =
  if not (keepDetails ()) then
    E.s (bug "checkChains but not keeping details");
  let edges = chainToList r in
  let rec loop (start: node) (* The next expected node *)
               (seen: int list) (* Nodes we've seen already *) = function
      [] -> start, seen
    | (sym, e) :: rest ->
        (* Orient the edge appropriately *)
        let estart, eend = if sym then e.eto, e.efrom else e.efrom, e.eto in
        (* Check that we start at the right points. estart must be pointing to
        * start or viceversa *)
        if start.id <> 0 &&
          not (checkPointsTo [] start estart.id) &&
          not (checkPointsTo [] estart start.id) then begin
            ignore (E.warn
                      "Disconnected chain: start=%d, edge %d->%d\n seen = %a\n"
                      start.id e.efrom.id e.eto.id
                      (docList num) (List.rev seen));
            raise (Failure "bad chain: disconnected")
          end;
        (* Complain if we've seen eend.id already *)
        if List.exists (fun s -> s = eend.id) seen then begin
          ignore (E.warn
                    "Circular chain: start=%d, edge %d->%d\n seen = %a\n"
                    start.id e.efrom.id e.eto.id
                    (docList num) (List.rev seen));
          raise (Failure "bad chain: circular")
        end;
        loop eend (eend.id :: (if start.id = 0 then [estart.id] else seen))
          rest
  in
  loop start [] edges

let checkChainEnds (nstart: node) (nend: node) (r: chain) : unit =
  try
    let end', seen'  = checkChain nstart r in
    if not (checkPointsTo [] end' nend.id) &&
       not (checkPointsTo [] nend end'.id) then begin
        ignore (E.warn "checkChainEnds. Ends at %d and expected %d\n"
                  end'.id nend.id);
        raise (Failure "bad chain: misoriented edge")
      end
  with e -> begin
    ignore (E.log "Failed the check that chain starts at %d and ends at %d\n"
              nstart.id nend.id);
    ();
  end

(* Override mkRTrans to do some checking *)
let mkRTrans (r1: chain) (r2: chain) =
  let res = mkRTransChain r1 r2 in
  if doCheckChains && res != r1 && res != r2 then begin
    try
      ignore (checkChain dummyNode res);
    with e -> begin
      ignore (E.warn "Trying to mkRTrans of");
      dumpChain r1;
      ignore (E.log "  and \n");
      dumpChain r2;
      raise e
    end
  end;
  res

(* Given a flag for a node, produce the original node where the flag
 * originates, the true chain why it originates, and the chain:orig->this *)
let rec trueSourceOfFlag (n: node) (f:int) : node * whyflag * chain =
  match n.flags.(f) with
  | Some(FlagSpreadFromNode(near,r_near_n,source)) when near.id <> n.id ->
      let orig, why, r_orig_near = trueSourceOfFlag near f in
      orig, why, mkRTrans r_orig_near r_near_n
  | Some w -> n, w, mkRIdent
  | None -> E.s (bug "trueSourceOfFlag(%d, %d)" n.id f)

(* obtain the representative of this equivalence class. Also return the
 * reaons n -> representative *)
let rec get_rep_why (n: node) : node * chain =
  match n.rep with
    Some(nr,why_n_nr) ->
      let final_result, why_nr_final_result = get_rep_why nr in
      if final_result == nr then
        nr, why_n_nr
      else begin
        (* Do path compression *)
        let why_n_final_result = mkRTrans why_n_nr why_nr_final_result in
        if not (hasFlag n pkRtti) then begin
          (if hasFlag n pkCompatWithScalars then
            let orig,_,_ = trueSourceOfFlag n pkCompatWithScalars in
            setFlag final_result pkCompatWithScalars
              (FlagSpreadFromNode(n,why_n_final_result,orig)));
          n.rep <- Some(final_result, why_n_final_result) ;
        end ;
        final_result, why_n_final_result
      end
  | None -> n, mkRIdent

let rec get_rep n = fst (get_rep_why n)

let rec join n1 n2 (why_n1_n2: chain) (* The chain goes n1 -> n2 *) =
  (if doCheckChains then checkChainEnds n1 n2 why_n1_n2);
  let n1r, why_n1_n1r = get_rep_why n1 in
  let n2r, why_n2_n2r = get_rep_why n2 in
  if n1r.id = n2r.id then begin
    () (* only join if they are distinct *)
  end else begin
    if isVoidType n1r.btype then begin (* n2r becomes the new rep *)
      if not (hasFlag n1r pkRtti) then begin
        (* chain: n1r -> n1 -> n2 -> n2r *)
        let why_n1r_n2r =
          mkRTrans (mkRSym why_n1_n1r) (mkRTrans why_n1_n2 why_n2_n2r)
        in
        n1r.rep <- Some(n2r, why_n1r_n2r);
        if hasFlag n1r pkCompatWithScalars then begin
          let res,_,_ = trueSourceOfFlag n1r pkCompatWithScalars in
          setFlag n2r pkCompatWithScalars
            (FlagSpreadFromNode(n1r, why_n1r_n2r, res))
        end
      end
    end else if isVoidType n2r.btype then begin (* n1r becomes the new rep *)
      if not (hasFlag n2r pkRtti) then begin
        let why_n2r_n1r =
          mkRTrans (mkRSym why_n2_n2r) (mkRTrans (mkRSym why_n1_n2) why_n1_n1r)
        in
        n2r.rep <- Some(n1r, why_n2r_n1r);
        if hasFlag n2r pkCompatWithScalars then
          let res,_,_ = trueSourceOfFlag n2r pkCompatWithScalars in
          setFlag n1r pkCompatWithScalars
            (FlagSpreadFromNode(n2r, why_n2r_n1r, res))
      end
    end else
      (* Do not join nodes whose representatives are not void-ptr *)
      ()
  end
(*
  ignore (E.warn "join %d(%b) %d(%b) -> %d(%b)"
    n1.id (hasFlag n1 pkCompatWithScalars)
    n2.id (hasFlag n2 pkCompatWithScalars)
    (get_rep n1).id (hasFlag (get_rep n1) pkCompatWithScalars)
    )  *)

(* Given a kind for a node, produce the original node where the kind
 * originates, the true chain why it originates, and the chain:orig->this *)
let rec trueSourceOfKind (n: node) : node * whykind * chain =
  match n.why_kind with
  | SpreadFromNode(near,r_near_n,source) ->
      let orig, why, r_orig_near = trueSourceOfKind near in
      orig, why, mkRTrans r_orig_near r_near_n
  | w -> n, w, mkRIdent

(* Type names, computed in such a way that compatible types have the same id,
 * even if they are syntactically different. Right now we flatten structures
 * but we do not pull common subcomponents out of unions and we do not unroll
 * arrays. *)

(* Some structs (those involved in recursive types) are named. This hash maps
 * their name to the ID *)
let namedStructs : (string, string) H.t = H.create 110

(* Keep track of the structs in which we are (to detect loops). When we
 * detect a loop we remember that *)
let inStruct : (string, bool ref) H.t = H.create 110

let rec typeIdentifier (t: typ) : string =
  let res = typeId t in
  H.clear inStruct;  (* Start afresh next time *)
  res

and typeId = function
    TInt(ik, a) -> ikId ik ^ attrsId a
  | TVoid a -> "V" ^ attrsId a
  | TFloat (fk, a) -> fkId fk ^ attrsId a
  | TEnum _ -> ikId IInt (* !!! *)
  | TNamed (t, a) -> typeId (typeAddAttributes a t.ttype)
  | TComp (comp, a) when comp.cstruct -> begin
      (* See if we are in a loop *)
      try
        let inloop = H.find inStruct comp.cname in
        inloop := true; (* Part of a recursive type *)
        "t" ^ prependLength comp.cname (* ^ attrsId comp.cattr *)
      with Not_found ->
        let inloop = ref false in
        let isanon = hasPrefix "__anon" comp.cname  in
        if not isanon then H.add inStruct comp.cname inloop;
        let fieldsids =
          List.fold_left (fun acc f -> acc ^ typeId f.ftype) "" comp.cfields in
        (* If it is in a loop then keep its name *)
        let res = fieldsids (* ^ attrsId comp.cattr *) in
        if not isanon then H.remove inStruct comp.cname;
        if !inloop && not (H.mem namedStructs comp.cname) then begin
          H.add namedStructs comp.cname res;
          "t" ^ prependLength comp.cname (* ^ attrsId comp.cattr *)
        end else
          res
  end
  | TComp (comp, a) when not comp.cstruct ->
      "N" ^ (string_of_int (List.length comp.cfields)) ^
      (List.fold_left (fun acc f -> acc ^ typeId f.ftype ^ "n")
         "" comp.cfields) ^
      attrsId (addAttributes comp.cattr  a)
  | TPtr (t, a) -> "P" ^ typeId t ^ "p" ^ attrsId a
  | TArray (t, lo, a) ->
      let thelen = "len" in
      "A" ^ typeId t ^ "a" ^ prependLength thelen ^ attrsId a
  | TFun (tres, args, va, a) ->
      "F" ^ typeId tres ^ "f" ^
      (string_of_int (List.length (argsToList args))) ^
      (List.fold_left (fun acc (_, at, _) -> acc ^ typeId at ^ "f")
         "" (argsToList args)) ^ (if va then "V" else "v") ^ attrsId a
  | _ -> E.s (E.bug "typeId")

and ikId = function
    IChar -> "C"
  | ISChar -> "c"
  | IUChar -> "b"
  | IBool  -> "B"
  | IInt -> "I"
  | IUInt -> "U"
  | IShort -> "S"
  | IUShort -> "s"
  | ILong -> "L"
  | IULong -> "l"
  | ILongLong -> "W"
  | IULongLong -> "w"

and fkId = function
    FFloat -> "O"
  | FDouble -> "D"
  | FLongDouble -> "T"

and prependLength s =
  let l = String.length s in
  if s = "" || (s >= "0" && s <= "9") then
    E.s (E.unimp "String %s starts with a digit\n" s);
  string_of_int l ^ s

and attrsId al =
  match al with
    [] -> "_"
  | _ -> "r" ^ List.fold_left (fun acc (Attr(an,_)) -> acc ^ an) "" al ^ "r"

(************ Print statistics about the graph ******************)
let addToHisto (histo: ('a, int ref) H.t) (much: int) (which: 'a) : unit =
  let r = Ccutil.findOrAdd histo which (fun _ -> ref 0) in
  r := !r + much

let getHisto (histo: ('a, int ref) H.t) (which: 'a) : int =
  try let r = H.find histo which in !r with Not_found -> 0

let sortHisto (histo: ('a, int ref) H.t) : ('a * int) list =
  let theList : ('a * int) list ref = ref [] in
  H.iter (fun k r -> theList := (k, !r) :: !theList) histo;
  List.sort (fun (_,v1) (_,v2) -> - (compare v1 v2)) !theList

let showFirst (showone: 'a -> int -> unit)
              (many: int) (lst: ('a * int) list) =
  let rec loop i = function
      (n, s) :: rest when i >= 0 && s > 0 ->
        showone n s;
        loop (i - 1) rest
    | _ -> ()
  in
  loop many lst

(*** Statistics ***)

type incompat = node * chain * node

type incompatClass =
    {
              icId: int;
      mutable icCompats: incompat list; (* A list of incompats in this class *)
      mutable icNodes: (int, node * int ref) H.t; (* A hashtable indexed by
                                  * node id; for each node also keep a count
                                  * of how many incompats it is part of *)
    }

(* Create a list of equivalence classes *)
let incompatEquivalence: (node * (node * edge) list) list ref = ref []
let nrIncompatClasses = ref 0
let nrIncompatCasts = ref 0

let reportIncompats (incompats: (int * int, incompat) H.t) =
  incompatEquivalence := [];
  nrIncompatClasses := 0;
  nrIncompatCasts := 0;
  let debugIncompat = false in
  let icLastId = ref (-1) in (* A counter for incompat classes *)
  (* Scan all incompats and construct the list of equivalence classes *)
  let nodeClass: (int, incompatClass) H.t = H.create 11 in
  let allClasses: (int, incompatClass) H.t = H.create 11 in
  H.iter (fun _ ((n1, why_n1_n2, n2) as inc) ->
    let c = chainToList why_n1_n2 in
    if debugIncompat then
      ignore (E.log "Processing incompat %d and %d\n" n1.id n2.id);
    let theReprClass =
      (* Scan first and find out the equivalence classes in which this chain
       * should go (indexed by class id). This could be empty if all nodes
       * are new. *)
      let classes: (int, incompatClass) H.t = H.create 7 in
      let markClassNode (n: node) =
        (* Omit the extreme nodes *)
        if n.id <> n1.id && n.id <> n2.id then begin
          try
            let cls = H.find nodeClass n.id in
            ignore (Ccutil.findOrAdd classes cls.icId (fun _ -> cls))
          with Not_found ->
            ()
        end
      in
      List.iter
        (fun (_, e) ->
          markClassNode e.efrom; markClassNode e.eto) c;
      let theRepr = ref None in
      (* Now we must union all the classes *)
      H.iter (fun _ cls ->
        if debugIncompat then
          ignore (E.log "  already in class %d\n" cls.icId);
        match !theRepr with
          None -> theRepr := Some cls
        | Some cls' ->
            (**** UNION ****)
            if debugIncompat then
              ignore (E.log " unioning class %d to %d\n" cls.icId cls'.icId);
            cls'.icCompats <- cls'.icCompats @ cls.icCompats;
            H.remove allClasses cls.icId;
            H.iter
              (fun nid (nd, pCount) ->
                let _, pCount' =
                  Ccutil.findOrAdd cls'.icNodes nid (fun _ -> (nd, ref 0)) in
                H.replace nodeClass nid cls';
                pCount' := !pCount' + !pCount)
              cls.icNodes)
        classes;
      (* Maybe we need to create a new class *)
      (match !theRepr with
        None ->
          incr icLastId;
          if debugIncompat then
            ignore (E.log "create a new class %d\n" !icLastId);
          let cls =
            { icId = !icLastId; icCompats = []; icNodes = H.create 5 } in
          H.add allClasses !icLastId cls;
          cls

      | Some cls -> cls)
    in
    if debugIncompat then
      ignore (E.log "Found the representative class %d\n" theReprClass.icId);
    (* Now add this chain to the class *)
    theReprClass.icCompats <- inc :: theReprClass.icCompats;
    let addIncToNode (n: node) =
      if n.id <> n1.id && n.id <> n2.id then begin
        H.replace nodeClass n.id theReprClass;
        let _, pCount =
          Ccutil.findOrAdd theReprClass.icNodes n.id (fun _ -> (n, ref 0)) in
        incr pCount
      end
    in

    List.iter (fun (_, e) -> addIncToNode e.efrom; addIncToNode e.eto) c;

    ) incompats;
  if debugIncompat then
    ignore (E.log "printing classes\n");
  (* Now we have a list of classes of incompats *)
  H.iter
    (fun _ cls ->
      (* Find the node with maximum count, and which is not Anon *)
      incr nrIncompatClasses;
      let maxNode = ref None in
      let maxCount = ref 0 in
      H.iter (fun nid (nd, pCount) ->
        if !pCount > !maxCount
           && (match nd.where with PAnon _, _ -> false | _ -> true) then begin
          maxNode := Some nd;
          maxCount := !pCount
        end) cls.icNodes;
      let reprNode =
        match !maxNode with
          None -> dummyNode
        | Some nd -> nd
      in
      (* Now for each incompat we collect the extreme nodes along with the
       * extreme edges *)
      let extremes: (int * int, node * edge) H.t = H.create 7 in
      List.iter
        (fun (n1, why_n1_n2, n2) ->
          let c = chainToList why_n1_n2 in
          if List.length c = 0 then begin
            if keepDetails() then
              ignore (E.warn "Chain for incompat %d and %d is empty"
                        n1.id n2.id)
          end else begin
            let _, e1 = List.nth c 0 in
            let _, e2 = List.nth (List.rev c) 0 in
            ignore (Ccutil.findOrAdd extremes (n1.id, e1.eid)
                      (fun _ -> (n1, e1)));
            ignore (Ccutil.findOrAdd extremes (n2.id, e2.eid)
                      (fun _ -> (n2, e2)))
          end)
        cls.icCompats;
      (* Now print them *)
      let extremesList = ref [] in
      H.iter
        (fun _ (n, e) ->
          incr nrIncompatCasts;
          extremesList := (n, e) :: !extremesList)
        extremes;
      incompatEquivalence :=
         (reprNode, !extremesList) :: !incompatEquivalence;)
    allClasses;
(*   if !nrIncompatClasses > 0 && not (keepDetails()) then begin *)
(*     ignore (E.warn "Cannot print details for the equivalence classes because you turned off the generation of the browser info") *)
(*   end *)
  ()

let printGraphStats () =
  (* Keep a histograph per kind *)
  if !isSubtype == origSubtype then
    E.s (bug "printGraphStats: isSubtype is not set\n");
  let totKind : (opointerkind, int ref) H.t = H.create 17 in
  let totalNodes = ref 0 in
  let unusedNodes = ref 0 in
  let voidStarNodes = ref 0 in
  let splitNodes = ref 0 in
  let metaPtrNodes = ref 0 in
  (* The number of bad casts *)
  let badCastsCount = ref 0 in
  let downCastCount = ref 0 in
  (* All the incompats *)
  let incompats: (int * int, node * chain * node) H.t = H.create 113 in
  (* A list of the edges involved in bad casts, and whether or not each is
   * a sequence cast.  Will be sorted and printed *)
  let badCastsList: (edge * bool) list ref = ref [] in
  (* Index the bad casts by location because one bad bad cast can be counted
   * many times (if it is in a macro).  Use a separate hashtable,
   * rather than badCastsList, for performance.  *)
  let badCastsLoc: (location, unit) H.t = H.create 113 in
  let badCastsVoid = ref 0 in
  let badCastsFPtr = ref 0 in
  (* Keep track of spread_from_edge. For each node how many other nodes have
   * WILD/spread_from_edge(n).  *)
  let spreadTo : (int, int ref) H.t = H.create 117 in
  let examine_node id n =
    incr totalNodes;
    (match unrollType n.btype with
      TVoid _ -> incr voidStarNodes
    | _ -> ());
    (* See if it is not-used. We check that it does not have ECompat, ECast
     * or ESameKind edges *)
    if n.kind = Safe then begin
      let isUsedEdge e =
        match e.ekind with
          ECast _ | ECompat _ | ESameKind _ -> true
        | _ -> false
      in
      if not (List.exists isUsedEdge n.succ ||
              List.exists isUsedEdge n.pred) then
        incr unusedNodes;
    end;
    addToHisto totKind 1 n.kind;
    if hasFlag n pkSplit then incr splitNodes;
    if isC n.kind then incr metaPtrNodes;
    if n.kind = Wild then begin
      (match n.why_kind with
        SpreadFromNode (n_near, _, _) ->
          addToHisto spreadTo 1 n_near.id
      | (BadCast e | BadSequenceCast e) ->
          if not (H.mem badCastsLoc e.eloc) then begin
            H.add badCastsLoc e.eloc ();
            if true then begin
              let isseq =
                match n.why_kind with BadSequenceCast _ -> true | _ -> false in
              badCastsList := (e, isseq)::!badCastsList;
            end;
            (match e.efrom.btype, e.eto.btype with
              TVoid _, _ -> incr badCastsVoid
            | _, TVoid _ -> incr badCastsVoid
            | TFun _, _ -> incr badCastsFPtr
            | _, TFun _ -> incr badCastsFPtr
            | _ -> ());
            begin
            if !isSubtype e.eto.btype e.efrom.btype then
              incr downCastCount;
            end
          end
      | Incompat (n1, r, n2) ->
          if not (H.mem incompats (n1.id, n2.id)) then begin
            H.add incompats (n1.id, n2.id) (n1, r, n2);
          end

      | _ -> ())
    end
  in
  H.iter examine_node idNode;
  badCastsList := List.sort
      (fun (e1, _) (e2, _) -> compareLoc e1.eloc e2.eloc)
      !badCastsList;
  List.iter
    (fun (e, isseq) ->
      incr badCastsCount;
      ignore (E.log "** %d: Bad cast %sat %a (%a *%d ->%a *%d)\n"
                !badCastsCount
                (if isseq then "(seq) " else "")
		d_loc e.eloc d_type e.efrom.btype e.efrom.id
                d_type e.eto.btype e.eto.id))
    !badCastsList;
  (* sm: prepend string 'ptrkinds:' so I can easily grep for this info *)
  ignore (E.log "ptrkinds: Graph contains %d nodes (%d are used)\n"
            !totalNodes (!totalNodes - !unusedNodes));
  (* Now subtract the unused ones *)
  totalNodes := !totalNodes - !unusedNodes;
  (try
    let rsafe = H.find totKind Safe in
    rsafe := !rsafe - !unusedNodes
  with Not_found -> ());
  let percent (n: int) : float =
    if !totalNodes = 0 then begin
      if n <> 0 then
        ignore (E.warn "Ptrnode.percent: divide by 0");
      100.0
    end else
      (float_of_int n)
         /. float_of_int (!totalNodes) *. 100.0
  in
  H.iter
    (fun k r -> ignore (E.log "ptrkinds:   %a - %d (%3.0f%%)\n"
                          d_opointerkind k !r (percent !r)))
    totKind;
  ignore (E.log "%d pointers are void*\n" !voidStarNodes);
  if keepDetails () then begin
    ignore (E.log "%d bad casts of which %d involved void* and %d involved function pointers\n"
              !badCastsCount !badCastsVoid !badCastsFPtr);
    if !badCastsCount = 0 then
      ignore (E.log "No bad casts, so no downcasts\n")
    else begin
      ignore (E.log "%d (%d%%) of the bad casts are downcasts\n"
                !downCastCount (100 * !downCastCount / !badCastsCount));
    end ;
    ignore (E.log "%d (%d%%) of the nodes are split\n"
                !splitNodes (int_of_float (percent !splitNodes)));
    ignore (E.log "%d (%d%%) of the nodes are have a metadata pointer\n"
                !metaPtrNodes (int_of_float (percent !metaPtrNodes)));
    reportIncompats incompats;
    let incompatCount = ref 0 in
    List.iter
      (fun (n, extremes) ->
         let nrExtremes = List.length extremes in
         if nrExtremes > 0 then begin
           ignore (E.log "%d incompatible types flow into node %a *%d\n"
                     nrExtremes
                     d_type n.btype n.id);
           List.iter
             (fun (n, e) ->
                incr incompatCount;
                ignore (E.log "  Type %a *%d at %a\n"
                          d_type n.btype n.id d_loc e.eloc)) extremes
         end)
      !incompatEquivalence;
    ignore (E.log "%d incompatible equivalence classes\n" !incompatCount);
  end
  else begin
    ignore (E.warn "Cannot print information about bad casts or void* equivalence classes because you turned off the generation of the browser info\n")
  end;
  H.clear totKind;
  H.clear spreadTo;
  ()

let printInferGraph (c: out_channel) =
begin
  (* Get the nodes ordered by ID *)
  let allsorted =
    Stats.time "sortgraph"
      (fun () ->
        let all : node list ref = ref [] in
        H.iter (fun id n -> all := n :: !all) idNode;
        List.sort (fun n1 n2 -> compare n1.id n2.id) !all) ()
  in
  Stats.time "printnodes"
    (List.iter (fun n -> (
      fprint c 80 (d_node () n)
        )))
    allsorted;
end

let printInfer (f: string) (file: Cil.file) =
  begin
    let c =
      try open_out f  (* Might throw an exception *)
      with e -> E.s (E.error "Cannot open infer output file %s" f)
    in
    Ccutil.tryFinally
      (fun _ ->
        dumpFile ccuredInferPrinter c f file;
        (trace "sm" (dprintf "printing pointer graph\n"));
        output_string c "#if 0\n/* Now the graph */\n";
        output_string c "/* Now the solved graph (simplesolve) */\n";
        Stats.time "printgraph" printInferGraph c;
        output_string c "/* End of solved graph*/\n#endif\n";)
      (fun _ ->
        close_out c)
      ()
  end

let initialize () =
  H.clear placeId;
  lastEdgeIdx := 0;
  lastNodeId := 0; (* We reserve the ID=0 to the dummyNode *)
  if dummyNode.id <> 0 then
    E.s (E.bug "Ptrnode:dummyNode does not have ID=0");
  H.clear idNode;
  (* And add the dummyNode in the graph *)
  H.add idNode dummyNode.id dummyNode;
  if not !useStrings && !use_wild_solver then begin
    useStrings := true;
    ignore (E.warn "You must use strings when using the WILD solver! I turned them back on!");
  end;

  ()

(************************************************************************
 **
 **
 *** BROWSER printing
 **
 ***********************************************************************)

let emitGlobals = true

(* We need a special form of typeOf to handle the & operator *)
let nodeOfExp (e: exp) : node option =
  match e with
    AddrOf (b, off) -> begin
      let startNode : node option =
        match b with
          Mem e -> nodeOfAttrlist (typeAttrs (typeOf e))
        | Var v -> nodeOfAttrlist v.vattr
      in
      let rec doOffset (start: node) (off: offset) : node option =
        match off with
          NoOffset -> Some start
        | Field (fi, off) -> begin
            match nodeOfAttrlist fi.fattr with
              None -> None
            | Some n -> doOffset n off
        end
        | Cil.Index (_, NoOffset) -> None (* !!! *)
        | Cil.Index (_, off) -> doOffset dummyNode off (* !!! *)
      in
      match startNode with
        None -> None
      | Some n -> doOffset n off
    end

  | e -> nodeOfAttrlist (typeAttrs (typeOf e))

(** First scan the graph and find out the source points that are of interest.
  * We'll need to mark them in a special way while printing the graph *)
type codeOfInterest = { loc: location;
                        src: int;
                        dest: int;
                        cKind: codeKind }
and codeKind =
    CKCast (* A cast from src -> dest *)
  | CKArith (* Arithmetic on dest. src is 0. For now we mix PosArith and
             * Arith to simplify the printer *)
  | CKString (* Reach string on dest. *)
  | CKIntCast (* Casting an integer into a pointer *)
  | CKVar of string (* A variable definition *)
  | CKType of string (* A type definition *)
  | CKComp of string (* A compinfo definition *)

let d_codeKind () = function
    CKCast -> text "cast"
  | CKArith -> text "arith"
  | CKString -> text "reach str"
  | CKIntCast -> text "intcast"
  | CKVar n -> text ("var(" ^ n ^ ")")
  | CKType n -> text ("type(" ^ n ^ ")")
  | CKComp n -> text ("comp(" ^ n ^ ")")

let d_codeOfInterest () (ci: codeOfInterest) =
  dprintf "k=%a,d=%d,s=%d @@ %a"
    d_codeKind ci.cKind ci.dest ci.src d_loc ci.loc

(* Remember here the interesting features. For each one keep a place where
 * we'll store the fileIndex where the feature is defined, thd identifier of
 * the interesting feature, and its forward reference identifier if it was
 * referenced before being defined. *)
let debugInteresting = false
let interestingEdges: (int, unit) H.t = H.create 1111
let interestingFeatures:
    (codeOfInterest, (int * int * int) ref) H.t = H.create 11111

(* We remember in the interesting features both declarations and definitions
 * of variables. We remember here the defined variables *)
let definedVariables: (string, unit) H.t = H.create 112

(* Remember here the bad casts *)
let nrBadCasts: int ref = ref 0
(* For each bad cast (indexed by eid) we keep whether this is a Sequence
 * cast. *)
let badCasts: (int, bool) H.t = H.create 37

(* And the imcompatible classes *)
let incompats: (int * int, unit) H.t = H.create 37

let addInterestingFeature (ci: codeOfInterest) =
  if debugInteresting then
    ignore (E.log "addInteresting(%a)\n" d_codeOfInterest ci);
  H.replace interestingFeatures ci (ref (-1, -1, -1))

let edgeToFeature (e: edge) : codeOfInterest =
  match e.ekind with
    ECast EEK_extends -> (* This is the location of the pragma *)
      { loc = e.eloc; dest = -1; src = -1; cKind = CKCast }
  | _ ->
      { loc = e.eloc; dest = e.eto.id; src = e.efrom.id; cKind = CKCast; }

let varToFeature (v: varinfo) : codeOfInterest =
  { loc = locUnknown; dest = -1; src = -1;
    cKind = CKVar v.vname }

let typenameToFeature (ti: typeinfo) : codeOfInterest =
  { loc = locUnknown; dest = -1; src = -1;
    cKind = CKType ti.tname }

let compToFeature (ci: compinfo) : codeOfInterest =
  { loc = locUnknown; dest = -1; src = -1;
    cKind = CKComp ci.cname }

let addInterestingEdge (e: edge) =
  if debugInteresting then
    ignore (E.log "addInterestingEdge(%d->%d)\n" e.efrom.id e.eto.id);
  if not (H.mem interestingEdges e.eid) then begin (* Already added *)
    H.add interestingEdges e.eid ();
    (* Construct the key *)
    let key = edgeToFeature e in
    H.add interestingFeatures key (ref (-1, -1, -1))
  end

(* Make a scan of the graph to collect the interesting features in the code
 * that will be refered to from the graph explanations. We will fill in later
 * the fileIdx and feature idx *)
let collectInterestingFeatures (f: file) =
  let debugCollect = false in
  if !E.verboseFlag then
    ignore (E.log "browser: find interesting source locations\n");
  H.clear interestingFeatures;
  H.clear definedVariables;
  let nodeCount = ref 0 in
  H.iter (fun _ nd -> (* Scan all nodes *)
    (* This is sometimes very slow. Print some information *)
    if debugCollect &&
      (!nodeCount mod 1000 = 0 (* || !nodeCount >= 1970 *)) then
      ignore (E.log "collectInteresting: %d\n" !nodeCount);
    (* Collect the interesting casts from a chain. While we are at it, we
     * return a compressed chain.  *)
    let rec scanChain (r: chain) : unit =
      if debugCollect && (!nodeCount = 1976) then
        (emitGraphDetailLevel := 3;
         ignore (E.log " scanChain: ");
         dumpChain r);
      let l = chainToList r in
      List.iter (fun (_, e) -> addInterestingEdge e) l
    in
    (* Check te why_kind *)
    (match nd.why_kind with
    | BadCast e | BadSequenceCast e ->
        if not (H.mem badCasts e.eid) then begin
          let isSeq =
            match nd.why_kind with BadSequenceCast _ -> true | _ -> false
          in
          H.add badCasts e.eid isSeq;

          if not (isECast e) then
            ignore (warnLoc e.eloc
                      "found bad cast on a non-Ecast edge (%a) %d-%d\n"
                      d_ekind e.ekind e.efrom.id e.eto.id);

          incr nrBadCasts
        end;
        addInterestingEdge e

    | Incompat (n1, why_n1_n2, n2) ->
        if not (H.mem incompats (n1.id, n2.id)) then begin
          H.add incompats (n1.id, n2.id) ();
          scanChain why_n1_n2
        end

    | SpreadFromNode (n1, chain, n2) -> scanChain chain

    | _ -> ());
    (* Take a look at the flags *)
    (* Scan a flag *)
    let scanFlag (nd: node) (fidx: int) (ck: codeKind) =
      match nd.flags.(fidx) with
        Some (ProgramSyntax l) ->
          addInterestingFeature { loc = l; dest = nd.id; src = 0; cKind = ck }
      | Some (FlagSpreadFromNode(n1, chain, n2)) ->
          scanChain chain

      | _ -> ()
    in
    scanFlag nd pkArith CKArith;
    scanFlag nd pkPosArith CKArith;
    scanFlag nd pkString CKString;
    scanFlag nd pkIntCast CKIntCast;
    scanFlag nd pkRtti CKCast;

    incr nodeCount;
    ) idNode;
  (* Now scan the file for the globals. They are interesting features. *)
  iterGlobals
    f
    (function
        GVar (vi, _, l) ->
          H.add definedVariables vi.vname ();
          addInterestingFeature (varToFeature vi)

      | GVarDecl (vi, l) ->
          addInterestingFeature (varToFeature vi)

      | GType (ti, l) ->   addInterestingFeature (typenameToFeature ti)
      | GCompTag (ci, l) -> addInterestingFeature (compToFeature ci)

      | GFun (f, l) ->
          H.add definedVariables f.svar.vname ();
          addInterestingFeature (varToFeature f.svar)

      | _ -> ())

(* Keep some identifiers for the interesting features *)
let lastInterestingFeatureId = ref (-1)

let inferFrame = "\'codeseg\'"
let graphFrame = "\'bottom\'"

let useNodeImages = true

(* We break the output file into several smaller files. We store here the
 * current file index *)
let currentOutIdx = ref (-1)

(* Assign a feature id to an interesting feature. Call this while you are
 * outputting files (it uses currentOutIdx). *)
let assignFeatureId (pIdx: (int * int * int) ref) : int option =
  let fileIdx, featureIdx, forwardIdx = !pIdx in
  if featureIdx >= 0 then begin
    if debugInteresting then
      ignore (E.log ": already done(%d)\n" featureIdx);
    None  (* Already taken care of *)
  end else begin
    incr lastInterestingFeatureId;
    pIdx := (!currentOutIdx, !lastInterestingFeatureId, forwardIdx);
    if debugInteresting then
      ignore (E.log ": assigned code %d\n" !lastInterestingFeatureId);
    Some !lastInterestingFeatureId
  end

(* Check if a feature is interesting. Return its index if so. At this point
 * we also set the fileIdx for the feature. *)
let checkInterestingFeature (ci: codeOfInterest) : int option =
  if debugInteresting then
    ignore (E.log "checkInteresting(%a)" d_codeOfInterest ci);
  try
    let pIdx = H.find interestingFeatures ci in
    assignFeatureId pIdx
  with Not_found -> begin
    if debugInteresting then
      ignore (E.log ": not found\n");
    None
  end

let markInterestingFeature (ci: codeOfInterest) (base: doc) : doc =
  match checkInterestingFeature ci with
    None -> base (* Not interesting *)
  | Some featureIdx -> (* Interesting. Put an image there *)
      (if useNodeImages then
        mark ++ text "<img name=\"if" ++ num featureIdx
          ++ text ("\" src=pixel.gif width=10 height = 10> ") ++ unmark
      else nil) ++
        mark ++ text "<a name=\"f" ++ num featureIdx ++ text "\">" ++
        unmark ++
        base ++ mark ++ text "</a>" ++ unmark

let markInterestingCast (efrom: exp) (tto: typ) : doc =
  match nodeOfExp efrom, nodeOfType tto with
    Some nfrom, Some nto when nfrom.id <> nto.id ->
      if debugInteresting then
        ignore (E.log "markInterestingCast %d -> %d at %a\n"
                  nfrom.id nto.id d_loc !currentLoc);
      let res =
        markInterestingFeature { loc = !currentLoc; dest = nto.id;
                                 src = nfrom.id; cKind = CKCast } nil
      in
      if debugInteresting then
        ignore (E.log "   res=%a\n" insert res);
      res

  | None, Some nto -> (* Maybe it is an int cast *)
      markInterestingFeature { loc = !currentLoc; dest = nto.id;
                               src = 0; cKind = CKIntCast } nil
  | _, _ -> nil (* No nodes! *)

let markInterestingCastType (tfrom: typ) (tto: typ) : doc =
  match nodeOfType tfrom, nodeOfType tto with
    Some nfrom, Some nto when nfrom.id <> nto.id ->
      markInterestingFeature { loc = !currentLoc; dest = nto.id;
                               src = nfrom.id; cKind = CKCast } nil
  | _, _ -> nil (* No nodes! *)

let markInterestingIndex (e: exp) : doc =
  match nodeOfExp e with
    Some n ->
      markInterestingFeature { loc = !currentLoc; dest = n.id;
                               src = 0; cKind = CKArith } nil
  | _ -> nil (* No nodes! *)

let markInterestingBinOp (e1: exp) (b: binop) : doc =
  match b with
    PlusPI | MinusPI | IndexPI -> begin
      match nodeOfExp e1 with
        Some ndst ->
          markInterestingFeature { loc = !currentLoc; dest = ndst.id;
                                   src = 0; cKind = CKArith } nil
      | _ -> nil (* Not a node !! *)
    end
  | _ -> nil (* Not a pointer arithmetic *)

let markInterestingPragma (pn: string) (l: location) : doc =
  match pn with
    "ccured_extends" ->
      markInterestingFeature { loc = !currentLoc;
                               dest = -1; src = -1;
                               cKind = CKCast } nil
  | _ -> nil

let colorOfKind (k: opointerkind) =
  (* The interpretations of these styles is defined in lib/styles.css *)
  let color =
    match k with
      Wild -> Some "wild"
    | Seq | SeqN -> Some "seq"
    | FSeq | FSeqN -> Some "fseq"
    | Safe -> Some "safe"
    | Rtti -> Some "rtti"
    | Scalar -> None
    | _ -> Some "other"
  in
  match color with
    None -> ""
  | Some c -> "class=\"" ^ c ^ "\""

(* For each node we remember in which file we put its definition *)
let fileOfNode: (int, int) H.t = H.create 111113

let declareNode (n: node) (color: string) (nodestuff: doc) : doc =
  (* Remember the counter for this node *)
  if not (H.mem fileOfNode n.id) then
    H.add fileOfNode n.id !currentOutIdx;

  (if useNodeImages then
    (* Emit an img without a source to keep the source small *)
    markup (text "<img name=\"in" ++ num n.id
      ++ text ("\" src=pixel.gif width=10 height = 10> "))
  else
    nil)

    ++ markup (text "<a name=\"n" ++ num n.id++ text "\" "
                 ++ text color
                 ++ text " href=\"javascript: sn(" ++ num n.id
                 ++ text ")\">")
    ++ nodestuff
    ++ markup (text "<sub>"
                 ++ num n.id
                 ++ text "</sub></a>")

(* keep track of forward references to feature *)
let lastForwardFeatureId = ref 0

let showFeatureCode (code: codeOfInterest) (what: string) : doc =
  try
    let pIdx = H.find interestingFeatures code in
    let fileIdx, featureIdx, forwardId = !pIdx in
    if fileIdx < 0 then begin
      (* This is an interesting feature but we are showing a forward
       * reference *)
      let forwardId =
        if forwardId >= 0 then (* We have already assigned a forward reference
                                * to this feature *)
          forwardId
        else begin
          incr lastForwardFeatureId;
          pIdx := (-1, -1, !lastForwardFeatureId);
          !lastForwardFeatureId
        end
      in
      markup (text "<a href=\"javascript: sff(" ++
                num forwardId ++ text ")\">")
        ++ text what
        ++ markup (text "</a> ")
    end else
      markup (text "<a href=\"javascript: sf(" ++ num fileIdx
                ++ text ", 'if"
                ++ num featureIdx ++ text "')\">")
        ++ text what
        ++ markup (text "</a> ")
  with Not_found -> (* Not an interesting feature *)
    text what

let showVarname (vi: varinfo) =
  showFeatureCode (varToFeature vi) vi.vname

let showTypename (ti: typeinfo) =
  showFeatureCode (typenameToFeature ti) ti.tname

let showCompname (ci: compinfo) =
  let su = if ci.cstruct then "struct" else "union" in
  let name = su ^ " " ^ ci.cname ^ " " in
  showFeatureCode (compToFeature ci) name

    (* This is the main function for printing of attributes *)
type printBrowserWhat =
    PAVar (* variable attributes *)
  | PAPtr (* pointer type attributes *)
  | PAFun (* function type attributes *)
  | PAArray (* array type attributes *)

let printBrowserAttributes (what: printBrowserWhat) (a: attributes) : doc =
  let n =
    (* Search for the node for this pointer *)
    try
      match filterAttributes "_ptrnode" a with
        [Attr(_, [AInt n])] -> H.find idNode n
      | _ -> raise Not_found
    with Not_found -> dummyNode
  in
  if n == dummyNode then (* No node attribute *)
    (* Print the attributes like the inferencer *)
    (match what with
      PAPtr -> text " * "
    | PAArray  -> text "]"
    | _ -> nil)
      ++ ccuredInferPrinter#pAttrs () a
  else begin (* We found a node *)
    let color = colorOfKind n.kind in
    (* We do not show the Safe nodes, except if they point to non-SAFE nodes *)
    (* Prevent recursion when we follow EPointsTo *)
    let seen: (int, unit) H.t = H.create 15 in
    let rec mustShowNode (n: node) =
      if H.mem seen n.id then
        false
      else begin
        H.add seen n.id ();
        (n.kind <> Safe) ||
        (* If it is SAFE, show it if its base type is void *)
        (match n.btype with TVoid _ -> true | _ -> false) ||
        (* Also show it if it points to nodes that must be shown *)
        (List.exists (fun e -> e.ekind = EPointsTo &&
                               mustShowNode e.eto) n.succ)
      end
    in
    if not (mustShowNode n) then
      (* We drop other attributes as well !!! *)
      match what with
        PAPtr -> text " * "
      | PAArray -> text "]"
      | _ -> nil
    else
      match what with
        PAPtr -> declareNode n color (text "*")
      | PAArray -> declareNode n color (text "]")
      | PAVar -> declareNode n color (text "&")
      | _ -> declareNode n color nil
  end

(* Parentheses level. An expression "a op b" is printed parenthesized if its
 * parentheses level is >= that that of its context. Identifiers have the
 * lowest level and weakly binding operators (e.g. |) have the largest level
 *)
let derefStarLevel = 20
let indexLevel = 20
let arrowLevel = 20
let addrOfLevel = 30
let additiveLevel = 60
let comparativeLevel = 70
let bitwiseLevel = 75
let getParenthLevel = function
  | Question(_,_,_,_)       -> 85
  | BinOp((LAnd|LOr),_,_,_) -> 80
                                        (* Bit operations. *)
  | BinOp((BOr|BXor|BAnd),_,_,_) -> bitwiseLevel (* 75 *)

                                        (* Comparisons *)
  | BinOp((Eq|Ne|Gt|Lt|Ge|Le),_,_,_) ->
      comparativeLevel (* 70 *)
                                        (* Additive. Shifts can have higher
                                         * level but I want parentheses
                                         * around them *)
  | BinOp((MinusA|MinusPP|MinusPI|PlusA|
           PlusPI|IndexPI|Shiftlt|Shiftrt),_,_,_)
    -> additiveLevel (* 60 *)

                                        (* Multiplicative *)
  | BinOp((Div|Mod|Mult),_,_,_) -> 40

                                        (* Unary *)
  | CastE(_,_) -> 30
  | AddrOf(_) -> 30
  | AddrOfLabel(_) -> 30
  | StartOf(_) -> 30
  | UnOp((Neg|BNot|LNot),_,_) -> 30

                                        (* Lvals *)
  | Lval(Mem _ , _) -> 20
  | Lval(Var _, (Field _|Cil.Index _)) -> 20
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> 20
  | AlignOf _ | AlignOfE _ -> 20

  | Lval(Var _, NoOffset) -> 0        (* Plain variables *)
  | Const _ -> 0                        (* Constants *)

let invalidStmt = mkStmt (Instr [])

let currentFunctionReturnType = ref voidType

(* Now define a special way of printing the infer file *)
class ccuredBrowserPrinterClass = object (self)
  inherit ccuredInferPrinterClass as super

  method pType (nameOpt: doc option) () (t: typ) =
    let name = match nameOpt with None -> nil | Some d -> d in
    match t with
      TPtr(bt, a) ->
        (* Search for the node for this pointer *)
        (* let n, color = processAttributes a in *)
        (* Parenthesize the ( * attr name) if a pointer to a function or an
        * array *)
        let paren = match bt with TFun _ | TArray _ -> true | _ -> false in
        let name' = printBrowserAttributes PAPtr a ++ name in
        let name'' = if paren then text "(" ++ name' ++ text ")" else name' in
        self#pType
          (Some name'')
          ()
          bt

    | TArray (elemt, lo, a) ->
        let brattr = printBrowserAttributes PAArray a in
        self#pType
          (Some (name
                   ++ text "["
                   ++ (match lo with None -> nil | Some e -> self#pExp () e)
                   ++ brattr))
          ()
          elemt

    | TFun (restyp, args, isvararg, a) ->
        let name' =
          if a == [] then name else
          if nameOpt == None then printBrowserAttributes PAFun a else
          text "(" ++ printBrowserAttributes PAFun a ++ name ++ text ")"
        in
        self#pType
          (Some
             (name'
                ++ text "("
                ++ (align
                      ++
                      (if args = Some [] && isvararg then
                        text "..."
                      else
                        (if args = None then nil
                        else if args = Some [] then text "void"
                        else
                          let pArg (aname, atype, aattr) =
                            (self#pType (Some (text aname)) () atype)
                              ++ text "  "
                              ++ printBrowserAttributes PAVar aattr
                          in
                          (docList ~sep:(chr ',' ++ break) pArg) ()
                            (argsToList args))
                          ++ (if isvararg then break ++ text ", ..." else nil))
                      ++ unalign)
                ++ text ")"))
          ()
          restyp

    | TNamed (t, a) ->
        showTypename t ++ self#pAttrs () a ++ text " " ++ name

    | TComp (comp, a) -> (* A reference to a struct *)
        showCompname comp
          ++ self#pAttrs () a
          ++ name

          (* Hopefully the remaining types cannot have node attributes *)
    | t -> super#pType nameOpt () t

  (* Variable declaration *)
  method pVDecl () (v:varinfo) =
      d_storage () v.vstorage
      ++ (self#pType (Some (text v.vname)) () v.vtype)
      ++ text " "
      ++ printBrowserAttributes PAVar v.vattr

  method pFieldDecl () fi =
    (self#pType
       (Some (text (if fi.fname = missingFieldName then "" else fi.fname)))
       ()
       fi.ftype)
      ++ text " "
      ++ (match fi.fbitfield with None -> nil
      | Some i -> text ": " ++ num i ++ text " ")
      ++ printBrowserAttributes PAVar fi.fattr
      ++ text ";"

  method private pLvalPrec (contextprec: int) () lv =
    if getParenthLevel (Lval(lv)) >= contextprec then
      text "(" ++ self#pLval () lv ++ text ")"
    else
      self#pLval () lv

  (** L-VALUES **)
  method pLval () (lv:lval) =  (* lval (base is 1st field)  *)
    match lv with
      Var vi, o ->
        self#pOffsetBrowser (Var vi, NoOffset) (self#pVar vi) o
    | Mem e, Field(fi, o) ->
        self#pOffsetBrowser
          (Mem e, Field(fi, NoOffset))
          ((self#pExpPrec arrowLevel () e) ++ text ("->" ^ fi.fname)) o
    | Mem e, o ->
        self#pOffsetBrowser
          (Mem e, NoOffset)
          (text "(*" ++ self#pExpPrec derefStarLevel () e ++ text ")") o

  (** Like pOffest but carries with it the base lval *)
  method private pOffsetBrowser (baselv: lval) (base: doc) = function
    | NoOffset -> base
    | Field (fi, o) ->
        self#pOffsetBrowser
          (addOffsetLval (Field(fi, NoOffset)) baselv)
          (base ++ text "." ++ text fi.fname) o
    | Cil.Index (e, o) ->
        self#pOffsetBrowser
          (addOffsetLval (Cil.Index(e, NoOffset)) baselv)
          (base ++ markInterestingIndex (Lval baselv) ++
             text "[" ++ self#pExp () e ++ text "]") o

  method pVar (v: varinfo) = showVarname v

  (*** EXPRESSIONS ***)
  method pExp () (e: exp) : doc =
    let level = getParenthLevel e in
    match e with
      Const(c) -> d_const () c
    | Lval(l) -> self#pLval () l
    | Question(p,e1,e2,_) ->
         self#pExpPrec level () p
         ++ text " ? "
         ++ self#pExpPrec level () e1
         ++ text " : "
         ++ self#pExpPrec level () e2
    | UnOp(u,e1,_) ->
        let d_unop () u =
          match u with
            Neg -> text "-"
          | BNot -> text "~"
          | LNot -> text "!"
        in
        (d_unop () u) ++ chr ' ' ++ (self#pExpPrec level () e1)

    | BinOp(b,e1,e2,_) ->
        align
          ++ (self#pExpPrec level () e1)
          ++ chr ' '
          ++ markInterestingBinOp e1 b
          ++ d_binop () b
          ++ chr ' '
          ++ (self#pExpPrec level () e2)
          ++ unalign

    | CastE(t,e) ->
        text "("
          ++ markInterestingCast e t
          ++ self#pType None () t
          ++ text ")"
          ++ self#pExpPrec level () e

    | SizeOf (t) ->
        text "sizeof(" ++ self#pType None () t ++ chr ')'
    | SizeOfE (e) ->
        text "sizeof(" ++ self#pExp () e ++ chr ')'
    | SizeOfStr (s) ->
        text "sizeof(" ++ d_const () (CStr s) ++ chr ')'
    | AlignOf (t) ->
        text "__alignof__(" ++ self#pType None () t ++ chr ')'
    | AlignOfE (e) ->
        text "__alignof__(" ++ self#pExp () e ++ chr ')'
    | AddrOf(lv) ->
        text "& " ++ (self#pLvalPrec addrOfLevel () lv)
    | AddrOfLabel(s) ->
        text "&& (FIXME:AddrOfLabel)"
    | StartOf(lv) -> self#pLval () lv

  method private pExpPrec (contextprec: int) () (e: exp) =
    let thisLevel = getParenthLevel e in
    let needParens =
      if thisLevel >= contextprec then
	true
      else if contextprec == bitwiseLevel then
        (* quiet down some GCC warnings *)
	thisLevel == additiveLevel || thisLevel == comparativeLevel
      else
	false
    in
    if needParens then
      chr '(' ++ self#pExp () e ++ chr ')'
    else
      self#pExp () e

  (** What terminator to print after an instruction. sometimes we want to
   * print sequences of instructions separated by comma *)
  val mutable printInstrTerminator = ";"

  (*** INSTRUCTIONS ****)
  method pInstr () (i:instr) =       (* imperative instruction *)
    match i with
    | Set(lv,e,l) -> begin
        currentLoc := l;
        (* Be nice to some special cases *)
        match e with
          BinOp(((PlusA|PlusPI|IndexPI) as b),
                Lval(lv'),Const(CInt64(one,_,_)),_)
            when lv == lv' && one = Int64.one ->
              self#pLineDirective l
                ++ self#pLval () lv
                ++ markInterestingBinOp (Lval lv) b
                ++ text (" ++" ^ printInstrTerminator)

        | BinOp(((MinusA|MinusPI) as b),Lval(lv'),
                Const(CInt64(one,_,_)), _) when lv == lv' && one = Int64.one ->
                  self#pLineDirective l
                    ++ self#pLval () lv
                    ++ markInterestingBinOp (Lval lv) b
                    ++ text (" --" ^ printInstrTerminator)

        | BinOp((PlusA|PlusPI|IndexPI|MinusA|MinusPP|MinusPI|BAnd|BOr|BXor|
          Mult|Div|Mod|Shiftlt|Shiftrt) as bop,
                Lval(lv'),e,_) when lv == lv' ->
                  self#pLineDirective l
                    ++ self#pLval () lv
                    ++ text " "
                    ++ markInterestingBinOp (Lval lv) bop
                    ++ d_binop () bop ++ text "= " (* += and the such *)
                    ++ self#pExp () e
                    ++ text printInstrTerminator

        | _ ->
            self#pLineDirective l
              ++ self#pLval () lv
              ++ markInterestingCast e (typeOfLval lv)
              ++ text " = "
              ++ self#pExp () e
              ++ text printInstrTerminator

    end
    | Call(result, Lval(Var vi, NoOffset), [dest; SizeOf t], l)
        when vi.vname = "__builtin_va_arg" ->
          currentLoc := l;
          self#pLineDirective l
	    ++ (match result with
	      None -> nil
	    | Some lv ->
		self#pLval () lv ++ text " = ")

            (* Now the function name *)
            ++ text "__builtin_va_arg"
            ++ text "(" ++ (align
                              (* Now the arguments *)
                              ++ self#pExp () dest
                              ++ chr ',' ++ break
                              ++ self#pType None () t
                              ++ unalign)
            ++ text (")" ^ printInstrTerminator)

    | Call(dest,e,args,l) ->
        currentLoc := l;
        (* Get the function return type *)
        let (rt, argTypes, _, _) = splitFunctionType (typeOf e) in
        let pArgTypes = ref (argsToList argTypes) in
        let doOneArg (arg: exp) =
          match !pArgTypes with
            (_, at, _) :: rest ->
              pArgTypes := rest;
              markInterestingCast arg at
                ++ self#pExp () arg
          | _ -> (* More arguments than we have types *)
              self#pExp () arg
        in
        self#pLineDirective l
          ++ (match dest with
            None -> nil
          | Some lv ->
              self#pLval () lv
                ++ text " = " ++
                (* Maybe we need to print a cast *)
                (let destt = typeOfLval lv in
                if typeSig rt <> typeSig destt then
                  text "(" ++
                    markInterestingCastType rt destt ++
                    self#pType None () destt ++ text ")"
                else nil))

          (* Now the function name *)
          ++ (let ed = self#pExp () e in
              match e with
                Lval(Var _, _) -> ed
              | _ -> text "(" ++ ed ++ text ")")
          ++ text "(" ++
          (align
             (* Now the arguments *)
             ++ (docList ~sep:(chr ',' ++ break) doOneArg) () args
             ++ unalign)
          ++ text (")" ^ printInstrTerminator)

    | Asm(attrs, tmpls, outs, ins, clobs, l) ->
        currentLoc := l;
        super#pInstr () i

  (**** STATEMENTS ****)
  method pStmt () (s:stmt) =        (* control-flow statement *)
    self#pStmtNext invalidStmt () s

  method dStmt (out: out_channel) (ind: int) (s:stmt) : unit =
    fprint out 80 (indent ind (self#pStmt () s))

  method private pStmtNext (next: stmt) () (s: stmt) =
    (* print the labels *)
    ((docList ~sep:line (fun l -> self#pLabel () l)) () s.labels)
      (* print the statement itself. If the labels are non-empty and the
      * statement is empty, print a semicolon  *)
      ++
      (if s.skind = Instr [] && s.labels <> [] then
        text ";"
      else
        (if s.labels <> [] then line else nil)
          ++ self#pStmtKind next () s.skind)

  method private pLabel () = function
      Label (s, _, true) -> text (s ^ ": ")
    | Label (s, _, false) -> text (s ^ ": /* CIL Label */ ")
    | Case (e, _) -> text "case " ++ self#pExp () e ++ text ": "
    | CaseRange (e1, e2, _) ->
      text "case " ++ self#pExp () e1 ++ text " ... " ++ self#pExp () e2 ++ text ": "
    | Cil.Default _ -> text "default: "

  method private pBlock () (blk: block) =
    let rec dofirst () = function
        [] -> nil
      | [x] -> self#pStmtNext invalidStmt () x
      | x :: rest -> dorest nil x rest
    and dorest acc prev = function
        [] -> acc ++ (self#pStmtNext invalidStmt () prev)
      | x :: rest ->
          dorest (acc ++ (self#pStmtNext x () prev) ++ line)
            x rest
    in
    (* Let the host of the block decide on the alignment. The d_block will
     * pop the alignment as well  *)
    text "{"
      ++ line
      ++ (dofirst () blk.bstmts)
      ++ unalign ++ line ++ text "}"

  method private pStmtKind (next: stmt) () = function
      Return(None, l) ->
        currentLoc := l;
        self#pLineDirective l
          ++ text "return;"

    | Return(Some e, l) ->
        currentLoc := l;
        self#pLineDirective l
          ++ markInterestingCast e !currentFunctionReturnType
          ++ text "return ("
          ++ self#pExp () e
          ++ text ");"

    | Goto (sref, l) -> begin
        currentLoc := l;
        (* Grab one of the labels *)
        let rec pickLabel = function
            [] -> None
          | Label (l, _, _) :: _ -> Some l
          | _ :: rest -> pickLabel rest
        in
        match pickLabel !sref.labels with
          Some l -> text ("goto " ^ l ^ ";")
        | None ->
            ignore (error "Cannot find label for target of goto\n");
            text "goto __invalid_label;"
    end

    | ComputedGoto (e, l) -> begin
        currentLoc := l;
        self#pLineDirective l
        ++ text "goto "
        ++ self#pExp () e
        ++ text ";"
    end

    | Break l ->
        currentLoc := l;
        self#pLineDirective l
          ++ text "break;"

    | Continue l ->
        currentLoc := l;
        self#pLineDirective l
          ++ text "continue;"

    | Instr il ->
        align
          ++ (docList ~sep:line (fun i -> self#pInstr () i) () il)
          ++ unalign

    | If(be,t,{bstmts=[];battrs=[]},l) ->
        currentLoc := l;
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () be
                ++ text ") "
                ++ self#pBlock () t)

    | If(be,t,{bstmts=[{skind=Goto(gref,_);labels=[]}];
                battrs=[]},l)
     when !gref == next ->
        currentLoc := l;
       self#pLineDirective l
         ++ text "if"
         ++ (align
               ++ text " ("
               ++ self#pExp () be
               ++ text ") "
               ++ self#pBlock () t)

    | If(be,{bstmts=[];battrs=[]},e,l) ->
        currentLoc := l;
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)

    | If(be,{bstmts=[{skind=Goto(gref,_);labels=[]}];
           battrs=[]},e,l)
      when !gref == next ->
        currentLoc := l;
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)

    | If(be,t,e,l) ->
        currentLoc := l;
        self#pLineDirective l
          ++ (align
                ++ text "if"
                ++ (align
                      ++ text " ("
                      ++ self#pExp () be
                      ++ text ") "
                      ++ self#pBlock () t)
                ++ text " "   (* sm: indent next code 2 spaces (was 4) *)
                ++ (align
                      ++ text "else "
                      ++ self#pBlock () e)
                ++ unalign)

    | Switch(e,b,_,l) ->
        currentLoc := l;
        self#pLineDirective l
          ++ (align
                ++ text "switch ("
                ++ self#pExp () e
                ++ text ") "
                ++ self#pBlock () b)
    | Loop(b, l, _, _) -> begin
        currentLoc := l;
        (* Maybe the first thing is a conditional. Turn it into a WHILE *)
        try
          let term, bodystmts =
            let rec skipEmpty = function
                [] -> []
              | {skind=Instr [];labels=[]} :: rest -> skipEmpty rest
              | x -> x
            in
            match skipEmpty b.bstmts with
              {skind=If(e,tb,fb,_)} :: rest -> begin
                match skipEmpty tb.bstmts, skipEmpty fb.bstmts with
                  [], {skind=Break _} :: _  -> e, rest
                | {skind=Break _} :: _, [] -> UnOp(LNot, e, intType), rest
                | _ -> raise Not_found
              end
            | _ -> raise Not_found
          in
          self#pLineDirective l
            ++ text "wh"
            ++ (align
                  ++ text "ile ("
                  ++ self#pExp () term
                  ++ text ") "
                  ++ self#pBlock () {bstmts=bodystmts; battrs=b.battrs})

        with Not_found ->
          self#pLineDirective l
            ++ text "wh"
            ++ (align
                  ++ text "ile (1) "
                  ++ self#pBlock () b)
    end
    | Block b -> align ++ self#pBlock () b

    | TryFinally (b, h, l) ->
        self#pLineDirective l
          ++ text "__try "
          ++ align
          ++ self#pBlock () b
          ++ text " __fin" ++ align ++ text "ally "
          ++ self#pBlock () h

    | TryExcept (b, (il, e), h, l) ->
        self#pLineDirective l
          ++ text "__try "
          ++ align
          ++ self#pBlock () b
          ++ text " __e" ++ align ++ text "xcept(" ++ line
          ++ align
          (* Print the instructions but with a comma at the end, instead of
           * semicolon *)
          ++ (printInstrTerminator <- ",";
              let res =
                (docList ~sep:line (self#pInstr ())
                   () il)
              in
              printInstrTerminator <- ";";
              res)
          ++ self#pExp () e
          ++ text ") " ++ unalign
          ++ self#pBlock () h

   method dGlobal (out: out_channel) (g: global) : unit =
     (* For all except functions and variable with initializers, use the
      * pGlobal *)
     match g with
       GFun (fdec, l) ->
         currentLoc := l;
         let (rt, _, _, _) = splitFunctionType fdec.svar.vtype in
         currentFunctionReturnType := rt;
         (* If the function has attributes then print a prototype because
          * GCC cannot accept function attributes in a definition *)
         let oldattr = fdec.svar.vattr in
         let proto =
           if oldattr <> [] then
             (self#pLineDirective l) ++ (self#pVDecl () fdec.svar)
               ++ chr ';' ++ line
           else nil in
         fprint out 80 (proto ++ (self#pLineDirective  ~forcefile:true l));
         (* Temporarily remove the function attributes *)
         fdec.svar.vattr <- [];
         fprint out 80 (markInterestingFeature (varToFeature fdec.svar) nil);
         fprint out 80 (self#pFunDecl () fdec);
         fdec.svar.vattr <- oldattr;
         output_string out "\n";

     | GVar (vi, io, l) ->
         currentLoc := l;
         fprint out 80
           (self#pLineDirective  ~forcefile:true l
              ++ markInterestingFeature (varToFeature vi) nil
              ++ self#pVDecl () vi
              ++ (match io.init with
                   Some i ->
                     text " = "
                       ++ (let islong =
                             match i with
                               CompoundInit (_, il)
                                 when List.length il >= 8 -> true
                             | _ -> false
                           in
                           if islong then
                             line ++ self#pLineDirective l ++ text "  "
                           else nil)
              | _ -> nil));
         (match io.init with
           Some i -> self#dInit out 3 i
         | _ -> ());
         output_string out ";\n"

     | GVarDecl (vi, l) when not (H.mem definedVariables vi.vname) ->
         currentLoc := l;
         (* Mark the variable as defined now *)
         H.add definedVariables vi.vname ();
         fprint out 80
           (self#pLineDirective l
              ++ markInterestingFeature (varToFeature vi) nil
              ++ self#pVDecl () vi
              ++ text ";\n")

     | GPragma(Attr(pn, _), l) as g ->
         (* See if this is special *)
         let p = markInterestingPragma pn l in
         if hasPrefix "cil" pn || hasPrefix "ccured" pn then
           if !printVerboseOutput || p != nil then
             fprint out 80 (p ++  self#pGlobal () g)
           else
             ()
         else
           super#dGlobal out g


     | GType (typ, l) ->
        fprint out 80
           (self#pLineDirective  ~forcefile:true l
              ++ markInterestingFeature (typenameToFeature typ) nil
              ++ text "typedef "
              ++ (self#pType (Some (text typ.tname)) () typ.ttype)
              ++ text ";\n")

     | GCompTag (comp, l) -> (* This is a definition of a tag *)
         let n = comp.cname in
         let su, su1, su2 =
           if comp.cstruct then "struct", "str", "uct"
           else "union",  "uni", "on"
         in
         fprint out 80
           (self#pLineDirective  ~forcefile:true l
              ++ text su1 ++ (align ++ text su2 ++ chr ' '
                                ++ markInterestingFeature (compToFeature comp)
                                   nil
                                ++ text n
                                ++ text " {" ++ line
                                ++ ((docList ~sep:line (self#pFieldDecl ())) ()
                                      comp.cfields)
                                ++ unalign)
              ++ line ++ text "}" ++
              (self#pAttrs () comp.cattr) ++ text ";\n")

     | g -> fprint out 80 (self#pGlobal () g)

  method private pFunDecl () f =
      self#pVDecl () f.svar
      ++ line
      ++ text "{ "
      ++ (align
            (* locals. *)
            ++ (docList ~sep:line (fun vi -> self#pVDecl () vi ++ text ";")
                  () f.slocals)
            ++ line ++ line
            (* the body *)
            ++ self#pBlock () f.sbody)
      ++ line
      ++ text "}"

end

let ccuredBrowserPrinter = new ccuredBrowserPrinterClass

(** To save space, use an encoding of pointer kinds as small numbers **)
let kindCodes: (opointerkind, int) H.t = H.create 17
let nextKindCode = ref 0
let encodeKind (k: opointerkind) : int =
  try
    H.find kindCodes k
  with Not_found -> begin
    let code = !nextKindCode in
    H.add kindCodes k code;
    incr nextKindCode;
    code
  end

(* Now dump the codes *)
let dumpKindEncoding (c: out_channel) =
  H.iter
    (fun k code ->
      fprint c 80 (dprintf "parent.kindCodes[%d]='%a';\n"
                     code d_opointerkind k))
    kindCodes

(*** Encode locations. For each file we assign a small integer *)
let fileCodes : (string, int) H.t = H.create 17
let nextFileCode = ref 0
let encodeLocation (l: location) : int * int =
  (try H.find fileCodes l.file
  with Not_found -> begin
    let fcode = !nextFileCode in
    incr nextFileCode;
    H.add fileCodes l.file fcode;
    fcode
  end),
  l.line
let dumpFileEncoding (c: out_channel) =
  H.iter
    (fun fn code ->
      fprint c 80 (dprintf "parent.fileCodes[%d]='%s';\n" code fn))
    fileCodes

(**** Encode edges. We do not encode ECompat edges, but instead we explain
    * them in terms of ECast edges ***)
let lastEncodedEdgeId = ref (-1)
(* For each edge we map the edge id (eid) to the edge and the encoding index *)
let encodedEdges: (int, edge * int) H.t = H.create 1111

(* Encode an edge. If the resulting list starts with a negative number then
 * this is an ECompat edge and the encoding is the encoding of its chain *)
let rec encodeEdge (e: edge) : int list =
  match e.ekind with
    ECompat r -> encodeChain r
  | _ ->
      try
        [snd (H.find encodedEdges e.eid)]
      with Not_found -> begin
        incr lastEncodedEdgeId;
        H.add encodedEdges e.eid (e, !lastEncodedEdgeId);
        [!lastEncodedEdgeId]
      end

(* The encoding of a chain starts with a negative integer that is the length
 * of the rest of the list followed by edge indices. If an edge index is
 * negated then this is a RSym edge *)
and encodeChain (r: chain) : int list =
  (* Convert a chain to a list *)
  let edges = chainToList r in
  (- (List.length edges)) ::
  (List.map
     (fun (sym, e) ->
       let eidx =
         match encodeEdge e with
           [ eidx ] -> eidx
         | _ -> E.s (bug "Edge %d->%d does not have singleton encoding. Make sure you do not use mkRSingle on ECompat edges."
                       e.efrom.id e.eto.id)
       in
       if sym then - eidx else eidx)
     edges)

let emitOneEdge (c: out_channel) (eidx: int) (e: edge) =
  let f, ln = encodeLocation e.eloc in
  let k =
    (* This must match the decoder implementation in
     * "browser_code.js:decodeOneEdge" *)
    match e.ekind with
      ECast EEK_cast -> 0
    | ECast EEK_union -> 1
    | ECast EEK_mkptr -> 2
    | ECast EEK_copytags -> 3
    | ECast EEK_cxxOverride -> 4
    | ECast EEK_extends -> 5
    | ECast EEK_rtti -> 6
    | ESameKind EEK_trustedCast -> 10
    | EIndex -> 11
    | EOffset -> 12
    | EPointsTo -> 13
    | EArgs -> 14
    | ESameType -> 15
    | ESameKind EEK_taggedUnion -> 16
    | ek -> E.s (bug "trying to dump edge of kinds %a\n" d_ekind ek)
  in
  (* See if this is interesting and was found in the code *)
  let hasMarker : doc =
    try
      let pIdx = H.find interestingFeatures (edgeToFeature e) in
      let fileIdx, featureIdx, _ = !pIdx in
      if featureIdx >= 0 then
        text "," ++ num fileIdx ++ text "," ++ num featureIdx
      else
        nil (* Was not marked in the code *)
    with Not_found -> nil
  in
  fprint c 80 (dprintf "ae(%d,%d,%d,%d,%d,%d%a);\n"
                 eidx e.efrom.id e.eto.id k f ln insert hasMarker)

(*** Encode flags. They are already encoded *)
let dumpFlagEncoding (c: out_channel) =
  Array.iteri (fun i what ->
    fprint c 80 (dprintf "parent.flagCodes[%d]='%s';\n" i what))
    pkFlagName

(*** Encoding whykind ***)
(* !!! If you change this, change also the decoder in lib/browser_code.js *)
let encodeWhyKind (n: node) : int list =
  (* Assume that we have fewer than 16 main codes  *)
  let mult = 16 in
  let encodeSpecial (s: string) (l: location) : int list =
    let f, ln = encodeLocation l in
    [f; ln] (* Leave alone the rest for now *)
  in
  match n.why_kind with
  | Unconstrained -> [0]
  | UserSpec -> [1]
  | PolyInt -> [2]
  | Default -> [3]
  | PrintfArg -> [4]
  | BoolFlag(i) -> [5 + mult * i]
  | Special (s, l) -> 7 :: encodeSpecial s l

  | BadCast e ->
      8 :: List.hd (encodeEdge e) (* This should be a single edge *) ::
      begin
        (* Now see if any of the ends is a void-ptr. In that case we follow
         * the encoding of the edge with the encoding of the representatives
         * and the chain they are connected. *)
        let frep, why_efrom_frep = get_rep_why e.efrom in
        let trep, why_eto_trep = get_rep_why e.eto in
        if frep != e.efrom || trep != e.eto then
          let why_frep_trep =
            mkRTrans (mkRSym why_efrom_frep)
              (mkRTrans (mkRSingle e) why_eto_trep) in
          frep.id :: trep.id :: encodeChain why_frep_trep
        else
          []
      end
  | BadSequenceCast e -> 9 :: encodeEdge e

  | Incompat (n1,why_n1_n2, n2) ->
      (10 + mult * n1.id) :: n2.id :: encodeChain why_n1_n2

  | SpreadFromNode (n_near, chain, n_source) ->
      (11 + mult * n_source.id) :: n_near.id :: encodeChain chain

(** Encoding whyFlag *)
(* !!! If you change this, change also the decoder in lib/browser_code.js *)
let emitNodeFlags (c: out_channel) (n: node) =
  let oneFlag (fidx: int) (wf: whyflag) : int list =
    (* We assume at most 8 chains. This way we can encode two integers into
     * one *)
    let mult = 8 in
    match wf with
    | FlagSpreadFromNode(n_near, chain, n_source) ->
        (0 + mult * n_source.id) :: n_near.id :: encodeChain chain
    | ProgramSyntax(l) ->
        let fl, ln = encodeLocation l in
        (* See if it is interesting *)
        let marker: int list =
          try
            let ck =
              if fidx = pkArith || fidx = pkPosArith then
                CKArith
              else if fidx = pkString then
                CKString
              else if fidx = pkIntCast then
                CKIntCast
              else
                raise Not_found
            in
            let pIdx = H.find interestingFeatures { loc = l;
                                                    src = 0;
                                                    dest = n.id;
                                                    cKind = ck } in
            let fileIdx, featureIdx, _ = !pIdx in
            if featureIdx >= 0 then
              fileIdx :: featureIdx :: []
            else
              []
          with Not_found -> []
        in
        (1 + mult * fl) :: ln :: marker

    | DownCast(n) -> [2 + mult * n.id]
    | SubtypeFailed(n) -> [3 + mult * n.id]
    | RequiredByEdge(e) -> 4 :: encodeEdge e
    | RequiredByPointerKind(o) -> [5 + mult * (encodeKind o)]
    | RequiredByFlag(i) -> [6 + mult * i]
    | FlUserSpec l ->
        let fl, ln = encodeLocation l in
        [7 + mult*fl; ln]
  in
  let browserPrintAllFlags = false in
  Array.iteri
    (fun idx wfo ->
      match wfo with
        (* Do not print certain flags *)
      | Some wf when (browserPrintAllFlags ||
        (idx <> pkUpdated &&
         idx <> pkReferenced &&
         idx <> pkInterface &&
         idx <> pkEscape &&
         (* Do not emit the posArith flag if we emit the pkArith flag *)
         (idx <> pkPosArith || not (hasFlag n pkArith))))
        ->
          let args = oneFlag idx wf in
          fprint c 80
            (dprintf "nf(%d,%d,%a);\n" n.id idx (docList num) args)

      | _ -> ())
    n.flags

let emitBrowserNode (c: out_channel) n =
  let why_kind = encodeWhyKind n in
  let fidx = try H.find fileOfNode n.id with Not_found -> -1 in
  fprint c 80
    (text "an(" ++
       num n.id ++ text "," ++
       num fidx ++ text "," ++
       num (encodeKind n.kind) ++ text "," ++
       (docList num) () why_kind ++ text ");\n");
  emitNodeFlags c n

(** Read a file and print it to the output, while changing some keywords *)
let copyFileToOutput (fn: string)
                     (out: out_channel)
                     (changes: (string, string) H.t) =
  let inch =
    try
      open_in fn
    with e ->
      raise (Arg.Bad("Cannot open input file " ^ fn))
  in
  let repl_regexp = Str.regexp "@@\\([^@]+\\)@@" in
  try
    while true do
      let in_line = input_line inch in
      (* Now see if we must make some replacements *)
      let in_line' =
        Str.global_substitute repl_regexp
          (fun s ->
            let key = Str.matched_group 1 s in
            try
              H.find changes key
            with Not_found ->
              Str.matched_string s)
          in_line
      in
      output_string out in_line';
      output_string out "\n";
    done
  with End_of_file ->
    close_in inch

let printBrowser (outdir: string) file =
  if !E.verboseFlag then
    ignore (E.log "printing browser info\n");
  H.clear kindCodes;
  nextKindCode := 0;
  H.clear fileCodes;
  nextFileCode := 0;
  currentOutIdx := -1;
  H.clear fileOfNode;
  lastEncodedEdgeId := -1;
  H.clear encodedEdges;
  lastInterestingFeatureId := -1;
  lastForwardFeatureId := -1;
  H.clear badCasts;
  nrBadCasts := 0;

  H.clear incompats;

  (* Make a scan to find the interesting syntactic features *)
  collectInterestingFeatures file;
  if !E.verboseFlag then
    ignore (E.log "browser: 1\n");
  if !Cc_args.libDir = "" then
    E.s (error "The browser data can be printed only if the --libdir argument is also given\n");
  (* We split the printout into several files. We decide when to split by
   * calculating an approximate size of globals: for functions we count the
   * number of instructions; for variables, the size of the initializer; for
   * structure definitions, the number of fields. *)
  let sizeOfGlobal = function
      GFun(fd, _) ->
        let rec statementSize (acc: int) (s: stmt) =
          match s.skind with
            Instr il -> acc + List.length il
          | Return _ | Goto _ | ComputedGoto _ | Break _ | Continue _ -> acc + 1
          | If(_, bt, bf, _) ->
              blockSize (blockSize (1 + acc) bt) bf
          | Switch (_, b, _, _) -> blockSize (1 + acc) b
          | Loop (b, _, _, _) -> blockSize (1 + acc) b
          | Block b -> blockSize acc b
          | TryExcept (b, (il, e), h, _) ->
              blockSize (blockSize (1 + List.length il + acc) b) h
          | TryFinally (b, h, _) ->
              blockSize (blockSize (1 + acc) b) h

        and blockSize (acc: int) (b: block) =
          List.fold_left statementSize acc b.bstmts
        in
        blockSize 0 fd.sbody
    | GVar (vi, {init=Some (CompoundInit (_, il))},  _) -> 1 + List.length il
    | GVar _ -> 1
    | GVarDecl _ | GCompTagDecl _ | GEnumTagDecl _
    | GType _ | GPragma _ | GText _ | GAsm _  -> 1
    | GCompTag (ci, _) -> List.length ci.cfields
    | GEnumTag (ei, _) -> List.length ei.eitems
  in
  let currentOutChannel = ref stdout in
  let o s = output_string !currentOutChannel s in
  (* Start and close a new file *)
  let startCloseNewFile
        (basename: string)
        (pre: unit -> unit)
        (post: unit -> unit) :   (unit -> unit) (* start new one *)
                               * (unit -> unit) (* close the last one*) =
    let rec startit () =
      closeit ();
      incr currentOutIdx;
      currentOutChannel :=
         (let oname =
           outdir ^ "/" ^ basename ^ "__" ^
           (string_of_int !currentOutIdx) ^ ".html" in
         if !E.verboseFlag then
           ignore (E.log "printing browser output file %s\n" oname);
         try open_out oname
         with e -> raise (Arg.Bad("Cannot open output file " ^ oname)));
      pre ()

        (* Close the current file *)
    and  closeit () =
      if !currentOutChannel != stdout then begin
        post ();
        close_out !currentOutChannel;
        currentOutChannel := stdout
      end
    in
    startit, closeit
  in

  let startNewSourceFile, closeSourceFile =
    startCloseNewFile
      "source"
      (fun _ -> (* PRE SOURCE *)
        o "<html>";
        o "<body bgcolor=white onload='parent.fileFinishedLoading();'>\n";
        (* The styles.css file was copied there by the ccured script *)
        o ("<link rel=stylesheet type=\"text/css\" href=\"styles.css\">");
        o "<pre>\n")


      (* At the end of each file we must define some trampolines for the
      * functions that we use in the file. We do this to keep the function
      * names short in the main file *)
      (fun _ -> (* POST SOURCE *)
        o "</pre>\n";
        o "<script language=\"javascript\">\n";
        o "// Trampoline for sn\n";
        o "var sn = parent.sn;\n";
        o "var sf = parent.sf;\n";
        o "var sff = parent.sff;\n";
        (* After the document finished loading we call the handler. We cannot
        * do this for the first document because it appears that the code is
        * not already loaded when this loads *)
        o ("if(parent.fileFinishedLoading == undefined) { alert('The code is not yet loaded (in source file)');}\n");
        o "</script></html>\n")
  in

    (* Now print the file. Keep a counter of how many lines we've printed so
     * far in this file  *)
  let sofarInThisFile = ref 0 in
  startNewSourceFile ();
  iterGlobals
    file
    (fun g ->
      (* See if we must change the file *)
      if !sofarInThisFile >= !browserSourceFileSize then begin
        startNewSourceFile ();
        sofarInThisFile := 0
      end;
      (* Now print the global *)
      dumpGlobal ccuredBrowserPrinter !currentOutChannel g;
      (* Now update the counter *)
      sofarInThisFile := !sofarInThisFile + sizeOfGlobal g);
  (* Close the last file *)
  closeSourceFile ();
  (* Now remember the index of the last source file *)
  let lastSourceFile = !currentOutIdx in

  (************** Now create the node info files *)

  currentOutIdx := -1; (* Restart the counter *)
  let startNewNodeFile, closeNodeFile =
    startCloseNewFile "node"
      (fun _ -> (* PRE NODE *)
        o "<html>";
        o "<body bgcolor=white onload='parent.fileFinishedLoading();'>\n";
        o ("Loading node info file " ^ (string_of_int !currentOutIdx) ^ "...");
        o "\n<script language=\"javascript\">\n";
        o "// Some trampolines\n";
        o "var an=parent.an;\n";
        o "var nf=parent.nf;\n";
        o "if(an == undefined) { alert('The code is not yet loaded'); }\n")

      (fun _ -> (* POST NODE *)
        o "\n</script>Done</html>")
  in

  (* Get the nodes ordered by ID. *)
  let sortedNodes =
    Stats.time "sortgraph"
      (fun () ->
        let all : node list ref = ref [] in
        H.iter (fun id n -> all := n :: !all) idNode;
        List.sort (fun n1 n2 -> compare n1.id n2.id) !all) ()
  in
  List.iter (fun n ->
    if n.id >= 0 then begin
      (* See if we must start a new node *)
      if n.id mod !browserNodeFileSize = 0 then begin
        startNewNodeFile ();
      end;
      emitBrowserNode !currentOutChannel n;
    end) sortedNodes;
  closeNodeFile ();

  (************** Now create the edge info files *)

  currentOutIdx := -1; (* Restart the counter *)
  let startNewEdgeFile, closeEdgeFile =
    startCloseNewFile "edge"
      (fun _ -> (* PRE EDGE *)
        o "<html>";
        o "<body bgcolor=white  onload='parent.fileFinishedLoading();'>\n";
        o ("Loading edge info file " ^ (string_of_int !currentOutIdx) ^ "...");
        o "\n<script language=\"javascript\">\n";
        o "var ae=parent.ae;\n";
        o "if(ae == undefined) { alert('The code is not yet loaded'); }\n")

      (fun _ -> (* POST EDGE *)
        o "\n</script>Done</html>\n";
        )
  in

  (* Get the edges ordered by index into the file. *)
  let sortedEdges =
    Stats.time "sortedges"
      (fun () ->
        let all : (edge * int) list ref = ref [] in
        H.iter (fun id x -> all := x :: !all) encodedEdges;
        List.sort (fun (_, idx1) (_, idx2) -> compare idx1 idx2) !all) ()
  in
  List.iter
    (fun (e, eidx) ->
      (* See if we must start a new edge file *)
      if eidx mod !browserNodeFileSize = 0 then begin
        startNewEdgeFile ();
      end;
      emitOneEdge !currentOutChannel eidx e)
    sortedEdges;
  closeEdgeFile ();

  (** Create the global index file. *)
  (* First collect the globals and the types *)
  let allGlobals: (string * int * int) list ref = ref [] in
  let globalsCount = ref 0 in
  let allTypes: (string * int * int) list ref = ref [] in
  let typesCount = ref 0 in
  if emitGlobals then
    H.iter
      (fun ci pIdx ->
        let fileIdx, featureIdx, _ = !pIdx in
        match ci.cKind with
          CKVar vn ->
            incr globalsCount;
            allGlobals := (vn, fileIdx, featureIdx) :: !allGlobals
        | CKType tn | CKComp tn ->
            incr typesCount;
            allTypes := (tn, fileIdx, featureIdx) :: !allTypes
        | _ -> ()
              )
      interestingFeatures;

  (* Now a function to emit such a list *)
  let emitSorted (what: (string * int * int) list)
                 (filename: string)
                 (loadFunName: string) =
    let sortedFile =
      (let oname = outdir ^ "/" ^ filename in
      if !E.verboseFlag then
        ignore (E.log "printing browser global file %s\n" oname);
      try open_out oname
      with e -> raise (Arg.Bad("Cannot open output file " ^ oname))) in
    let os s = output_string sortedFile s in
    os "<html>";
    os "<body bgcolor=white  onload='parent.fileFinishedLoading();'>\n";
    os ("Loading "^filename^" info file... ");
    os "\n<script language=\"javascript\">\n";
    os ("var "^loadFunName^"=parent."^loadFunName^";\n");
    os ("if("^loadFunName^"== undefined) { alert('The code is not yet loaded'); }\n");
    (* Now sort the list *)
    let sortedList =
      List.sort (fun (s1, _, _) (s2, _, _) -> Pervasives.compare s1 s2) what in
    let count = ref 0 in
    List.iter
      (fun (n, fileIdx, featureIdx) ->
        fprint sortedFile 80
            (dprintf "%s(%d,'%s@@%d:%d');\n"
               loadFunName !count n fileIdx featureIdx);
        incr count)
      sortedList;
    os "\n</script>Done</html>\n";
    close_out sortedFile
  in
  if emitGlobals then begin
    emitSorted !allGlobals "globals.html" "ag";
    emitSorted !allTypes "types.html" "at";
  end;

  (*** Now create the top-level frame *)
  begin
    let oc =
      let oname = outdir ^ "/index.html" in
      try open_out oname
      with e -> raise (Arg.Bad("Cannot open output file " ^ oname))
    in
    let indexHash = H.create 13 in
    H.add indexHash "liburl" ".";
    (* Store in the top-level file the name of the first html chunk *)
    copyFileToOutput (!Cc_args.libDir ^ "/browser_index.html") oc indexHash;
    close_out oc
  end;

  (* Put the actual code in the form file *)
  currentOutChannel :=
     (let oname = outdir ^ "/form.html" in
     if !E.verboseFlag then
       ignore (E.log "printing browser code file %s\n" oname);
     try open_out oname
     with e -> raise (Arg.Bad("Cannot open output file " ^ oname)));

  let formHash : (string, string) H.t = H.create 5 in
  H.add formHash "liburl" ".";
  H.add formHash "maxnode" (string_of_int !lastNodeId);
  H.add formHash "nrBadCasts" (string_of_int !nrBadCasts);
  H.add formHash "nrIncompatClasses" (string_of_int !nrIncompatClasses);
  H.add formHash "nrIncompatCasts" (string_of_int !nrIncompatCasts);
  H.add formHash "nrGlobals" (string_of_int !globalsCount);
  H.add formHash "nrTypes" (string_of_int !typesCount);
  (* Create the file selection *)
  (* Make a list 0 .. max *)
  let rec mkListToMax (tail: int list) (i: int) : int list =
    if i < 0 then tail else
    mkListToMax (i :: tail) (i -1)
  in
  let selFiles =
    sprint 80
      (dprintf "%a"
         (docList ~sep:line
            (fun i -> dprintf "<option value='%d'>%d" i i))
         (mkListToMax [] lastSourceFile)) in
  H.add formHash "selectfiles" selFiles;
  copyFileToOutput (!Cc_args.libDir ^ "/browser_form.html")
    !currentOutChannel formHash;

  (* pre-Allocate the arrays *)
  fprint !currentOutChannel 80
    (dprintf "parent.nodelist = new Array(%d);\n" (!lastNodeId + 1));
  fprint !currentOutChannel 80
    (dprintf "parent.nodesPerFile = %d;\n" !browserNodeFileSize);

  fprint !currentOutChannel 80
    (dprintf "parent.edgelist = new Array(%d);\n" (1 + !lastEncodedEdgeId));
  fprint !currentOutChannel 80
    (dprintf "parent.edgesPerFile = %d;\n" !browserNodeFileSize);

  fprint !currentOutChannel 80
    (dprintf "parent.globalslist = new Array(%d);\n" !globalsCount);
  fprint !currentOutChannel 80
    (dprintf "parent.typeslist = new Array(%d);\n" !typesCount);

  (* Dump the bad casts. These should not be too many *)
  let _ =
    o "// Bad casts\n";
    fprint !currentOutChannel 80
      (dprintf "parent.nrBadCasts = %d;parent.badCastEdge=new Array(parent.nrBadCasts);parent.badCastIsSeq=new Array(parent.nrBadCasts);\n" !nrBadCasts);
    let count = ref 0 in
    H.iter
      (fun eid isSeq ->
        let _, encidx =
          try H.find encodedEdges eid
          with Not_found -> E.s (E.bug "bad cast edge %d is not encoded\n" eid)
        in
        fprint !currentOutChannel 80
          (dprintf "parent.badCastEdge[%d]=%d;\n" !count encidx);
        fprint !currentOutChannel 80
          (dprintf "parent.badCastIsSeq[%d]=%b;\n" !count isSeq);
        incr count)
      badCasts
  in
  (* Dump the incompatible classes. These should not be too many *)
  let _ =
    o "// Incompatible classes\n";
    fprint !currentOutChannel 80
      (dprintf "parent.nrIncompat = %d;parent.incompatClass=new Array(parent.nrIncompat);var theIncompat;\n" !nrIncompatClasses);
    let count = ref 0 in
    List.iter
      (fun (nd, extremes) ->
        fprint !currentOutChannel 80
          (dprintf "parent.incompatClass[%d]='%d:%a';\n"
             !count nd.id
             (docList
                (fun (n, e) ->
                  let _, eidx =
                    try H.find encodedEdges e.eid
                    with Not_found ->
                      E.s (E.bug "extreme edge %d is not encoded\n" e.eid)
                  in
                  dprintf "%d@@%d" n.id eidx))
             extremes);
        incr count)
      !incompatEquivalence
  in
  o "// The encoding of kinds \n";
  dumpKindEncoding !currentOutChannel;
  o "// The encoding of files \n";
  dumpFileEncoding !currentOutChannel;
  o "// The encoding of flags \n";
  dumpFlagEncoding !currentOutChannel;
  o "// The forward feature references\n";
  fprint !currentOutChannel 80
    (dprintf "parent.forwardFeatures = new Array(%d);\n"
       (!lastForwardFeatureId + 1));
  (H.iter (fun _ pIdx ->
    let fileIdx, featureIdx, forwardId = !pIdx in
    if forwardId >= 0 then
      fprint !currentOutChannel 80
        (dprintf "parent.forwardFeatures[%d] = '%d:%d';\n"
           forwardId fileIdx featureIdx))
     interestingFeatures);

  (* Now signal the end of the code *)
  o "// alert('form has loaded');\n";
  o "</script></html>\n";
  close_out !currentOutChannel
