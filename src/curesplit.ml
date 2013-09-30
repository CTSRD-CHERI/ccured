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
open Trace

module H = Hashtbl
module E = Errormsg

let dontSplit = ref false
let metaSplit = ref false

(* Whether to split the arguments of functions *)
let splitArguments = true

(* Whether we try to do the splitting all in one pass. The advantage is that 
 * it is faster and it generates nicer names *)
let lu = locUnknown

(* Go over the code and split fat temporary variables into several separate 
 * variables. The hope is that the compiler will have an easier time to do 
 * standard optimizations with the resulting scalars *)
(* Unfortunately, implementing this turns out to be more complicated than I 
 * thought *)
let onePassSplit = false

(** Iterate over the fat fields. Returns the empty list if no fat type. The 
 * offsets are in order in which they appear in the fat type. The first field 
 * must have the name "_p". Along with the offset we pass a string that 
 * identifies the meta-component, and the type of that component. *)
let mapFatFields (doit: offset * string * typ -> 'a) (t: typ) : 'a list = 
  match unrollType t with
  | TComp (comp, _) -> 
      if onePassSplit then 
        if hasAttribute "mergecomp" comp.cattr then begin
          (* We get the _p field from here *)
          match comp.cfields with 
            fp :: fmeta :: [] when fp.fname = "_p" -> begin
              match fmeta.ftype with 
                TComp (mcomp, _) -> 
                  (* The _p field is the first one *)
                  doit (Field(fp, NoOffset), fp.fname, fp.ftype) ::
                  List.map (fun f -> doit (Field(fmeta, Field(f, NoOffset)),
                                           f.fname,
                                           f.ftype)) mcomp.cfields
              | _ -> E.s (bug "Meta-field %s is not a TComp" fmeta.fname)
            end
          | _ -> E.s (bug "Merge-comp %s has too many fields" comp.cname)
        end else if hasAttribute "metacomp" comp.cattr then 
          List.map 
            (fun f -> doit (Field(f, NoOffset), f.fname, f.ftype)) 
            comp.cfields
        else 
          []
      else if
        ((not !metaSplit) && (hasAttribute "mergecomp" comp.cattr)) ||
        (!metaSplit && hasAttribute "metacomp" comp.cattr) 
      then
        List.map 
          (fun f -> doit (Field(f, NoOffset), f.fname, f.ftype)) 
          comp.cfields
      else
        []

  | _ -> []
  

(* Map a variable name to a list of component variables, along with the 
 * accessor offset. The first field element in the list is supposed to 
 * always be the actual data (the _p field).  *)
let newvars : (string, (offset * varinfo) list) H.t = H.create 13

let re1 = Str.regexp "\\(.+\\)_ms[0-9]*"

(* Split a variable and return the replacement, in the proper order. If this 
 * variable is not split, then return just the variable. *)
let splitOneVar (v: varinfo) 
                (mknewvar: string -> typ -> varinfo) : varinfo list = 
  let vars = 
    mapFatFields
      (fun (off, n, t) -> 
        if n = "_p" then begin (* The first one, reuse *)
          v.vtype <- t;
          off, v
        end else begin (* make a new one *)
          (* We try to generate nicer names. If the v.vname ends with _msxxx 
           * then we drop that *)
          let newname = 
            if Str.string_match re1 v.vname 0 then 
              (Str.matched_group 1 v.vname) ^ n
            else
              v.vname ^ n 
          in
          let v'= mknewvar newname t in
          off, v'
        end)
      v.vtype
  in
  if vars <> [] then begin
    (* Now remember the newly created vars *)
    H.add newvars v.vname vars;
    List.map snd vars (* Return just the vars *)
  end else
    [ v ]
      


(* A visitor that finds all locals that appear in a call or have their 
 * address taken *)

let dontSplitLocals : (string, bool) H.t = H.create 111
class findVarsCantSplitClass : cilVisitor = object (self) 
  inherit nopCilVisitor
        
        (* expressions, to see the address being taken *)
  method vexpr (e: exp) : exp visitAction =
    match e with 
      AddrOf (Var v, NoOffset) -> 
        H.add dontSplitLocals v.vname true; SkipChildren
      (* See if we take the address of the "_ms" field in a variable *)
    | AddrOf (Var v, Field(ms, _)) 
        when hasAttribute "mergecomp" ms.fcomp.cattr-> 
        H.add dontSplitLocals v.vname true; SkipChildren
    | _ -> DoChildren


          (* variables involved in call instructions *)
  method vinst (i: instr) : instr list visitAction = 
    match i with 
      Call (res, f, args, _) -> 
        (match res with 
          Some (Var v, NoOffset) -> H.add dontSplitLocals v.vname true
        | _ -> ());
        if not splitArguments then 
          List.iter (fun a -> 
            match a with
              Lval (Var v, NoOffset) -> H.add dontSplitLocals v.vname true
            | _ -> ()) args; 
        (* Now continue the visit *)
        DoChildren

    | _ -> DoChildren

          (* Variables used in return should not be split *)
  method vstmt (s: stmt) : stmt visitAction = 
    match s.skind with 
      Return (Some (Lval (Var v, NoOffset)), _) -> 
        H.add dontSplitLocals v.vname true; DoChildren
    | Return (Some e, _) -> 
        DoChildren
    | _ -> DoChildren

  method vtype t = SkipChildren

end
let findVarsCantSplit = new findVarsCantSplitClass




class splitVarVisitorClass : cilVisitor = object (self)
  inherit nopCilVisitor


  (* We must process the function types *)
  method vtype t = 
    (* We invoke the visitor first and then we fix it *)
    let postProcessFunType (t: typ) : typ = 
      match t with 
        TFun(rt, Some params, isva, a) -> 
          let rec loopParams = function
              [] -> []
            | ((pn, pt, pa) :: rest) as params -> 
                let rest' = loopParams rest in
                let res = 
                  mapFatFields
                    (fun (fi, n, t) -> 
                      (* Careful with no-name parameters, or we end up with 
                       * many parameters named _p ! *)
                      ((if pn <> "" then pn ^ n else ""), t, pa)) 
                    pt
                in
                if res = [] then (* Not a fat *)
                  if rest' == rest then 
                    params (* No change at all. Try not to reallocate so that 
                            * the visitor does not allocate. *)
                  else
                    (pn, pt, pa) :: rest'
                else (* Some change *)
                  res @ rest'
          in
          let params' = loopParams params in
          if params == params' then 
            t
          else
            TFun(rt, Some params', isva, a)
          
      | t -> t
    in
    if splitArguments then 
      ChangeDoChildrenPost(t, postProcessFunType)
    else
      SkipChildren

      (* Whenever we see a variable with a field access we try to replace it 
       * by its components *)
  method vlval ((b, off) : lval) : lval visitAction = 
    try
      match b, off with
        Var v, (Field _ as off) ->
          (* See if this variable has some splits.Might throw Not_found *)
          let splits = H.find newvars v.vname in
          (* Now find among the splits one that matches this offset. And 
           * return the remaining offset *)
          let rec find = function
              [] -> 
                E.s (E.bug "Cannot find component %a of %s\n" 
                       (d_offset nil) off v.vname)
            | (splitoff, splitvar) :: restsplits -> 
                let rec matches = function 
                    Field(f1, rest1), Field(f2, rest2) 
                      when f1.fname = f2.fname -> 
                        matches (rest1, rest2)
                  | off, NoOffset -> 
                      (* We found a match *)
                      (Var splitvar, off)
                  | NoOffset, restoff -> 
                      ignore (warn "Found aggregate lval %a\n" 
                                d_lval (b, off));
                      find restsplits

                  | _, _ -> (* We did not match this one; go on *)
                      find restsplits
                in
                matches (off, splitoff)
          in
          ChangeTo (find splits)
      | _ -> DoChildren
    with Not_found -> DoChildren

        (* Sometimes we pass the variable as a whole to a function or we 
         * assign it to something *)
  method vinst (i: instr) : instr list visitAction = 
    match i with
      (* Split into two instructions and then do children. Howver, v._p might 
       * appear in the lv and if we duplicate the instruction we might get 
       * bad results. To fix this problem we make sure that the update to _p 
       * happens last. Other fields of v should not appear in lv. *)
      Set ((Var v, NoOffset), Lval lv, l) when H.mem newvars v.vname -> begin
        match H.find newvars v.vname with
          fst :: rest -> 
            ChangeTo 
              (List.map 
                 (fun (off, newv) ->  
                   let lv' = 
                     visitCilLval (self :> cilVisitor)
                       (addOffsetLval off lv) in
                   Set((Var newv, NoOffset), Lval lv', l))
                 (rest @ [fst]))
        | _ -> E.s (errorLoc l "No first field (in splitFats)")
      end 
 
      | Set (lv, Lval (Var v, NoOffset), l) when H.mem newvars v.vname ->
          begin
            match H.find newvars v.vname with
              fst :: rest -> 
                ChangeTo  
                  (List.map 
                     (fun (off, newv) -> 
                       let lv' = 
                         visitCilLval (self :> cilVisitor)
                           (addOffsetLval off lv) in
                       Set(lv', Lval (Var newv, NoOffset), l))
                     (rest @ [fst]))
            | _ -> E.s (errorLoc l "No first field (in splitFats)")
          end 

        (* Split all function arguments in calls *)
      | Call (ret, f, args, l) when splitArguments ->
          (* Visit the children first and then see if we must change the 
           * arguments *)
          let finishArgs = function
              [Call (ret', f', args', l')] as i' -> 
                let mustChange = ref false in
                let newargs = 
                  (* Look for opportunities to split arguments. If we can
                   * split, we must split the original argument (in args).
                   * Otherwise, we use the result of processing children
                   * (in args'). *)
                  List.fold_right2
                    (fun a a' acc -> 
                      match a with
                        Lval (Var v, NoOffset) when H.mem newvars v.vname -> 
                          begin
                            mustChange := true;
                            (List.map 
                               (fun (_, newv) -> 
                                 Lval (Var newv, NoOffset)) 
                               (H.find newvars v.vname))
                            @ acc
                          end
                      | _ -> a' :: acc)
                    args args'
                    []
                in
                if !mustChange then 
                  [Call (ret', f', newargs, l')]
                else
                  i'
            | _ -> E.s (E.bug "splitVarVisitorClass: expecting call")
          in
          ChangeDoChildrenPost ([i], finishArgs)

      | _ -> DoChildren

        
  method vfunc (func: fundec) : fundec visitAction = 
    H.clear newvars;
    H.clear dontSplitLocals;
    (* Visit the type of the function itself *)
    if splitArguments then 
      func.svar.vtype <- visitCilType (self :> cilVisitor) func.svar.vtype;

    (* Go over the block and find the candidates *)
    ignore (visitCilBlock findVarsCantSplit func.sbody);

    (* Now go over the formals and create the splits *)
    if splitArguments then begin
      (* Split all formals because we will split all arguments in function 
       * types *)
      let newformals = 
        List.fold_right 
          (fun form acc -> 
            (* Process the type first *)
            form.vtype <- 
               visitCilType (self : #cilVisitor :> cilVisitor) form.vtype;
            let form' = 
              splitOneVar form 
                          (fun s t -> makeLocalVar func ~insert:false s t)
            in
            (* Now it is a good time to check if we actually can split this 
             * one *)
            if List.length form' > 1 &&
               H.mem dontSplitLocals form.vname then
              ignore (warn "boxsplit: can't split formal \"%s\" in %s. Make sure you never take the address of a formal.\n"
                     form.vname func.svar.vname);
            form' @ acc)
          func.sformals [] 
      in
      (* Now make sure we fix the type.  *)
      setFormals func newformals
    end;
    (* Now go over the locals and create the splits *)
    List.iter 
      (fun l ->
        (* Process the type of the local *)
        l.vtype <- visitCilType (self :> cilVisitor) l.vtype;
        (* Now see if we must split it *)
        if not (H.mem dontSplitLocals l.vname) then begin
          ignore (splitOneVar l (fun s t -> makeTempVar func ~name:s t))
        end) 
      func.slocals;
    (* Now visit the body and change references to these variables *)
    ignore (visitCilBlock (self :> cilVisitor) func.sbody);
    H.clear newvars;
    H.clear dontSplitLocals;
    SkipChildren  (* We are done with this function *)

  (* Try to catch the occurrences of the variable in a sizeof expression *)
  method vexpr (e: exp) = 
    match e with 
    | SizeOfE (Lval(Var v, NoOffset)) -> begin
        try
          let splits =  H.find newvars v.vname in
          (* We cound here on no padding between the elements ! *)
          ChangeTo
            (List.fold_left
               (fun acc (_, thisv) -> 
                 BinOp(PlusA, SizeOfE(Lval(Var thisv, NoOffset)), 
                       acc, uintType))
               zero
               splits)
        with Not_found -> DoChildren
    end
    | _ -> DoChildren
end

let splitVarVisitor = new splitVarVisitorClass


let splitLocals (f: file) : file = 
  H.clear dontSplitLocals;
  if not !dontSplit then begin
    metaSplit := false;
    ignore (visitCilFileSameGlobals splitVarVisitor f);
    if not onePassSplit then begin
      metaSplit := true;
      ignore (visitCilFileSameGlobals splitVarVisitor f);
    end;
    if splitArguments then 
      f.globals <- (GText "#define CCURED_SPLIT_ARGUMENTS") :: f.globals
  end;
  f
  



