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

(* A module that pulls out certain global initializers and generates 
 * initialization code in a special per-module function *)
open Cil
open Pretty 
open Trace

module H = Hashtbl
module E = Errormsg

let mainname = ref "main"

(* Insert the global initializer in the main *)
let insertGlobInit (file: file) : unit = 
  match file.globinit with 
  | Some gi when not file.globinitcalled -> 
      let theFile : global list ref = ref [] in
      let inserted = ref false in
      List.iter 
        begin
          fun g ->
            (match g with
              GFun(m, lm) when m.svar.vname = !mainname ->
                (* Prepend a prototype *)
                theFile := GVarDecl (gi.svar, lm) :: !theFile;
                m.sbody.bstmts <- 
                   compactStmts (mkStmt (Instr [Call(None, 
                                                     Lval(var gi.svar), 
                                                     [], locUnknown)]) 
                                 :: m.sbody.bstmts);
                inserted := true;
                file.globinitcalled <- true;
                if !E.verboseFlag then
                  ignore (E.log "Inserted the globinit\n")
            | _ -> ());
            theFile := g :: !theFile (* Now put the global back *)
        end
        file.globals;
      if not !inserted then 
        ignore (E.warn "Cannot find %s to add global initializer %s" 
                  !mainname gi.svar.vname);
      file.globals <- List.rev !theFile
  | Some gi  (* when file.globinitcalled *) -> 
      (* getGlobInit has already inserted a call.  *)
      (* Add a prototype to the start of the file.  getGlobInit does this too,
         but we clobber file.globals while curing. *)
      file.globals <- GVarDecl(gi.svar, locUnknown)::file.globals
  | None -> ()


let doFile (fl: file) : file = 
  let boxing = ref true in
  let rec doGlobal = function
      GVar (vi, {init = Some init}, l) as g -> 
        let hasPointers = 
          existsType 
            (fun t ->
              match t with 
                TPtr _ -> ExistsTrue
              | _ -> ExistsMaybe) vi.vtype in
        if !boxing && hasPointers then 
          let finit = getGlobInit fl in
          (* Now generate the code. Baseoff is the offset to the current 
           * compound  *)
          let rec initone (baseoff: offset) off what t acc = 
            let off' = addOffset off baseoff in
            match what with
              CompoundInit (t, initl) -> 
                foldLeftCompound ~implicit:false
                           ~doinit:(initone off') ~ct:t ~initl:initl ~acc:acc
(*
            | ArrayInit (bt, len, initl) -> 
                let idx = ref (-1) in
                List.fold_left 
                  (fun acc i -> 
                    incr idx;
                    initone off' (Index(integer !idx, NoOffset)) i bt acc)
                  acc
                  initl
*)
            | SingleInit ei -> 
                mkStmt (Instr [Set ((Var vi, off'), ei, locUnknown)]) 
                :: acc
          in
          let inits = 
            initone NoOffset NoOffset init vi.vtype finit.sbody.bstmts in 
          finit.sbody.bstmts <- compactStmts (List.rev inits);
          GVar (vi, {init = None}, l)
        else g
          
        (* Leave alone all other globals *)
    | GPragma (a, _) as g -> begin
        (match a with
        | Attr("ccure", [ACons("on",[])]) -> boxing := true
        | Attr("ccure", [ACons("off",[])]) -> boxing := false
        | _ -> ());
        g
    end
  | g -> g
  in
  let newglobals = List.map doGlobal fl.globals in (* Do this first *)
  let newfile = {fl with globals = newglobals} in
  if !Cilutil.doCheck then begin
    ignore (E.log "Checking after globinit\n");
    ignore (Check.checkFile [] newfile)
  end;
  insertGlobInit newfile;
  newfile
  


