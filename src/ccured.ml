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

module type FRONTEND =
  sig
   (* Signal that we are in MS VC mode *)
    val setMSVCMode: unit -> unit

   (* Parse a file in *)
    exception ParseError of string

    (* additional command line arguments *)
    val args  : (string * Arg.spec * string) list
    (* the main command to parse a file. Return a thunk that can be use to
     * convert the AST to CIL *)
    val parse : string -> (unit -> Cil.file)

  end
                                        (* Use the frontc frontend *)
module F : FRONTEND = Frontc
module C = Cil
module CK = Check
module E = Errormsg
open Pretty
open Trace

let binary_file_suffix = "bin" (* extension for binary "Cil.file"s *)

(*
 * [weimer] Mon Apr 29 13:33:45 PDT 2002
 * This verison of the CCured main.ml file allows the various CIL/CCured
 * stages to be performed separately. The stages:
 *
 * (1) convert post-processed input files to .cil
 * (2) merge many .cils into one .cil
 * (3) pull out global initializers
 * (4) infer pointer annotations on .cil, emit .cil with annotations
 * (5) cure annotated .cil, emit .cil with extra code
 * (6) program transformations (e.g., logcalls)
 * (7) optimize the resulting cured code (remove redundant checks)
 *
 * If you skip a stage, the output from the previous stage is passed along.
 * You may ask for the resulting file after any particular stage to be
 * emitted.
 *
 * For example, you might manually annotate a post-processed file and then
 * cure it with something like:
 *  ccured --cureOnly my_input_file.i --curedout my_cured_file.c
 *
 * As a convenience, you may use "--out" to get a printout of whatever we
 * had left right before CCured was about to exit normally.
 *
 * In addition, the command line arguments have been grouped and
 * streamlined.
 *)

let parseOneFile (fname:string) : Cil.file = begin
  if !Cilutil.printStages then ignore (E.log "Parsing %s\n" fname);
  let cil =
    if Filename.check_suffix fname binary_file_suffix then
      Stats.time "loading binary files" Cil.loadBinaryFile fname
    else
      F.parse fname ()
  in

  (* See if we had errors *)
  if !E.hadErrors then
    E.s (E.error "We had errors during parsing\n");
  if !Cilutil.doCheck then begin
    ignore (E.log "Checking CIL after CABS2CIL\n");
    ignore (CK.checkFile [] cil);
  end;
  cil
end

class stripASMVisitor = object
  inherit C.nopCilVisitor
  method vglob g = match g with
    C.GAsm(_,l) -> C.ChangeTo([C.GText("/* Removed ASM */\n")])
  | _ -> C.DoChildren
  method vinst i = match i with
    C.Asm(_) -> C.ChangeTo([])
  | _ -> C.SkipChildren
end

  (* E.logChannel *)
let cilChannel = ref None
let mergeChannel = ref None
let cxxppChannel = ref None
let globinitChannel = ref None
let cureChannel = ref None
let optChannel = ref None
let globAnnChannel = ref None

let optimOutFileName = ref ""

let defaultChannel = ref None


let main () = begin
  Cil.useLogicalOperators := false;

  (* what stages should we run? *)
  let doMerge = ref true in
  let doGlobInit = ref false in
  Cc_args.doCxxPP := false;
  let doInfer = ref true in
  let doCure = ref true in
  let doTransform = ref false in
  let doOpt = ref false in

  let doNothing () =
    doMerge := false ;
    Cc_args.doCxxPP := false ;
    doGlobInit := false ;
    doInfer := false ;
    doCure := false ;
    doTransform := false ;
    doOpt := false ;
    ()
  in

  let make_cfg = ref false in
  let doASTSlicerEnumerate = ref None in
  let doASTSlicerAnnotate = ref false in
  let doASTSlicer = ref false in
  let astslicerKeep = ref None in
  let astslicerDrop = ref None in

  let doTypeSizeCheck = ref false in
  let doListNonSafe = ref false in

  let stripASM = ref false in

  let doSimplemem = ref false in
  let doPartial = ref false in

  let maxSplit = ref false in
  let typecheck = ref false in
  let optimElimAll : string list ref = ref [] in
    (* A list of CHECK_xxx to remove  *)
  let doElimabc = ref false in

  (* sm: when true, merged output includes CIL pragmas and
   * attributes; this is important so we can have a merge process
   * which does not lose information, so merging can be separated
   * from other tasks (like curing) *)
  let mergeOutputHasAnnotations = ref false in

  (* open and set an output channel *)
  let outChannel (what:string) (cr: (out_channel * string * bool) option ref)
                 (fname: string) =
    match fname with
      "-" | "stdout" -> cr := Some(stdout,"stdout",false) ;
        if !E.verboseFlag then
          ignore (E.log "Writing %s output to stdout\n" what );
    | _ ->
      try
        (if Filename.check_suffix fname binary_file_suffix then
          cr := Some(open_out_bin fname, fname, true)
        else
          cr := Some(open_out fname,fname,  false)) ;
        if !E.verboseFlag then
          ignore (E.log "Writing %s output to %s\n" what fname );
      with e ->
        raise (Arg.Bad ("Cannot open " ^ what ^ " file " ^ fname))
  in

  let rec recursiveAddThing n =
    if (n = 0) then 0 else 1 + (recursiveAddThing (n-1))
  in

  let dumpFCG = ref false in

  let default_stages =
    Printf.sprintf "(default stages:%s%s%s%s%s%s%s)\n"
      (if !doMerge then " merge" else " (no merge)")
      (if !Cc_args.doCxxPP then " cxxpp" else " (no cxxpp)")
      (if !doGlobInit then " globinit" else " (no globinit)")
      (if !doInfer then " infer" else " (no infer)")
      (if !doCure then " cure" else " (no cure)")
      (if !doTransform then " transform" else " (no transform)")
      (if !doOpt then " opt" else " (no opt)")
  in

  let argDescr = Ciloptions.options @
    [
    (* Stage Control Options *)
    "", Arg.Unit (fun () -> ()), "\n\n\n\t*****  CCured Options  *****\n" ;
    "", Arg.Unit (fun () -> ()), "\n\t\tStage Control Options\n"
    ^ default_stages;

    "--stages", Arg.Unit (fun _ -> Cilutil.printStages := true),
        "print the stages of CCured as they happen";
    "--noMerge", Arg.Unit (fun () -> doMerge := false),
        "do not merge multiple input files" ;
    "--noCxxPP", Arg.Unit (fun () -> Cc_args.doCxxPP := false),
        "do not preprocess C++ files prior to curing" ;
    "--noGlobInit", Arg.Unit (fun () -> doGlobInit := false),
        "do not pull out global initializers" ;
    "--noInfer", Arg.Unit (fun () -> doInfer := false),
        "do not infer pointer annotations" ;
    "--noCure", Arg.Unit (fun () -> doCure := false),
        "do not instrument the code with run-time safety checks" ;
    "--noTransform", Arg.Unit (fun () -> doTransform := false),
        "do not transform (e.g., logcalls) the code" ;
    "--noOpt", Arg.Unit (fun () -> doOpt := false),
        "do not optimize the instrumented code" ;

    "--doMerge", Arg.Unit (fun () -> doMerge := true),
        "do merge multiple input files" ;
    "--doCxxPP", Arg.Unit (fun () -> Cc_args.doCxxPP := true),
        "preprocess C++ files prior to curing" ;
    "--doGlobInit", Arg.Unit (fun () -> doGlobInit := true),
        "do pull out global initializers" ;
    "--doInfer", Arg.Unit (fun () -> doInfer := true),
        "do infer pointer annotations" ;
    "--doCure", Arg.Unit (fun () -> doCure := true),
        "do instrument the code with run-time safety checks" ;
    "--doTransform", Arg.Unit (fun () -> doTransform := true),
        "do transform (e.g., logcalls) the code" ;
    "--doOpt", Arg.Unit (fun () -> doOpt := true),
        "do optimize the instrumented code" ;

    "--onlyMerge", Arg.Unit (fun () -> doNothing () ; doMerge := true),
        "only merge the input files" ;
    "--onlyGlobInit", Arg.Unit (fun () -> doNothing () ; doGlobInit := true),
        "only pull out global initializers" ;
    "--onlyInfer", Arg.Unit (fun () -> doNothing () ; doInfer := true),
        "only inter pointer annotations" ;
    "--onlyCure", Arg.Unit (fun () -> doNothing () ; doCure := true),
        "only instrument the code" ;
    "--onlyTransform", Arg.Unit (fun () -> doNothing () ; doTransform := true),
        "only transform (e.g., logcalls) the code" ;
    "--onlyOpt", Arg.Unit (fun () -> doNothing () ; doOpt := true),
        "only optimize the instrumented code" ;

    (* Output Channel Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tOutput Options\n(you may specify '-' or 'stdout' for output file names)\n" ;

    "--out", Arg.String (outChannel "default" defaultChannel) ,
        "the name of the final result file" ;
    "--cilout", Arg.String (outChannel "cil" cilChannel) ,
        "the name of the cil file (or merged file, if many input files)" ;
    "--mergedout", Arg.String (outChannel "merger" mergeChannel) ,
        "the name of the merged file" ;
    "--cxxppout", Arg.String (outChannel "cxxpp" cxxppChannel) ,
        "the name of the preprocessed C++ file" ;
    "--globinitout", Arg.String (outChannel "globinit" globinitChannel) ,
        "the name of the global-initializer-containting file" ;
    "--inferout", Arg.String (fun s -> Ptrnode.inferFile := Some s) ,
        "the name of the inference file (with graph)" ;
    "--browserout", Arg.String (fun s -> Ptrnode.browserFile := Some s) ,
        "the name of the inference browser directory" ;
    "--curedout", Arg.String (outChannel "cure" cureChannel) ,
        "the name of the cured file" ;
    "--optimout", Arg.String (fun s ->
                                optimOutFileName := s;
                                doOpt := true;
                                outChannel "optim" optChannel s) ,
        "the name of the optimized cured file" ;
    "--annout", Arg.String (outChannel "annotations" globAnnChannel) ,
        "list the annotations that would be needed for separate compilation in this file." ;

    (* General Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tGeneral Options\n" ;
    "--logscalars", Arg.Unit (fun _ -> Curechecks.logScalars := true),
               "produce a run-time log with all scalar casts";
    "--recurse",    Arg.Int (fun n -> (ignore (recursiveAddThing n)); ()),
                      "<n>: deliberately make stack grow to O(n) bytes";
    "--libdir", Arg.String (fun s -> Cc_args.libDir := s),
                      "<s>: set the name of the CCured library directory";
    "--listnonsafe", Arg.Unit (fun _ -> doListNonSafe := true),
                       ("List all of the function types, global vars, and "
                        ^"inner pointers that are not SAFE and may need "
                        ^"Deputy annotation.");

    (* Merging Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tMerging Options\n" ;

    "--mergeKeepAnnotations", Arg.Unit (fun _ -> mergeOutputHasAnnotations := true),
                ": merger output retains CIL pragmas and attributes";

    (* Globinit Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tGlobal Initializer Options\n" ;

    "--entryPoint", Arg.String (fun s -> Globinit.mainname := s),
                     "<xxx> call globinit from program entry point xxx";

    (* Inference Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tPointer-Qualifier Inference Options\n" ;

    "--nocure", Arg.Unit (fun _ -> doInfer := false; doCure := false),
    "Do not cure";
    "--allwild", Arg.Unit (fun _ -> doInfer := true; doCure := true;
                                    Ptrnode.use_wild_solver := true),
    "Infer all pointers to be WILD";
    "--boxdefaultwild", Arg.Unit (fun _ -> Ptrnode.defaultIsWild := true),
                       "the default pointer qualifier is wild";
    "--noRTTI", Arg.Unit (fun _ -> Ptrnode.useRTTI := false),
                       "turn off the use of RTTI";
    "--noFSEQ", Arg.Unit (fun _ -> Ptrnode.useFSEQ := false),
                       "do not use FSEQ pointers";
    "--noWILD", Arg.Unit (fun _ -> Solver.noteAndIgnoreBadCasts := true),
                       "do not use Wild pointers";
    "--noStrings", Arg.Unit (fun _ -> Ptrnode.useStrings := false),
                       "do not treat null-terminated strings specially";
    "--noExtendStringBuffer",
    Arg.Unit (fun _ -> Ptrnode.extendStringBuffers := false),
                       "do not expand string buffers with the null char";
    "--noOverride", Arg.Unit (fun _ -> Ptrnode.allowOverride := false),
                       "do not override user-specified pointer kinds";
    "--stripASM", Arg.Unit (fun _ -> stripASM := true),
                       "remove inline assembly statements";
    "--assumePrintf", Arg.Unit (fun _ -> Vararg.assumePrintf := true),
                       "assume all vararg functions are like printf";

    "--maxSplit", Arg.Unit (fun _ -> maxSplit := true),
      "Make as many pointer as possible compatible.";
    "--typecheck", Arg.Unit (fun _ -> typecheck := true),
                     "turns on consistency checking of CCured types";

    (* Curing Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tCuring Options\n" ;

    "--wildUntaggedFns", Arg.Unit
      (fun _ -> Ptrnode.wild_solve_untagged_functions := true),
                 "force all functions untagged when curetype=wild";

    "--wildTagAllFns", Arg.Unit
      (fun _ -> Ptrnode.wild_solve_tag_all_functions := true),
                 "force all functions (except main) to be tagged when curetype=wild";
    "--wildTagTheseFns", Arg.String
      (fun fname -> Solveutil.readTagFunctionFile fname),
                 "<fname>: this file lists, one per line, functions to make tagged";
    "--noStackChecks", Arg.Unit (fun _ -> Curechecks.stackChecks := false),
                     "turns off storing-local-variable checks";
    "--noReturnStackChecks", Arg.Unit (fun _ -> Curechecks.returnStackChecks := false),
                     "turns off returning-local-variable checks";

    "--noStackOverflowChecks",
                   Arg.Unit (fun _ -> Markptr.noStackOverflowChecks := true),
                   "turn off the stack overflow checks";
    "--noUnrefPointerChecks",
         Arg.Unit (fun _ -> Cure.noUnrefPointerChecks := true),
         "reduced checking for operations on pointers that are not referenced";
    "--allowPartialElementsInSequence",
         Arg.Unit (fun _ -> Ptrnode.allowPartialElementsInSequence := true),
         "do not check that sequences have a whole number of elements. This slows down the bounds checks though";
    "--allowInlineAssembly",
         Arg.Unit (fun _ -> Ptrnode.allowInlineAssembly := true),
         "allow (unsound) handling of inline assembly";

    "--cxxDumpClasses",
         Arg.Unit (fun _ -> Cxxpp.doDumpClasses := true),
         "dump the class information during cxxpp";

    "--shallowMangling",
         Arg.Unit (fun _ -> Markutil.shallowMangling := true),
         "use shallow mangling of globals";
    "--showMangleReasons",
         Arg.Unit (fun _ -> Cure.showMangleReasons := true),
         "When a global name is mangled, say what nodes caused it.";

    "--typeSizeCheck",
         Arg.Unit (fun _ -> doTypeSizeCheck := true),
         "check and print which types have changed after curing";
    "--alwaysStopOnError",
         Arg.Unit (fun _ -> Markutil.alwaysStopOnError := true),
         "Stop execution when a run-time check fails.";
    "--failIsTerse",
         Arg.Unit (fun _ -> Markutil.failIsTerse := true),
         "when a run-time check is triggered do not print location information.";
    "--logNonPointers",
         Arg.Unit (fun _ -> Markutil.logNonPointers := true),
         "attempt to identify at run-time where a non-pointer originates";

    (* Browser options *)
    "--browserSourceFileSize",
         Arg.Int (fun n -> Ptrnode.browserSourceFileSize := n),
         "the size of a source-file fragment for the browser (roughly in statements)";
    "--browserNodeFileSize",
         Arg.Int (fun n -> Ptrnode.browserNodeFileSize := n),
         "the size of a node-file fragment for the browser (roughly in nodes)";

    "--emitGraphDetailLevel",
         Arg.Int (fun n -> Ptrnode.emitGraphDetailLevel := n),
         Ptrnode.graphDetailLevelLegend;

    (* Transformation Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tTransformation Options\n" ;
    "--logwrites", Arg.Unit (fun _ -> Cc_args.logWrites := true),
          "turns on generation of code to log memory writes calls in CIL";
    "--makeCFG", Arg.Unit (fun _ -> make_cfg := true),
          "make the file look more like a CFG";
    "--astslicerList", Arg.String (fun s ->
        doASTSlicerEnumerate := Some(s)),
          "<fname>: enumerate AST slicer points to file <fname>";
    "--astslicerAnnotate", Arg.Unit (fun _ -> doASTSlicerAnnotate := true),
          "annotate AST slicer points (cf. logcalls)";
    "--astslicerKeep", Arg.String (fun s -> astslicerKeep := Some(s)),
          "keep the AST slicer points listed in this file";
    "--astslicerDrop", Arg.String (fun s -> astslicerDrop := Some(s)),
          "keep the AST slicer points listed in this file";
    "--astslicer", Arg.Unit (fun _ -> doASTSlicer := true),
          "perform AST slicing";
    "--simplemem", Arg.Unit (fun _ -> doSimplemem := true),
          "simplify memory operations";
    "--partial", Arg.Unit (fun _ -> doPartial := true),
          "partial evaluation and constant folding optimizations";
    "--verann", Arg.Unit (fun _ -> Markutil.doAnnotateOutput := true),
          "Annotate the output";

    (* Optimization Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tOptimization Options\n" ;
    "--noSplitPointers", Arg.Unit (fun _ -> Curesplit.dontSplit := true),
                   "Turn off splitting of fat pointers";
    "--optimelimall",
                   Arg.String (fun s -> optimElimAll := s :: !optimElimAll),
                   "Produce several variants of optimized code";
    "--elimabc", Arg.Unit (fun _ -> doElimabc := true),
           "attempt to eliminate redundant array bounds checks";
    "--elimabcgraph", Arg.Unit (fun _ -> Elimabc.dumpvargraph := true),
           "dump variable graph from elimabc phase (useful for debugging)";

    (* Parsing Options *)
    "", Arg.Unit (fun () -> ()), "\n\t\tParsing Options\n" ;

    (* MISC options *)
    "--dumpFCG", Arg.Unit (fun _ -> dumpFCG := true),
    "dump the function call graph";

  ] @ F.args in
  let usageMsg = "Usage: ccured [options] source-files" in

  Stats.reset Stats.SoftwareTimer; (* No performance counters *)
(*  Formatcil.test (); *)
  Arg.parse argDescr Ciloptions.recordFile usageMsg;
  Cil.initCIL ();
  Type.init ();
(*
  XXX: Why is this needed?  It causes CIL to barf, since these symbols
  also come in via ccuredcheck.h.  Commenting out for now.

  (* Now change the type of some builtins for CCured *)
  Hashtbl.add Cil.gccBuiltins
    "GCC_VARARGS_START" (Cil.ulongType, [ ], false);
  Hashtbl.add Cil.msvcBuiltins
    "GCC_VARARGS_START" (Cil.ulongType, [ ], false);
  Hashtbl.add Cil.gccBuiltins
    "GCC_STDARG_START" (Cil.ulongType, [ ], false);
  Hashtbl.add Cil.msvcBuiltins
    "GCC_STDARG_START" (Cil.ulongType, [ ], false);
*)
  let files = List.rev !Ciloptions.fileNames in

  (**********************************************************************
   * STAGE 1
   *
   * Parse input files into CIL.
   **********************************************************************)
  if !E.verboseFlag then ignore (E.log "Using CCured %s\n"
                                   Ccuredversion.ccuredVersion);
  if !Cilutil.printStages then ignore (E.log "Stage 1: Parsing\n") ;
  let cils = Stats.time "parsing" (fun () ->
    List.map parseOneFile files) () in

  let send_merged_output_to_cilChannel = ref false in

  begin
    match cils, !cilChannel with
    | _, None -> ()
    | [one], Some(x,fname,bin) ->
        if not !Rmtmps.keepUnused then begin
          if !Cilutil.printStages then
            ignore (E.log "Stage 1.1: Removing unused temporaries\n") ;
          (trace "sm" (dprintf "removing unused temporaries\n"));
          Rmtmps.removeUnusedTemps one;
        end;
        let oldpci = !C.print_CIL_Input in
        (trace "sm" (dprintf "printing file with CIL annotations\n"));
        C.print_CIL_Input := oldpci; (* Leave alone this one *)
        if bin then
          Stats.time "save binary file" (Cil.saveBinaryFileChannel one) x
        else
          Stats.time "printCil" (C.dumpFile C.defaultCilPrinter x fname) one;
        C.print_CIL_Input := oldpci
    | many, Some x -> send_merged_output_to_cilChannel := true
  end ;

  (**********************************************************************
   * STAGE 2
   *
   * Merge input files into one file.
   **********************************************************************)
  let merged : Cil.file = Stats.time "merge" (fun () ->
    match !doMerge, cils with
  | _, [] -> E.s (E.error "No arguments\n")
  | _, [one] -> one
  | false, lst -> E.s (E.error "Too many input files with no merging")
  | true, lst ->
      if !Cilutil.printStages then ignore (E.log "Stage 2: Merging\n") ;
      Mergecil.merge lst "merged"
  ) () in

  (**********************************************************************
   * STAGE 2.1
   *
   * Merge input files into one file.
   **********************************************************************)
  if not !Rmtmps.keepUnused then begin
    if !Cilutil.printStages then
      ignore (E.log "Stage 2.1: Removing unused temporaries\n") ;
    (trace "sm" (dprintf "removing unused temporaries\n"));
    Rmtmps.removeUnusedTemps merged;
  end;

  let withOrWithout:string =
    if !mergeOutputHasAnnotations then "with" else "without" in

  if !send_merged_output_to_cilChannel then begin
    match !cilChannel with
      None -> ()
    | Some(x,fname,bin) ->
      let oldpci = !C.print_CIL_Input in
      (trace "sm" (dprintf "printing merged file %s CIL annotations\n"
                           withOrWithout));
      C.print_CIL_Input := !mergeOutputHasAnnotations;
      if bin then
        Stats.time "save binary file" (Cil.saveBinaryFileChannel merged) x
      else
        Stats.time "printCil" (C.dumpFile C.defaultCilPrinter x fname) merged;
      C.print_CIL_Input := oldpci
  end ;
  begin
    match !mergeChannel with
      None -> ()
    | Some(x,fname,bin) ->
      let oldpci = !C.print_CIL_Input in
      (trace "sm" (dprintf "printing merged file %s CIL annotations\n"
                           withOrWithout));
      C.print_CIL_Input := !mergeOutputHasAnnotations;
      if bin then
        Stats.time "save binary file" (Cil.saveBinaryFileChannel merged) x
      else
        Stats.time "printCil" (C.dumpFile C.defaultCilPrinter x fname) merged;
      C.print_CIL_Input := oldpci
  end ;
  (* See if we had errors *)
  if !E.hadErrors then
    E.s (E.error "We had errors during removal of unused temporaries\n");

  (**********************************************************************
   * STAGE 3
   *
   * Preprocess the C++ features
   **********************************************************************)
  let cxx =
    if !Cc_args.doCxxPP then begin
      if !Cilutil.printStages then ignore (E.log "Stage 3: Preprocess C++\n") ;
      let cxx = Stats.time "CXXPP" Cxxpp.cxxFile merged in
      (match !cxxppChannel with
        None -> ()
      | Some(x,fname,bin) ->
          (trace "sm" (dprintf "printing preprocessed C++ file with CIL annotations\n"));
          let oldci = !C.print_CIL_Input in C.print_CIL_Input := true;
          if bin then
            Stats.time "save binary file" (Cil.saveBinaryFileChannel cxx) x
          else
            Stats.time "printCil" (C.dumpFile C.defaultCilPrinter x fname) cxx;
          C.print_CIL_Input := oldci);
      (* See if we had errors *)
      if !E.hadErrors then
        ignore (E.warn "We had errors during CXXPP\n");
      cxx
    end else merged
  in

  if !dumpFCG then
    Stackoverflow.makeAndDumpFunctionCallGraph cxx;

  (**********************************************************************
   * STAGE 4
   *
   * Pull out global initializers (and inline assmebly, if desired)
   **********************************************************************)
  let globinit = match !doGlobInit with
    true ->
      if !Cilutil.printStages then ignore (E.log "Stage 4: Glob-Init\n") ;
      Globinit.doFile cxx
  | false -> cxx
  in

  begin
    match !globinitChannel with
      None -> ()
    | Some(x,fname,bin) ->
        (trace "sm" (dprintf "printing globinit file with CIL annotations\n"));
        if bin then
          Stats.time "save binary file" (Cil.saveBinaryFileChannel globinit) x
        else
          Stats.time "printCil" (C.dumpFile Ptrnode.ccuredPrinter x fname) globinit;
  end ;

  let globinit = match !stripASM with
    true ->
      C.visitCilFileSameGlobals (new stripASMVisitor) globinit ;
      globinit

  | false -> globinit
  in

  if !Markutil.doAnnotateOutput then
    ( Stats.time "annotate-for-verify"  Verify.preprocess globinit);

  (**********************************************************************
   * STAGE 5
   *
   * Perform pointer qualifier inference.
   **********************************************************************)
  let infer = match !doInfer, !doCure with
    false, _ -> globinit
  | true, false -> globinit
  | true, _ -> begin
      if !Cilutil.printStages then ignore (E.log "Stage 5: Inference\n") ;
      (trace "sm" (dprintf "calling markptr\n"));
      if !Cilutil.printStages then ignore (E.log "Collecting constraints\n");
      let marked = Stats.time "markptr" Markptr.markFile globinit in
      (* Solve the graph *)
      if !Cilutil.printStages then ignore (E.log "Solving constraints\n");
      (trace "sm" (dprintf "invoking the solver\n"));
      (Ccutil.tryFinally
         (fun _ ->
           Stats.time "solver"
             (fun graph ->
               if (!maxSplit) then begin
                 Solver.markAllSplit := true;
               end ;
               (* Here we actually call the solver *)
               let should_typecheck =
                 if !Ptrnode.use_wild_solver then
                   Solveutil.wild_solve graph
                 else
                   Solver.solve marked graph
               in
               if should_typecheck && not !typecheck then begin
                 ignore (E.warn "The inference results should be type-checked.")
               end ;
             ) Ptrnode.idNode
         )
         (* Now the finally clause *)
         (fun _ ->
           if !doCure then
             Stats.time "graphstats" Ptrnode.printGraphStats ();
           (match !Ptrnode.inferFile with
             None -> ()
           | Some f ->
               Stats.time "printInfer" (Ptrnode.printInfer f) marked);
           (match !Ptrnode.browserFile with
             None -> ()
           | Some(f)->
               Stats.time "printBrowser" (Ptrnode.printBrowser f) marked))
         )
        ();
      marked
  end
  in

  (* Stop if we had errors. We did not stop in markptr so that we can print
   * the browser *)
  if !E.hadErrors then
    E.s (E.error "Stop because we had errors in markptr or in the solver\n");
  if !typecheck then begin
    Stats.time "typecheck" Typecheck.typecheck_file infer
  end ;

  (* weimer: remember the size of types *)
  if !doTypeSizeCheck then
    Stats.time "type-size-check" Curestats.rememberTypeSizes infer;

  (* code to estimate what annotations would be needed to support
     separate compilation. *)
  (match !globAnnChannel with
     Some (c, _, _) -> Stats.time "describe-global-annot"
                      (Curestats.printGlobalAnnotations c) infer
   | None -> ());

  (* List each location that needs a Deputy annotation.  Unlike
     printGlobalAnnotations, this includes static functions and
     displays the results in a way that works with Emacs compile mode. *)
  if !doListNonSafe then
    Stats.time "list-non-safe" Curestats.listGlobalAnnotations infer;

  (**********************************************************************
   * STAGE 6
   *
   * Cure the program with run-time checks.
   **********************************************************************)

  if !E.hadErrors then
    E.s (E.error "Stop before curing because there were errors\n");
  let cured = match !doCure with
    false -> infer
  | true -> begin
      if !Cilutil.printStages then ignore (E.log "Stage 5: Curing\n") ;
      (trace "sm" (dprintf "invoking the boxer\n"));
      let cured = Stats.time "cure" Cure.cureFile infer in
      if !Cilutil.doCheck then
        ignore (CK.checkFile [CK.NoCheckGlobalIds] cured);

      if not !Rmtmps.keepUnused then begin
        if !Cilutil.printStages then
          ignore (E.log "Stage 5.1: Removing unused temporaries\n") ;
        (trace "sm" (dprintf "removing unused temporaries\n"));
        Rmtmps.removeUnusedTemps cured;
      end;
      if !Markutil.doAnnotateOutput then
        ( Stats.time "annotate-for-verify"  Verify.annotate cured);
      ignore (E.log "printing the cured file\n");
      begin
        match !cureChannel with
          Some(c,fname,bin) ->
            if bin then
              Stats.time "save binary file"
                (Cil.saveBinaryFileChannel cured) c
            else
              Stats.time "printCured" (C.dumpFile Ptrnode.ccuredPrinter c fname)
                cured;
        | None -> ()
      end ;
      ignore (E.log "finished printing the cured file\n");
      if !E.hadErrors then begin
        E.s (E.error "There were errors during curing\n");
      end;
      (trace "sm" (dprintf "cureer has finished\n"));
      cured
  end
  in

  (**********************************************************************
   * STAGE 7
   *
   * Program Transformations
   **********************************************************************)
  if !doTransform then begin
    if !Cilutil.printStages then ignore (E.log "Stage 6: Transformations\n") ;

    (* AST Slicer Stuff *)
    (match !doASTSlicerEnumerate with
      Some(s) ->
        begin
          let outchan = open_out s in
          let ei = Astslicer.enumerate outchan cured in
          close_out outchan ;
          if !doASTSlicerAnnotate then begin
            ignore (Astslicer.annotate cured ei )
          end
        end
    | None -> () ) ;
    if !doASTSlicer then begin
      let file_to_str_list ht value name =
        try
          let inchan = open_in name in
          while true do
            let this_string = input_line inchan in
            Hashtbl.add ht this_string value
          done
        with _ -> ()
      in
      let wanted = Hashtbl.create 511 in
      (match !astslicerKeep with
        Some(s) -> file_to_str_list wanted Astslicer.Wanted s
      | None -> ()) ;
      (match !astslicerDrop with
        Some(s) -> file_to_str_list wanted Astslicer.Unwanted s
      | None -> ()) ;
      ignore (Astslicer.mark_file cured wanted)
    end ;

    (* Other CIL Transforms *)
    if !doSimplemem then
      ignore (Simplemem.simplemem cured) ;
    if !Cc_args.logCalls then (
      (trace "sm" (dprintf "invoking logcalls on cured file\n"));
      Logcalls.feature.Feature.fd_doit cured
    );
    if !Cc_args.logWrites then
      Logwrites.feature.Feature.fd_doit cured;
    if !make_cfg then begin
      ignore (Partial.calls_end_basic_blocks cured) ;
      ignore (Partial.globally_unique_vids cured) ;
      Cil.iterGlobals cured (fun glob -> match glob with
        Cil.GFun(fd,_) -> Cil.prepareCFG fd ;
                      ignore (Cil.computeCFGInfo fd true)
      | _ -> ()) ;
    end ;
    if !doPartial then
      ignore (Stats.time "partial-eval" Partial.partial cured "main" []) ;
  end ;

  (**********************************************************************
   * STAGE 8
   *
   * Optimize the cured output.
   **********************************************************************)
  let optim = match !doOpt with
    false -> cured
  | true -> begin
      if !Cilutil.printStages then ignore (E.log "Stage 7: Optimization\n") ;
      (trace "sm" (dprintf "invoking the optimizer\n"));
      Optim.checkToRemove := None;
      let optimized1 = Stats.time "Optim" Seoptim.optim cured in
      let optimized2 = Stats.time "Optim" Choptim.optim optimized1 in
      let optimized3 = Stats.time "Optim" Optim.optimFile optimized2 in
      ignore (E.log "Optim.ml optimizer statistics : %t\n" Optim.getStatistics);
      let optimized4 = if (not !doElimabc) then optimized3 else begin
        Stats.time "pointer analysis" Ptranal.analyze_file optimized3;
        Stats.time "pointer analysis" Ptranal.compute_results true; (*false; *)
        Stats.time "elimabc" Elimabc.elimabcFile optimized3
      end in

      begin
        match !optChannel with
          None -> ()
        | Some(c,fname,bin) ->
            if bin then
              Stats.time "save binary file"
                (Cil.saveBinaryFileChannel optimized4) c
            else
              Stats.time "printOptim"
                (C.dumpFile Ptrnode.ccuredPrinter c fname) optimized4;
      end ;
      (* Return the optimized version *)
      optimized4
    end
  in

  if !E.verboseFlag || !Cc_args.printStats then begin
    Curestats.printChecks cured;
  end;

  (* Now see if we must also produce a number of optimizer variants *)
  List.iter
    (fun name ->
      let toremove =
        if name = "CHECKS" then "" (* remove all *)
        else "CHECK_" ^ name
      in
      (* Find the new file name *)
      let newname =
        if Filename.check_suffix !optimOutFileName ".c" then
          (Filename.chop_suffix !optimOutFileName ".c")
          ^ ".no" ^ name ^ ".c"
        else
          E.s (E.bug "doOneVariant: wrong suffix in ouput file name (%s)"
                 !optimOutFileName)
      in
      (* Make a private copy of the file *)
      let copyGlobal = function
          C.GFun (fd, l) ->
            C.GFun (C.copyFunction fd fd.C.svar.C.vname, l)
        | g -> g
      in
      let copy =
        { optim with
               C.globals = List.map copyGlobal optim.C.globals;
               C.globinit =
                match optim.C.globinit with
                   None -> None
                 | Some g -> Some (C.copyFunction g
                                     g.C.svar.C.vname)} in
      if toremove = "" then
        Seoptim.forcefullyRemoveAll := true
      else
        Seoptim.forcefullyRemove := [toremove];

      Optim.checkToRemove := Some toremove;
      if !E.verboseFlag then
        ignore (E.log " removing checks: %s\n" toremove);
      let removed = Seoptim.optim copy in
      let variant_out = open_out newname in
      C.dumpFile Ptrnode.ccuredPrinter variant_out newname removed;
      close_out variant_out)
    !optimElimAll;

  if !Cilutil.printStages then ignore (E.log "CCured complete\n");
  (* weimer: check those types *)
  if !doTypeSizeCheck then
    ignore (Stats.time "type-size-check" Curestats.checkTypeSizes optim);

  begin
    match !defaultChannel with
      None -> ()
    | Some(x,fname,bin) ->
        (trace "sm" (dprintf "printing final file with CIL annotations\n"));
        if bin then
          Stats.time "save binary file" (Cil.saveBinaryFileChannel optim) x
        else
      Stats.time "printCil" (C.dumpFile Ptrnode.ccuredPrinter x fname) optim;
  end ;
  ()
end ;;

(* this mystery code was copied from George's original main.ml *)
let failed = ref false
let wrapMain () =
  (* This code implements a "try finally clause". We first run the "main" and
   * we produce a continuation *)
  Printexc.record_backtrace true;
  let term =
    try
      main ();
      (* Main did not throw an exception. The continuation just exits *)
      fun () -> exit (if !failed then 1 else 0)
    with e ->
      (* Main did throw an exception. Print a message about it and then exit *)
      (fun () ->
        let exc = Printexc.get_backtrace () in
        print_string ("Uncaught exception: " ^ (Printexc.to_string e)
                      ^ "\n");
        print_string exc;
        exit 2)
  in
  begin
    if !E.verboseFlag || !Cc_args.printStats then
      Stats.print stderr "Timings:\n";
    if !E.logChannel != stderr then
      close_out (! E.logChannel);
    (match ! cilChannel with Some (c,_,b) -> close_out c | _ -> ());
    (match ! mergeChannel with Some (c,_,b) -> close_out c | _ -> ());
    (match ! globinitChannel with Some (c,_,b) -> close_out c | _ -> ());
    (match ! cureChannel with Some (c,_,b )-> close_out c | _ -> ());
    (match ! optChannel with Some (c,_,b )-> close_out c | _ -> ());
    (match ! globAnnChannel with Some (c,_,b) -> close_out c | _ -> ());
    (match ! defaultChannel with Some (c,_,b )-> close_out c | _ -> ());

    term ()
  end
;;

wrapMain ()
;;
