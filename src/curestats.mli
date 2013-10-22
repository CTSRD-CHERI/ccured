

(* These are called when "--typeSizeCheck" is used.  Look for types whose sizes
   change. *)
val rememberTypeSizes: Cil.file -> unit
val checkTypeSizes: Cil.file -> unit

(* What annotations would be needed to support separate compilation?
   (here, we try to infer which globals are static.)*)
val printGlobalAnnotations: out_channel -> Cil.file -> unit

(* listGlobalAnnotations lists all of the annotations needed by Deputy.
   It's similar to printGlobalAnnotations, but it lists the results one
   at a time on stdout, and it includes even static globals. *)
val listGlobalAnnotations: Cil.file -> unit


(* Print how many of each check we use.
   Called when the "--stats" option is used. *)
val printChecks: Cil.file -> unit
