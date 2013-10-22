
val doit: Cil.file -> unit

(* for use by verify.ml: *)
val metaFields: (int * string, Cil.fieldinfo) Hashtbl.t


(* These functions are exposed for use by depfunc.ml,
   which does a similar transformation for function args.
   See dependent.ml for descriptions. *)
val getHelperFunction: string -> Cil.varinfo
val readAttrs: doit:(Cil.attrparam -> 'a) -> default:'a -> Cil.typ -> 'a
val compileAttribute:
  ((string * Cil.exp) list) -> this: string -> Cil.attrparam
  -> (string list * Cil.exp)
val moveSizeCountAttrs: Cil.attributes -> Cil.typ -> (Cil.attributes * Cil.typ)
