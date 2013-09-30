

(** Initialize the tagegd union module *)
val init: unit -> unit

val markUnionComp: Cil.compinfo -> Cil.location -> unit

val processTaggedUnions: Cil.file -> unit
val processTaggedUnionsAfterMarking: Cil.file -> unit

(* At the end of solving, strip Rtti from the fields of tagged unions.
   RTTI info is stored separately, as the union's tag, so fields don't need
   the kind RTTI. *)
val removeRttiFromFields: unit -> unit

(* If lv.f is a __data field of a tagged union, 
   "tagForDataField lv f" returns lv.__tag
   Otherwise, returns None*)
val tagForDataField: Cil.lval -> Cil.fieldinfo -> Cil.lval option
