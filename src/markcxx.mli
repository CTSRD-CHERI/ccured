
(** Add edges corresponding to the method overrides *)
val fixOverrides: unit -> unit

val fixFunctionPointerVar: Cil.varinfo -> Cil.location -> unit
