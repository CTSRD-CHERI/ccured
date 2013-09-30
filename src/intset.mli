type set = int array
val bitsPerInt : int
val index : int -> int * int
val empty : unit -> set
val singleton : int -> set
val equal : set -> set -> bool
val dextend : set -> int -> set
val dinsert : set -> int -> unit
val insert : set -> int -> set
val union2 : set * set -> set
val union : set list -> set
val intersect2 : set * set -> set
val intersect : set -> set list -> set
val dremove : set -> int -> unit
val remove : set -> int -> set
val iter : (int -> unit) -> set -> unit
val toList : set -> int list
val fromList : int list -> set
val contains : set -> int -> bool
val difference : set * set -> set
val fold : (int -> 'a -> 'a) -> set -> 'a -> 'a
val shrink : set -> int -> set
