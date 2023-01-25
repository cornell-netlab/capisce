open Core
open Base_quickcheck
   
type t [@@deriving compare, hash, sexp]

val (=) : t -> t -> bool
val equal : t -> t -> bool
  
val dedup : t list -> t list
  
val make : string -> int -> t
val str : t -> string
val size : t -> int
val rename : t -> string -> t
(* [rename x s] is a new variable named [s] with the same size as [x]*)
val map : t -> f:(string -> string) -> t

val well_formed : t -> bool 

val normalize_name : t -> t 
  
val is_ghost : t -> bool
val make_ghost : int -> t -> t   
val is_symbRow : t -> bool
val make_symbRow : int -> t -> t
val make_symbRow_str : string -> t -> t
val is_sym_of : sym:t -> data:t -> bool
(** [is_sym_of ~sym ~data] checks whether [sym] is the symbolic row variable for data plane variable ~data. In otherwords, ~sym represents the key that the controller matches on for ~data. *)  

val list_to_smtlib_quant : t list -> string
val list_to_smtlib_decls : t list -> string

val sort : t list -> t list

val index : t -> int -> t
val is_indexed : t -> bool
val unindex : t -> (t * int) option
(* [unindex x] is Some (y,i) when (str x) == y$_$i *)

val quickcheck_generator : t Generator.t
val quickcheck_observer : t Observer.t
val quickcheck_shrinker : t Shrinker.t


module Set : Set.S with type Elt.t = t
module Map : Map.S with type Key.t = t
