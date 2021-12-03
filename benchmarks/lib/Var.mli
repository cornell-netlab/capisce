open Base_quickcheck
   
type t [@@deriving compare, sexp]

val (=) : t -> t -> bool
val equal : t -> t -> bool
  
val dedup : t list -> t list
  
val make : string -> int -> t
val str : t -> string
val size : t -> int

val well_formed : t -> bool 
  
val is_ghost : t -> bool
val make_ghost : int -> t -> t   
val is_symbRow : t -> bool
val make_symbRow : int -> t -> t
val make_symbRow_str : string -> t -> t
val is_sym_of : sym:t -> data:t -> bool
(** [is_sym_of ~sym ~data] checks whether [sym] is the symbolic row variable for data plane variable ~data. In otherwords, ~sym represents the key that the controller matches on for ~data. *)  

val list_to_smtlib_quant : t list -> string
val list_to_smtlib_decls : t list -> string
                                       
val quickcheck_generator : t Generator.t
val quickcheck_observer : t Observer.t
val quickcheck_shrinker : t Shrinker.t
