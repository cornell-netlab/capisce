type t [@@deriving eq, sexp, compare, quickcheck]

val bv : Bigint.t -> int -> t
val bvi : int -> int -> t  
val var : Var.t -> t
val band : t -> t -> t
val bor : t -> t -> t
val badd : t -> t -> t
val bmul : t -> t -> t
val bsub : t -> t -> t
val bneg : t -> t  

val static_eq : t -> t -> bool option  
val subst : Var.t -> t -> t -> t
val vars : t -> Var.t list * Var.t list
val to_smtlib : t -> string

val index_subst : Subst.t option -> t -> t

val uelim : [`Neq | `Eq] -> Var.t list -> t -> t -> bool
(** [uelim sign vs e1 e2] heuristically determines whether we can falsify [forall vs (e1 sign e2)] *)

val well_formed : t -> bool
(** [well_formed e] returns true iff the variables are well-formed and no bitvector has negative length *)

val size : t -> int
(** [size e] is the size of e's AST *)
