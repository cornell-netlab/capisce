open Core

type t [@@deriving quickcheck, eq, sexp, compare]

val to_string : t -> string
val size : t -> int
val count_asserts : t -> int  
   
val assume : BExpr.t -> t
val assert_ : BExpr.t -> t
val havoc : Var.t -> t
val assign : Var.t -> Expr.t -> t
val seq : t -> t -> t
val choice : t -> t -> t
val choices : t list -> t
val skip : t
val sequence : t list -> t
val choice_seq : t list -> t list -> t
(** [choice_seq c1 c2] is equivalent to [choice (sequence c1) (sequence c2)] *)

val choice_seqs : t list list -> t
(** [choice_seqs] lifts [choice_seq] over lists*)

val apply_smart_constructors : t -> t

val negate : t -> t
  
val subst : Var.t -> Expr.t -> t -> t  
val table : int -> Var.t list -> (Var.t option * t) list -> t
val full_table : string -> (int * Expr.t) list -> (string * t) list -> t

val dnf : t -> t
val wp : t -> BExpr.t -> BExpr.t
val wrong : t -> BExpr.t
val vc : t -> BExpr.t
val optimize : t -> t
val const_prop : t -> t
val dead_code_elim : t -> t
val passify : t -> t
val assume_disjuncts : t -> t

val paths : t -> t Sequence.t
val count_paths : t -> Bigint.t
val abstract : t -> NameGen.t -> t * NameGen.t
val collect_action_vars : t -> Var.t list
val action_var_paths : t -> Bigint.t

val normalize_names : t -> t

