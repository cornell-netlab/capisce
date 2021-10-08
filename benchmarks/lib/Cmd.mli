type t

val to_string : t -> string
   
val assume : BExpr.t -> t
val assert_ : BExpr.t -> t
val havoc : Var.t -> t
val assign : Var.t -> Expr.t -> t
val seq : t -> t -> t
val choice : t -> t -> t
val skip : t
val sequence : t list -> t
val choice_seq : t list -> t list -> t
(** [choice_seq c1 c2] is equivalent to [choice (sequence c1) (sequence c2) *)

val choice_seqs : t list list -> t
(** [choice_seqs] lifts [choice_seq] over lists*)  

val negate : t -> t
  
val subst : Var.t -> Expr.t -> t -> t  
val table : int -> Var.t list -> (Var.t * t) list -> t -> t

val wp : t -> BExpr.t -> BExpr.t                                                            

val assert_slices : t -> t list
