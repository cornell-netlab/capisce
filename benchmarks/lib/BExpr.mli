type t [@@deriving eq, sexp, compare, quickcheck]

val (=) : t -> t -> bool
   
val false_ : t
val true_ : t

val not_ : t -> t
val and_ : t -> t -> t
val or_ : t -> t -> t
val imp_ : t -> t -> t
val eq_ : Expr.t -> Expr.t -> t
val forall : Var.t list -> t -> t
val exists : Var.t list -> t -> t

val to_smtlib : t -> string
val subst : Var.t -> Expr.t -> t -> t
val vars : t -> Var.t list * Var.t list
                  
val index_subst : Subst.t option -> t -> t

val simplify : t -> t
val well_formed : t -> bool                       
