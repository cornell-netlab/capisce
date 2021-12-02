type t [@@deriving eq, sexp, compare, quickcheck]

val enable_smart_constructors : [`On | `Off] ref
   
val (=) : t -> t -> bool
   
val false_ : t
val true_ : t

(*Unary Operations*)
val not_ : t -> t

(* Binary Operations *)  
val and_ : t -> t -> t
val or_ : t -> t -> t
val imp_ : t -> t -> t
val iff_ : t -> t -> t

(* Comparisons *)
val eq_ : Expr.t -> Expr.t -> t
val ult_ : Expr.t -> Expr.t -> t
val ule_ : Expr.t -> Expr.t -> t
val ugt_ : Expr.t -> Expr.t -> t
val uge_ : Expr.t -> Expr.t -> t
val slt_ : Expr.t -> Expr.t -> t
val sle_ : Expr.t -> Expr.t -> t
val sgt_ : Expr.t -> Expr.t -> t
val sge_ : Expr.t -> Expr.t -> t
  
(* Quantifiers *)
val forall : Var.t list -> t -> t
val exists : Var.t list -> t -> t

val to_smtlib : t -> string
val subst : Var.t -> Expr.t -> t -> t
val vars : t -> Var.t list * Var.t list
                  
val index_subst : Subst.t option -> t -> t

val simplify : t -> t
val size : t -> int  
val qf : t -> bool
val well_formed : t -> bool                       

val equivalence : t -> t -> t                         

(* FOR TESTING PURPOSES ONLY *)
val dumb : (unit -> t) -> t
