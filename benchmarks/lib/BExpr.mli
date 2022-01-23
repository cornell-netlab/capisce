open Core
open Base_quickcheck
   
type t [@@deriving eq, sexp, compare, quickcheck]

val to_smtlib : t -> string
val of_smtlib : ?cvs:Var.t list -> string -> t
val of_smtast : ?cvs:Var.t list -> SmtAst.t list -> t  

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

val ands_ : t list -> t
val ors_ : t list -> t
val imps_ : t list -> t
  
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

val subst : Var.t -> Expr.t -> t -> t
val fun_subst : (Var.t -> Expr.t) -> t -> t
(** [fun_subst f b] substitutes b according to function [f] *)  

val one_point_rule : Expr.t -> Expr.t -> t -> t
  
val vars : t -> Var.t list * Var.t list
val compute_vars : t -> Var.t list * Var.t list  
                  
val index_subst : Subst.t option -> t -> t

val simplify : t -> t
val nnf : t -> t
val cnf : t -> t  
val normalize_names : t -> t   
val size : t -> int  
val qf : t -> bool
val well_formed : t -> bool
val get_conjuncts : t -> t list
  
val label : Context.t -> t -> t

val equivalence : t -> t -> t

(* Solver-Aided functions *)
val check_iff : t -> t -> bool
val check_iff_str : ?timeout : int option -> t -> t -> string  
val check_sat : ?timeout : int option -> Var.t list -> t -> bool
val z3_simplify : Var.t list -> t -> t  

val predicate_abstraction : t -> t
val abstract_qvars : t -> string

  
val qf_quickcheck_generator : t Generator.t
  
  
(* FOR TESTING PURPOSES ONLY *)
val dumb : (unit -> t) -> t
