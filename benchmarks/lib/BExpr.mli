open Core
open Base_quickcheck
   
type bop =
  | LAnd
  | LOr
  | LArr
  | LIff
  [@@deriving eq, sexp, compare, quickcheck]

type comp =
  | Eq
  | Ult
  | Ule
  | Uge
  | Ugt
  | Slt
  | Sle
  | Sgt
  | Sge
  [@@deriving eq, sexp, compare, quickcheck]

type t = 
  | TFalse
  | TTrue
  | LVar of string
  | TNot of t 
  | TNary of bop * t list
  | TComp of comp * Expr.t * Expr.t
  | Forall of Var.t * t
  | Exists of Var.t * t
  [@@deriving eq, sexp, compare, quickcheck]

val to_smtlib : t -> string
(* val of_smtlib : ?cvs:Var.t list -> string -> t
 * val of_smtast : ?cvs:Var.t list -> SmtAst.t list -> t   *)

val enable_smart_constructors : [`On | `Off] ref
val q_count : Bigint.t ref
val incr_q : Var.t -> unit
val decr_q : Var.t -> string -> unit  
   
val (=) : t -> t -> bool
   
val false_ : t
val true_ : t

(*Unary Operations*)
val not_ : t -> t
val lvar : string -> t  

(* Binary Operations *)  
val and_ : t -> t -> t
val or_ : t -> t -> t
val imp_ : t -> t -> t
val iff_ : t -> t -> t
val get_smart : bop -> t -> t -> t
val get_smarts : bop -> t list -> t  

val ands_ : t list -> t
val ors_ : t list -> t
val imps_ : t list -> t
val iffs_ : t list -> t  
  
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
val subst_lvar : string -> t -> t -> t
val fun_subst_lvar : (string -> t) -> t -> t    
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
val coerce_types : TypeContext.t -> t -> t
val complete_predicate_abstraction : Var.t -> t -> t option
val get_atoms : t -> t list  
val get_equality :  t -> (Var.t * Expr.t) option
  
val label : Context.t -> t -> t

val comparisons : t -> (Var.t * Expr.t) list

val equivalence : t -> t -> t

val order_all_quantifiers : t -> t
  
(* Solver-Aided functions *)
(* val check_iff : t -> t -> bool
 * val check_iff_str : ?timeout : int option -> t -> t -> string  
 * val check_sat : ?timeout : int option -> Var.t list -> t -> bool
 * val z3_simplify : Var.t list -> t -> t   *)

(* Predicate Abstraction *)  
val predicate_abstraction : t -> t
val abstract_qvars : t -> string

  
val qf_quickcheck_generator : t Generator.t
  
  
(* FOR TESTING PURPOSES ONLY *)
val dumb : (unit -> t) -> t
