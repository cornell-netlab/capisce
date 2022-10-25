type t [@@deriving eq, sexp, hash, compare, quickcheck]

(* Constants *)
val bv : Bigint.t -> int -> t
val bvi : int -> int -> t

(* Constructor *)
val var : Var.t -> t
val is_var : t -> bool  
val get_var : t -> Var.t (* throws exception when not a var *)
val get_const : t -> Bigint.t option

val is_one : t -> bool
val is_zero : t -> bool  
  
(* Binary operators *)  
val band : t -> t -> t
val bor : t -> t -> t
val badd : t -> t -> t
val bmul : t -> t -> t
val bsub : t -> t -> t
val bxor : t -> t -> t  
val bconcat : t -> t -> t
val shl_ : t -> t -> t
val lshr_ : t -> t -> t
val ashr_ : t -> t -> t

(* n-ary operators *)
val nary : (t -> t -> t) -> t list -> t
  
(* Unary-ish Operators *)
val bnot : t -> t
val bcast : int -> t -> t
val bslice : int -> int -> t -> t

val eval : Model.t -> t -> (Bigint.t * int) option

val static_eq : t -> t -> bool option
val reassociate_bors : Var.t -> t -> (Var.t * t ) option  
val neq_contra : (t * t) -> (t * t) -> bool  
val subst : Var.t -> t -> t -> t
val vars : t -> Var.t list * Var.t list
val to_smtlib : t -> string
val coerce_types : TypeContext.t -> t -> t  

val index_subst : Subst.t option -> t -> t

val normalize_names : t -> t  

val uelim : [`Neq | `Eq] -> Var.t list -> t -> t -> bool
(** [uelim sign vs e1 e2] heuristically determines whether we can falsify [forall vs (e1 sign e2)] *)  
  
val well_formed : t -> bool
(** [well_formed e] returns true iff the variables are well-formed and no bitvector has negative length *)

val size : t -> int (* the ast size *)
val width : t -> int (* the bitwidth of the expr*)   
(** [size e] is the size of e's AST *)

val label : Context.t -> t -> t
(** [label ctx e] indexes the variables in [e] according to [ctx] *)              

val erase_max_label : Context.t -> t -> t
(** [erase_max_label ctx e] erases the variables from only the variables that are maximally indexed *)

val fun_subst : (Var.t -> t) -> t -> t
(** [fun_subst f e] substitutes [e] according to function [f] *)        
