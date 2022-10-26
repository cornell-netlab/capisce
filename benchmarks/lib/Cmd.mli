open Primitives

module Make : functor (P : Primitive) ->
 sig
  type t [@@deriving quickcheck, eq, sexp, compare]
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val skip : t
  val pass : t
  val dead : t
  val abort : t
  val zero : t
  val one : t
  val prim : P.t -> t
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
  val is_mult_unit : t -> bool
  val is_mult_annihil : t -> bool
  val is_add_unit : t -> bool
  val is_add_annihil : t -> bool
  val contra : t -> t -> bool
  val to_string_aux : int -> t -> string
  val to_string : t -> string
  val count_asserts_aux : t -> int -> int
  val count_asserts : t -> int
  val size : t -> int
  val seq : t -> t -> t
  val sequence : t list -> t
  val sequence_opt : t option list -> t option
  val choice : t -> t -> t
  val choices : t list -> t
  val choices_opt : t option list -> t option
  val choice_seq : t list -> t list -> t
  val choice_seqs : t list list -> t
  val is_primitive : t -> bool
  val dnf : t -> t
  val vars : t -> Var.t list

  val bottom_up :
    prim:(P.t -> 'a) ->
    sequence:('a list -> 'a) ->
    choices:('a list -> 'a)
    -> t
    -> 'a

  val top_down :
    init:'a ->
    prim:('a -> P.t -> 'a) ->
    sequence:('a -> t list -> ('a -> t -> 'a) -> 'a) ->
    choices:('a -> t list -> ('a -> t -> 'a) -> 'a)
    -> t
    -> 'a

  val forward :
    init:'a ->
    prim:('a -> P.t -> 'a) ->
    choices:('a list -> 'a)
    -> t
    -> 'a

  val backward :
    init:'a ->
    prim:(P.t -> 'a -> 'a) ->
    choices:('a list -> 'a)
    -> t
    -> 'a

  val optimize : t -> t
  val optimize_seq_pair : (t * t) -> (t * t)
end
