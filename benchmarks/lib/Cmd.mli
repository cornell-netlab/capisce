open Primitives

module Make : functor (P : Primitive) ->
 sig

  type t =
    | Prim of P.t
    | Seq of t list
    | Choice of t list
  [@@deriving quickcheck, eq, sexp, compare, hash]

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
  val contra : t -> t -> bool
  val to_string : t -> string
  val size : t -> int
  val seq : t -> t -> t
  val sequence : t list -> t
  val sequence_opt : t option list -> t option
  val sequence_map : 'a list -> f:('a -> t) -> t
  val choice : t -> t -> t
  val choices : t list -> t
  val choices_map : 'a list -> f:('a -> t) -> t
  val choices_opt : t option list -> t option
  val choice_seq : t list -> t list -> t
  val choice_seqs : t list list -> t
  val is_primitive : t -> bool
  val vars : t -> Var.t list
end
