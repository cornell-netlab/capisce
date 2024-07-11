open Primitives


(**
  The [Cmd.Make] functor generates IRs for nondeterminitistic code
  based on a set of core primitives defined by the parameter module
  [P], which must have module type [Primitive] defined in [Primitives]. 
*)
module Make : functor (P : Primitive) ->
 sig

  (** The type [t] describes the structure of commands.  *)
  type t =
    | Prim of P.t (** [Prim p] for a [p] of type [P.t] constructs a primitive action *)
    | Seq of t list (** [Seq cs] constructs an nary sequential composition *)
    | Choice of t list (** [Choice cs] constructs an n-ary nondeterministic composition*)
  [@@deriving quickcheck, eq, sexp, compare, hash]

  (** [assume b] is a core construct that can be constructed by any instance of [Cmd].
      In the IR semantics, [assume b] is a no-action when [b] evaluates to [true] and
      fails to terminate when [b] evaluates to [false]. 
    *)
  val assume : BExpr.t -> t

  (** [assert_ b] is a core construct that can be constructed by any instance of [Cmd].
    In the IR semantics, [assert_ b] is a no-action when [b] evaluates to [true] and
    crashes the program when [b] evaluates to [false]. 
  *)
  val assert_ : BExpr.t -> t

  (** [skip] is a command that does nothing *)
  val skip : t

  (** [pass] is a command that does nothing*)
  val pass : t

  (** [dead] marks the current execution unreachable
    * it is equivalent to [assume_ BExpr.false_]*)
  val dead : t

  (** [abort] fails the current execution *)
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
