open Core

module type S = sig
  type t [@@deriving quickcheck, eq, sexp, compare]
  module V : sig
    type t
    [@@deriving sexp, compare, hash, equal]
    val to_string : t -> string
    val get_id : t -> int
    val is_explodable : t -> bool
    val explode : t -> t list list
  end
  module E : sig type t end
  module G : sig
    type t
    val succ : t -> V.t -> V.t list
  end
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val skip : t
  val pass : t
  val dead : t
  val abort : t
  val zero : t
  val one : t
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
  val sequence : t list -> t
  val seq : t -> t -> t
  val choices : t list -> t
  val choice : t -> t -> t
  val choice_seq : t list -> t list -> t
  val choice_seqs : t list list -> t
  val is_primitive : t -> bool
  val subst : Var.t -> Expr.t -> t -> t
  val normalize_names : t -> t
  val dnf : t -> t
  val count_paths : t -> Bigint.t
  val paths : t -> t Sequence.t
  val construct_graph : t -> G.t
  val of_graph : G.t -> t
  val print_graph : G.t -> string option -> unit
  val count_cfg_paths : G.t -> Bigint.t
  val find_source : G.t -> V.t
  val vertex_to_cmd : V.t -> t

  val optimize : t -> t
  val optimize_seq_pair : (t * t) -> (t * t)
end
