open Core

module type Primitive = sig
  type t [@@deriving quickcheck, eq, hash, sexp, compare]
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val contra : t -> t -> bool
  val to_smtlib : t -> string
  val count_asserts : t -> int
  val size : t -> int
  val subst : Var.t -> Expr.t -> t -> t
  val normalize_names : t -> t
  val comparisons : t -> (Var.t * Expr.t) list option
  val is_node : t -> bool
  val name : t -> string
  val is_table : t -> bool
end


module Pipeline : Primitive

module Action : sig
  include Primitive
  val assign : Var.t -> Expr.t -> t
end

module type CMD = sig
  type t [@@deriving quickcheck, eq, sexp, compare]
  module G : sig type t end
  module Vertex : sig type t end
  module Edge : sig type t end
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val skip : t
  val pass : t
  val dead : t
  val abort : t

  (* idempotent semiring *)
  val zero : t
  val one : t
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t (*note ( * ) is not reflexive *)
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
  val print_graph : G.t -> string option -> unit
  val count_cfg_paths : G.t -> Bigint.t
end


module GCL : sig
  include CMD
  val assign : Var.t -> Expr.t -> t
  val wp : t -> BExpr.t -> BExpr.t
  val const_prop : t -> t
  val optimize : t -> t
  val vc : t -> BExpr.t
end

module PassiveGCL : sig
  include CMD
  val normal : t -> BExpr.t
  val wrong : t -> BExpr.t
  val passify : GCL.t -> Context.t * t
  val assume_disjuncts : t -> t
  val vc : t -> BExpr.t
end

module GPL : sig
  include CMD
  module Vertex : sig type t = Pipeline.t * int end
  val assign : Var.t -> Expr.t -> t
  val table : string -> Var.t list -> (Var.t list * (Action.t list)) list -> t
  val symbolize : t -> t
  val encode_tables : t -> GCL.t
  val induce : G.t -> (Vertex.t list) -> G.t
  val of_graph : G.t -> t
  val print_key : G.t -> string
end

module TFG : sig
  include CMD
  module Vertex : sig type t = Pipeline.t * int end
  val project : GPL.t -> t
  val inject : t -> GPL.t
  val print_key : G.t -> string
end

val vc : GCL.t -> BExpr.t

module Generator : sig
  val graph : TFG.G.t option ref
  val create : TFG.t -> unit
  val get_next : unit -> (TFG.Vertex.t) list option
end

