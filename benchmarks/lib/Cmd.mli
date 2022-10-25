open Primitives

module GCL : sig
  include Cmd_intf.S
  val assign : Var.t -> Expr.t -> t
  val wp : t -> BExpr.t -> BExpr.t
  val const_prop : t -> t
  val vc : t -> BExpr.t
end

module PassiveGCL : sig
  include Cmd_intf.S
  val normal : t -> BExpr.t
  val wrong : t -> BExpr.t
  val passify : GCL.t -> Context.t * t
  val assume_disjuncts : t -> t
  val remove_asserts : t -> t
  val vc : t -> BExpr.t
end

module GPL : sig
  include Cmd_intf.S
  val assign : Var.t -> Expr.t -> t
  val table : string -> Var.t list -> (Var.t list * (Action.t list)) list -> t
  val tables : t -> Table.t list
  val symbolize : t -> t
  val encode_tables : t -> GCL.t
  val induce : G.t -> (V.t list) -> G.t
  val print_key : G.t -> string
end

module TFG : sig
  include Cmd_intf.S
  val project : GPL.t -> t
  val inject : t -> GPL.t
  val print_key : G.t -> string
  val explode_random : t -> G.t option
  val cast_to_gpl_graph : G.t -> GPL.G.t
end

val vc : GCL.t -> BExpr.t
val induce_gpl_from_tfg_path : GPL.G.t -> TFG.V.t list -> GPL.G.t

module Concrete : sig
  (*Counter-Example Guided Path Exploration*)
  val slice : Model.t -> GCL.t -> GCL.t option
end


module Exploder : sig
  type t
  val create : unit -> t
  val arm : t -> Table.t -> unit
  val pop : t -> GPL.t -> GPL.t option
end
