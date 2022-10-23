module Make : functor
  (V : sig
         type t [@@deriving sexp, compare]
         val is_explodable : t -> bool
         val explode : t -> t list list
       end)
  (G : sig
         type t
         val find_source : t -> V.t
         val count_cfg_paths : t -> Bigint.t
         val succ : t -> V.t -> V.t list
       end)
  ->
  sig
    type t
    val graph : t -> G.t
    val create : G.t -> t
    val get_next : t -> V.t list option
    val total_paths : t -> Bigint.t
  end
