module Make : functor
    ( WMake : functor (VV : sig type t [@@deriving sexp, compare] end)
        -> sig
        type t
        val create : unit -> t
        val push : t -> (VV.t list * VV.t list) -> unit
        val pop : t -> (VV.t list * VV.t list) option
      end )
    ( V : sig
        type t [@@deriving sexp, compare]
      end )
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
