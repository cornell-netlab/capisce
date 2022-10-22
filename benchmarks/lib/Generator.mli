module Make : functor
  (V : sig
         type t
         val t_of_sexp : Sexplib0.Sexp.t -> t
         val sexp_of_t : t -> Sexplib0.Sexp.t
         val compare :
           t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
       end)
  (G : sig
         type t
         val find_source : t -> V.t
         val count_cfg_paths : t -> Bigint.t
         val succ : t -> V.t -> V.t list
       end)
  ->
  sig
    val graph : G.t option ref
    val create : G.t -> Bigint.t
    val get_next : unit -> V.t list option
  end
