type t

module FLAGS : sig
  val debug : t ref
  val override : bool ref
  val measure : t ref
  val dot : t ref
  val smt : t ref
  val irs : t ref
  val graph : t ref
  val path_gen : t ref
  val compiler : t ref
  val smart : t ref
  val rewrites : t ref
  val qe : t ref
end

val parse_flags : String.t -> unit
val override : unit -> unit


val warn : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val error : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit

val smt      : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val measure  : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val graph    : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val irs      : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val path_gen : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val compiler : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val smart    : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val rewrites : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val debug    : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit
val qe       : ('a -> unit, out_channel, unit) format -> 'a lazy_t -> unit

val graph_dot    : (string option -> unit) -> string -> unit
val path_gen_dot : (string option -> unit) -> string -> unit
