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
  val exploder : t ref
  val smart : t ref
  val rewrites : t ref
  val qe : t ref
end

val parse_flags : String.t -> unit
val override : unit -> unit

val error :  ('a -> unit, unit, string, string, string, unit) format6  -> 'a lazy_t -> unit
val error_s : string -> unit

val warn : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val warn_s : string -> unit

val smt      : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val irs      : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit

val measure   : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val measure_s : string -> unit

val graph    : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val graph_s  : string -> unit

val path_gen : ('a -> unit, unit, string, string, string, unit) format6  -> 'a lazy_t -> unit
val path_gen_s : string -> unit

val compiler : ('a -> unit, unit, string, string, string, unit) format6  -> 'a lazy_t -> unit
val compiler_s : string -> unit

val exploder : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val exploder_s : string -> unit

val tree : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val tree_s : string -> unit


val smart    : ('a -> unit, unit, string, string, string, unit) format6  -> 'a lazy_t -> unit
val rewrites : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val qe       : ('a -> unit, unit, string, string, string, unit) format6  -> 'a lazy_t -> unit
val qe_s     : string -> unit

val graph_dot    : (string option -> unit) -> string -> unit
val path_gen_dot : (string option -> unit) -> string -> unit
val tree_dot : (string option -> unit) -> string -> unit

val debug    : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val debug_s  : string -> unit

val monitor   : ('a -> unit, unit, string, string, string, unit) format6 -> 'a lazy_t -> unit
val monitor_s : string -> unit
