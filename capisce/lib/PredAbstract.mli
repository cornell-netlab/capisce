open Core

module type Key = sig
  type t
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
end   
      
module Make (Form : Key) : sig
  type t

  (** [abs a e] returns a pair (x,a), where x is a new string to replace e with
   and a' is the new abstraction state *)
  val abs : t -> Form.t -> string * t
  val create : unit -> t 
end
