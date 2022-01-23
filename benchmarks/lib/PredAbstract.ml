open Core

module type Key = sig
  type t
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
end

module Make (Form : Key) = struct

  module M = Map.Make (Form) 
  type t = (string M.t * NameGen.t)

  (* If no match, create new variable name, update map * generator *)       
  let abs (m, g) e =
    match M.find m e with
    | None ->
       let (x, g) = NameGen.get g in
       let m = M.set m ~key:e ~data:x in
       (x, (m, g))
    | Some x ->
       (x, (m,g))

  let create () = (M.empty, NameGen.create ())

end
