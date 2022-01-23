open Core

   
type t = Id of (string)
       | Let of t list * t
       | Forall of t list * t
       | Exists of t list * t
       | Fun of t * t list
       | BV of (Bigint.t * int) 
       [@@deriving eq, sexp, compare, quickcheck]     

let to_sexp_string s =
  [%sexp_of: t list] s
  |> Sexp.to_string
