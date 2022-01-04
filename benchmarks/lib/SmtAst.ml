open Core
   

type t = Id of string
       | App of t list
       [@@deriving eq, sexp, compare, quickcheck]     


let to_sexp_string s =
  [%sexp_of: t list] s
  |> Sexp.to_string
              
let rec to_string = function
  | Id string -> string
  | App ts ->
     let strings = List.map ~f:to_string ts in     
     Printf.sprintf "(%s)" (String.concat ~sep:" " strings)
  
let list_to_string ts =
  List.map ts ~f:to_string
  |> String.concat ~sep:"\n"
