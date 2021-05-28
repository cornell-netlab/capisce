open Core
   
type t = String.t

let (=) : t -> t -> bool = String.(=)           
