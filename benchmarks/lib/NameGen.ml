open Core   

type t = int

let create () = 0
let reset _ = 0
let get id = (Printf.sprintf "x$%d" id, id + 1)
  
