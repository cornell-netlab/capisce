open Core
open Time   

type t =  Time.t

let start () = now()
let stop c = diff (now ()) c                 
