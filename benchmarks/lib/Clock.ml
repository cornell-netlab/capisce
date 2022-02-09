open Core
open Time   

type t =  Time.t

let start () = now ()
let stop c = diff (now ()) c
let now () = now () |> to_span_since_epoch |> Span.to_ms               
