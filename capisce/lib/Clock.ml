open Core
open Time   

type t = Time.t

let start () : t = now ()
let stop c : float = diff (now ()) c |> Span.to_ms
let read (c : t) : float = to_span_since_epoch c |> Span.to_ms
let now () : float = start () |> read
