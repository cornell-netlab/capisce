module Bench = Pbench.Bench

let () =
  Bench.benchmark 2
  |> Printf.printf "%s\n%!"

