open Core
module Bench = Pbench.Bench

let main : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Invokes the Princess benchmarker"
    [%map_open
     let n = anon ("num tables" %: int) in
         fun () ->         
         Bench.benchmark n
         |> Printf.printf "%s\n%!"
    ]


let () = Command.run main

