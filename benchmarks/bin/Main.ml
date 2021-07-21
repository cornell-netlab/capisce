open Core
module Bench = Pbench.Bench
module Nat = Pbench.Nat             

let run_and_print_exp f one n =
  List.iteri (f one n)
    ~f:(fun i (t,s) ->
      Printf.printf "%d,%f,%b\n%!" (i+2) (Time.Span.to_ms t) (Bench.answer_ok s)
    )
             
let main : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Invokes the Princess benchmarker"
    [%map_open
     let n = anon ("num tables" %: int) and
         debug = flag "-D" no_arg ~doc:"show debugging info" and
         one = flag "-one" no_arg ~doc:"Only run the nth experiment" and
         princess = flag "-p" no_arg ~doc:"run the princess solver" and
         z3prince = flag "-b" no_arg ~doc:"run the sequenced solver" and
         z3 = flag "-z" no_arg ~doc:"run z3-only solver" and
         nat = flag "-nat" no_arg ~doc:"Print out the nat wp"
         in
         fun () ->
         Pbench.Log.debug := debug;
         if nat then
           Printf.printf "%s" (Nat.smt ())
         else begin
             if z3prince then begin
                 Printf.printf "Checking Z3 then Princess . . . \n%!";
                 run_and_print_exp Bench.z3_princess one n
               end;
             if princess then begin           
                 Printf.printf "Checking Princess. . . \n%!";
                 run_and_print_exp Bench.princess one n
               end;
             if z3 then begin
                 Printf.printf "Checking Z3. . . \n%!";
                 run_and_print_exp Bench.z3 one n
               end
           end
    ]


let () = Command.run main

