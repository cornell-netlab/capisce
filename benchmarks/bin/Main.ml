open Core
module Bench = Pbench.Bench
module Nat = Pbench.Nat             

let run_and_print_exp f smart one n =
  f smart one n
  |> List.iteri
    ~f:(fun i (time,str,size,used_solver) ->
      let ok = Bench.answer_ok str in
      Printf.printf "%d,%f,%b,%d,%b\n%!"
        (if one then n else i+2)
        (Time.Span.to_ms time)
        ok
        size
        used_solver;
      if not ok then Printf.printf "%s\n%!" str; 
    )
             
let bench : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Invokes the Princess benchmarker"
    [%map_open
     let n = anon ("num tables" %: int) and
         debug = flag "-D" no_arg ~doc:"show debugging info" and
         one = flag "-one" no_arg ~doc:"Only run the nth experiment" and
         princess = flag "-p" no_arg ~doc:"run the princess solver" and
         cvc4 = flag "-cvc4" no_arg ~doc:"run the cvc4 solver" and         
         z3 = flag "-z" no_arg ~doc:"run z3-only solver" and
         smart = flag "-s" no_arg ~doc:"enable heuristic smart constructors" and
         simpl = flag "-simpl" no_arg ~doc:"run ex-post facto heuristic analysis" 
         in
         fun () ->
         Pbench.Log.debug := debug;
         Pbench.BExpr.enable_smart_constructors := if smart then `On else `Off;
         begin
             if princess then begin           
                 (* Printf.printf "Checking Princess. . . \n%!"; *)
                 run_and_print_exp Bench.princess simpl one n
               end;
             if z3 then begin
                 (* Printf.printf "Checking Z3. . . \n%!"; *)
                 run_and_print_exp Bench.z3 simpl one n
               end;
             if cvc4 then begin
                 (* Printf.printf "checking cvc4. . . \n%!"; *)
                 run_and_print_exp Bench.cvc4 simpl one n
               end
         end
    ]

let nat : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Runs NAT example"
    [%map_open
     let debug = flag "-D" no_arg ~doc:"show debugging info" in
         fun () ->         
         Pbench.Log.debug := debug;
         Printf.printf "%s" (Nat.smt ())
    ]

let beastiary : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Runs the Beastiary of Examples"
    [%map_open
     let debug = flag "-D" no_arg ~doc:"show debugging info" in
         fun () ->         
         Pbench.Log.debug := debug;
         Pbench.MicroExamples.run_all ()
    ]
  

let main =
  Command.group ~summary:"research toy for exploring verification & synthesis of p4 programs"
    [("bench", bench);
     ("nat", nat);
     ("beastiary", beastiary)]

let () = Command.run main    
