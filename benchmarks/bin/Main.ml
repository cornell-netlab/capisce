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

let beastiary : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Runs the Beastiary of Examples"
    [%map_open
     let debug = flag "-D" no_arg ~doc:"show debugging info" in
         fun () ->         
         Pbench.Log.debug := debug;
         Pbench.MicroExamples.run_all ()
    ]
  
let infer : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Infers control plane constraint from data plane"
    [%map_open
     let source = anon ("p4 source file" %: string) and
         includes = flag "-I" (listed string) ~doc:"includes directories" and
         debug = flag "-D" no_arg ~doc:"show debugging info" and
         gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
         no_smart = flag "--disable-smart" no_arg ~doc:"disable smart constructors" and
         check_only = flag "--check-only" no_arg ~doc:"simply check the existence of a solution"
         in
         fun () ->         
         Pbench.Log.debug := debug;
         Pbench.BExpr.enable_smart_constructors := if no_smart then `Off else `On;
         let gas = Option.value gas_opt ~default:1000 in
         let cmd = Pbench.P4Parse.as_cmd_from_file includes source gas debug in
         Pbench.Log.print @@ lazy (Pbench.Cmd.to_string cmd);
         let (dur, res, _, called_solver) =
           Bench.cvc4_check false (cmd, Pbench.BExpr.true_)
         in
         if String.is_substring res ~substring:"sat"
            && not (String.is_substring res ~substring:"unsat") then
           if check_only then
             Printf.printf "Checked feasibility in %fms with%s calling the solver. Got: \n%s\n%!"
               (Time.Span.to_ms dur)
               (if called_solver then "" else "out")
               res
           else
             let (inf_dur, inf_res, _, inf_called_solver) =
               (* Bench.cvc4_z3_infer false (cmd, Pbench.BExpr.true_) *)
               Bench.cvc4_z3_fix 4 false (cmd, Pbench.BExpr.true_)
             in
             Printf.printf "Done in %fms with%s calling the solver in inference phase. Got: \n%s\n%!"
               (Time.Span.(to_ms (inf_dur + dur)))
               (if inf_called_solver then "" else "out")
               inf_res
    ]

  
let main =
  Command.group ~summary:"research toy for exploring verification & synthesis of p4 programs"
    [("bench", bench);
     ("beastiary", beastiary);
     ("infer", infer)
    ]

let () = Command.run main    
