open Core
module Bench = Pbench.Bench
module Qe = Pbench.Qe

let () = Memtrace.trace_if_requested ~context:"icecap" ()

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

let compile : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Infers control plane constraint from data plane"
    [%map_open
     let
       source = anon ("p4 source file" %: string) and       
       includes = flag "-I" (listed string) ~doc:"includes directories" and
       gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
       unroll_opt = flag "-u" (optional int) ~doc:"how much to_unroll the parser"
       in
       fun () ->
       Pbench.BExpr.enable_smart_constructors := `On;
       Pbench.Log.debug := true;
       let gas = Option.value gas_opt ~default:1000 in
       let unroll = Option.value unroll_opt ~default:10 in
       let cmd = Pbench.P4Parse.as_cmd_from_file includes source gas unroll false in
       let cmd_o = Pbench.Cmd.optimize cmd in
       (* let cmd_a,_ = Pbench.Cmd.abstract cmd_o (Pbench.NameGen.create ()) in *)
       let cmd_p = Pbench.Cmd.passify cmd_o in
       let merged = Pbench.Cmd.assume_disjuncts cmd_p in
       (* let vc = Pbench.Cmd.vc cmd_o in *)
       (* let (dvs, cvs) = Pbench.BExpr.vars vc in *)
       (* Printf.printf "GCL program:\n%s\n\n%!" @@ Pbench.Cmd.to_string cmd; *)
       Printf.printf "ConstProp'd:\n%s\n\n%!" @@ Pbench.Cmd.to_string cmd_o;
       Printf.printf "cmd went from %d nodes to %d nodes\n\n%!" (Pbench.Cmd.size cmd) (Pbench.Cmd.size cmd_o);
       (* Printf.printf "Path Merging:\n%s\n\n%!" (Pbench.Cmd.to_string merged); *)
        (* cmd went from 34303 nodes to 16872 nodes *)
       Printf.printf "From %s paths to %s\n%!"
         (Bigint.to_string (Pbench.Cmd.count_paths cmd_o))
         (Bigint.to_string (Pbench.Cmd.count_paths merged));
       (* Printf.printf "abstracted program is a homeomorphism of the OG program: %d nodes, %s paths\n %s\n%!" *)
       (*   (Pbench.Cmd.size cmd_a) *)
       (*   (Pbench.Cmd.count_paths cmd_o |> Bigint.to_string) *)
       (*   (Pbench.Cmd.to_string cmd_a); *)
       (* Printf.printf "the action variables are;\n"; *)
       (* let total_size = ref Bigint.zero in *)
       (* List.iter (Pbench.Cmd.collect_action_vars cmd_o) *)
       (*   ~f:(fun x -> *)
       (*       Printf.printf "\t%s (_ BitVec %d)\n%!" (Pbench.Var.str x) (Pbench.Var.size x); *)
       (*       total_size := Bigint.(!total_size + of_int (Pbench.Var.size x)); *)
       (*     ); *)
       (* Printf.printf "which has %s alternatives\n%!" (Bigint.((of_int 2) ** !total_size |> to_string)); *)
       (* Printf.printf "but there are only %s possibilities\n%!" (Pbench.Cmd.action_var_paths cmd_o |> Bigint.to_string); *)

       Printf.printf "Passified:\n%s \n%!" @@ Pbench.Cmd.to_string cmd_p;
       (* Printf.printf "\n And its VC: %s \n (forall (%s) \n %s) \n\n%!" *)
       (*   (Pbench.Var.list_to_smtlib_decls cvs) *)
       (*   (Pbench.Var.list_to_smtlib_quant dvs) *)
       (*   (Pbench.BExpr.to_smtlib vc) *)
    ]
       
let infer : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Infers control plane constraint from data plane"
    [%map_open
     let source = anon ("p4 source file" %: string) and
         includes = flag "-I" (listed string) ~doc:"includes directories" and
         debug = flag "-D" no_arg ~doc:"show debugging info" and
         gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
         unroll_opt = flag "-u" (optional int) ~doc:"how much to unroll the parser" and
         no_smart = flag "--disable-smart" no_arg ~doc:"disable smart constructors" and
         check_only = flag "--check-only" no_arg ~doc:"simply check the existence of a solution" and
         skip_check = flag "--skip-check" no_arg ~doc:"dont check whether a solution exists" and
         iter = flag "--iter" no_arg ~doc:"use iterative solution" and
         solvers = flag "-s" (listed string) ~doc:"solving order"
         in
         fun () ->
         Printexc.record_backtrace true;
         Pbench.Log.debug := debug;
         Pbench.BExpr.enable_smart_constructors := if no_smart then `Off else `On;
         let gas = Option.value gas_opt ~default:1000 in
         let unroll = Option.value unroll_opt ~default:10 in
         Pbench.Log.print @@ lazy (Printf.sprintf "compiling...");
         let cmd = Pbench.P4Parse.as_cmd_from_file includes source gas unroll false in
         Pbench.Log.print @@ lazy (Printf.sprintf "done\noptimizing...");
         let cmd_o = Pbench.Cmd.optimize cmd in
         Pbench.Log.print @@ lazy (Printf.sprintf "done\nserializing....");                  
         Pbench.Log.print @@ lazy (Pbench.Cmd.to_string cmd_o);
         let vc = Pbench.Cmd.vc cmd_o in
         let (dvs, cvs) = Pbench.BExpr.vars vc in
         Printf.printf "\n And its VC: %s \n (forall (%s) \n %s) \n\n%!"
           (Pbench.Var.list_to_smtlib_decls cvs)
           (Pbench.Var.list_to_smtlib_quant dvs)         
           (Pbench.BExpr.to_smtlib vc);

         Pbench.Breakpoint.set true;
         Pbench.Log.print @@ lazy (Printf.sprintf "cmd went from %d nodes to %d nodes" (Pbench.Cmd.size cmd) (Pbench.Cmd.size cmd_o));
         let cmd = cmd_o in
         (* Pbench.Breakpoint.set true; *)
         let (dur, res, _, called_solver) =
           if skip_check then
             (Time.Span.zero, "sat", 0, false)
           else begin 
               Pbench.Log.print @@ lazy "checking satisfiability\n";
               Qe.z3_check false (cmd, Pbench.BExpr.true_)
             end
         in
         Printf.printf "%s\n%!" res;
         if String.is_substring res ~substring:"sat"
            && not (String.is_substring res ~substring:"unsat") then
           if check_only then
             Printf.printf "Checked feasibility in %fms with%s calling the solver. Got: \n%s\n%!"
               (Time.Span.to_ms dur)
               (if called_solver then "" else "out")
               res
           else
             let _ : [`CVC4 | `Z3 | `Z3Light ] list =
               List.map solvers ~f:(function 
                   | "CVC4" | "cvc4" | "c" -> `CVC4
                   | "Z3" | "z3" | "z" -> `Z3
                   | "z3-light" | "light" | "qe-light" -> `Z3Light
                   |  _ -> failwith "unrecognized qe solver" ) in
             let (inf_dur, inf_res, _, inf_called_solver) =
               (* Bench.z3_infer false (cmd, Pbench.BExpr.true_) *)
               if iter then
                 (Qe.solving_all_paths (cmd, Pbench.BExpr.true_))
               else
                 (* Qe.cvc4_z3_fix fix solvers false (cmd, Pbench.BExpr.true_) *)
                 Qe.subsolving (cmd, Pbench.BExpr.true_)
             in
             Printf.printf "Done in %fms with%s calling the solver in inference phase. Got: \n%s\n%!"
               (Time.Span.(to_ms (inf_dur + dur)))
               (if inf_called_solver then "" else "out")
               inf_res
    ]

let smtlib : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Debugging frontend for smtlib parser"
    [%map_open
     let source = anon ("smtlib source file" %: string) in
         fun () ->
         let open Pbench in
         let smtast = SmtParser.parse source () in
         let b = SmtAst.translate smtast ~cvs:[] ~dvs:[] in
         let b = BExpr.simplify b in
         Printf.printf "%s\n%!" (BExpr.to_smtlib b);
    ]

    
let main =
  Command.group ~summary:"research toy for exploring verification & synthesis of p4 programs"
    [("bench", bench);
     ("beastiary", beastiary);
     ("infer", infer);
     ("compile", compile);
     ("smtlib", smtlib);
    ]

let () = Command_unix.run main    
