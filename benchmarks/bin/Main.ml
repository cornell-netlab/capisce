open Core
open Pbench
module Qe = Qe

let () = Memtrace.trace_if_requested ~context:"icecap" ()




let hoare : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Modular Inference of control plane constraints"
    [%map_open
      let
      source = anon ("p4 source file" %: string) and
      includes = flag "-I" (listed string) ~doc:"includes directories" and
      debug = flag "-DEBUG" no_arg ~doc:"allow pure debug messages" and
      verbosity = flag "-v" (listed string) ~doc:"verbosity" and
      gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
      unroll_opt = flag "-u" (optional int) ~doc:"how much to unroll the parser" and
      no_smart = flag "--disable-smart" no_arg ~doc:"disable smart constructors" and
      disable_header_validity = flag "--no-hv" (no_arg) ~doc:"disable header validity checks" and
      disable_soundness_check = flag "--unsound" (no_arg) ~doc:"disable soundness check" and
      nprocs = flag "--nprocs" (optional int) ~doc:"number of processes" and
      pid = flag "--pid" (optional int) ~doc:"process id"
      in fun () ->
        let open DependentTypeChecker in
        Printexc.record_backtrace true;
        Log.parse_flags (String.concat verbosity);
        if debug then Log.override ();
        BExpr.enable_smart_constructors := if no_smart then `Off else `On;
        let gas = Option.value gas_opt ~default:1000 in
        let unroll = Option.value unroll_opt ~default:10 in
        Log.compiler "gas %d" @@ lazy gas;
        Log.compiler "unroll %d" @@ lazy unroll;
        let coq_gcl = P4Parse.tbl_abstraction_from_file includes source gas unroll false (not disable_header_validity) in
        Log.compiler "%s" @@ lazy "compiling to gpl...";
        let (hprsr, hpipe) = Tuple2.map ~f:(Translate.gcl_to_hoare) coq_gcl in
        Log.irs "Parser:\n%s" @@ lazy (HoareNet.to_string hprsr);
        Log.irs "Pipeline:\n%s" @@ lazy (HoareNet.to_string hpipe);
        let hoarenet =  HoareNet.seq hprsr hpipe in
        let hoarenet = HoareNet.normalize_names hoarenet in
        let hoarenet = HoareNet.optimize hoarenet in
        let st = Clock.start () in
        (*First, check the soundness of the annotations*)
        if disable_soundness_check || HoareNet.check_annotations hoarenet then begin
          Printf.printf "Checked annotations in %fms\n%!" (Clock.stop st);
          let st = Clock.start () in
          let psi = HoareNet.infer hoarenet nprocs pid in
          Printf.printf "Inferred in %f ms\n%!" (Clock.stop st);
          Printf.printf "Got:\n%s\n%!" (BExpr.to_smtlib psi)
        end else
          Printf.printf "Soundness check failed in %fms\n%!" (Clock.stop st);
    ]

let compile : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Compiles the program to GCL"
    [%map_open
     let
       source = anon ("p4 source file" %: string) and       
       includes = flag "-I" (listed string) ~doc:"includes directories" and
       gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
       unroll_opt = flag "-u" (optional int) ~doc:"how much to_unroll the parser"
       in
       fun () ->
       let open ASTs in
       BExpr.enable_smart_constructors := `On;
       Log.parse_flags "vgi";
       let gas = Option.value gas_opt ~default:1000 in
       let unroll = Option.value unroll_opt ~default:10 in
       let coq_pair = P4Parse.tbl_abstraction_from_file includes source gas unroll false true in
       let (gpl_prsr, gpl_pipe) = Tuple2.map ~f:Translate.gcl_to_gpl coq_pair in
       Log.irs "RAW parser:\n%s\n" @@ lazy (GPL.to_string gpl_prsr);
       Log.irs "RAW pipeline:\n%s\n" @@ lazy (GPL.to_string gpl_pipe)
       (* Log.irs "RAW pipeline: \n%s" @@ lazy (GPL.to_string gpl_pipe); *)
       (* (\* let (gpl_prsr_o, gpl_pipe_o) = GPL.optimize_seq_pair (gpl_prsr, gpl_pipe) in *\) *)
       (* (\* let (gcl_prsr_o, gcl_pipe_o) = Tuple2.map ~f:GPL.encode_tables (gpl_prsr_o, gpl_pipe_o) in *\) *)
       (* Log.irs "%s" @@ lazy ("compiling from scratch"); *)
       (* let cmd = P4Parse.as_cmd_from_file includes source gas unroll false true in *)
       (* Log.irs "RAW FULL PROGRAM:\n%s" @@ lazy (GCL.to_string cmd); *)
       (* let cmd_o = Cmd.GCL.optimize cmd in *)

       (* let parse_graph = GCL.construct_graph gcl_prsr_o in *)
       (* Log.graph_dot (GCL.print_graph parse_graph) "parser"; *)
       (* Log.graph "Paths through parser %s" @@ lazy (parse_graph |> GCL.count_cfg_paths |> Bigint.to_string); *)
       (* let tfg_graph = TFG.project pipe |> TFG.construct_graph in *)
       (* Log.graph_dot (TFG.print_graph tfg_graph) "tfg_pipeline"; *)
       (* Log.graph "Paths through pipeline %s" @@ lazy (tfg_graph |> TFG.count_cfg_paths |> Bigint.to_string); *)
       (* let gpl_graph = pipe |> GPL.construct_graph in *)
       (* Log.graph_dot (GPL.print_graph gpl_graph) "gpl_pipeline"; *)
       (* Log.graph "Paths through pipeline %s" @@ lazy (gpl_graph |> GPL.count_cfg_paths |> Bigint.to_string) *)

       (* Log.irs "Optimized parser: \n%s" @@ lazy (GCL.to_string gcl_prsr_o); *)
       (* Log.irs "Optimized pipe: \n%s" @@ lazy (GCL.to_string gcl_pipe_o); *)
       (* Log.irs "Optimized together: %s" @@ lazy (GCL.to_string cmd_o); *)

       (* let cmd_a,_ = Cmd.abstract cmd_o (NameGen.create ()) in *)
       (* let (_, cmd_p) = PassiveGCL.passify cmd_o in *)
       (* let merged = PassiveGCL.assume_disjuncts cmd_p in *)
       (* let vc = Cmd.vc cmd_o in *)
       (* let (dvs, cvs) = BExpr.vars vc in *)
       (* Printf.printf "GCL program:\n%s\n\n%!" @@ GCL.to_string cmd; *)
       (* Printf.printf "ConstProp'd:\n%s\n\n%!" @@ GCL.to_string cmd_o; *)
       (* Printf.printf "cmd went from %d nodes to %d nodes\n\n%!" (GCL.size cmd) (GCL.size cmd_o); *)
       (* Printf.printf "Path Merging:\n%s\n\n%!" (PassiveGCL.to_string merged); *)
       (* Printf.printf "From %s paths to %s\n%!" *)
       (*   (Bigint.to_string (GCL.count_paths cmd_o)) *)
       (*   (Bigint.to_string (PassiveGCL.count_paths merged)); *)
       (* Printf.printf "abstracted program is a homeomorphism of the OG program: %d nodes, %s paths\n %s\n%!" *)
       (*   (Cmd.size cmd_a) *)
       (*   (Cmd.count_paths cmd_o |> Bigint.to_string) *)
       (*   (Cmd.to_string cmd_a); *)
       (* Printf.printf "the action variables are;\n"; *)
       (* let total_size = ref Bigint.zero in *)
       (* List.iter (Cmd.collect_action_vars cmd_o) *)
       (*   ~f:(fun x -> *)
       (*       Printf.printf "\t%s (_ BitVec %d)\n%!" (Var.str x) (Var.size x); *)
       (*       total_size := Bigint.(!total_size + of_int (Var.size x)); *)
       (*     ); *)
       (* Printf.printf "which has %s alternatives\n%!" (Bigint.((of_int 2) ** !total_size |> to_string)); *)
       (* Printf.printf "but there are only %s possibilities\n%!" (Cmd.action_var_paths cmd_o |> Bigint.to_string); *)

       (* Printf.printf "Passified:\n%s \n%!" @@ Cmd.to_string cmd_p; *)
       (* Printf.printf "\n And its VC: %s \n (forall (%s) \n %s) \n\n%!" *)
       (*   (Var.list_to_smtlib_decls cvs) *)
       (*   (Var.list_to_smtlib_quant dvs) *)
       (*   (BExpr.to_smtlib vc) *)
    ]


let table_infer : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Infers control plane constraint from data plane"
    [%map_open
      let source = anon ("p4 source file" %: string) and
      includes = flag "-I" (listed string) ~doc:"includes directories" and
      debug = flag "-DEBUG" no_arg ~doc:"allow pure debug messages" and
      verbosity = flag "-v" (listed string) ~doc:"verbosity" and
      gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
      unroll_opt = flag "-u" (optional int) ~doc:"how much to unroll the parser" and
      no_smart = flag "--disable-smart" no_arg ~doc:"disable smart constructors" and
      sfreq = flag "--freq" (optional int) ~doc:"frequency of sufficiency check" and
      fn = flag "--log" (optional string) ~doc:"file in which to log incremental paths" and
      disable_header_validity = flag "--no-hv" (no_arg) ~doc:"disable header validity checks"
      in
      fun () ->
        Printexc.record_backtrace true;
        Log.parse_flags (String.concat verbosity);
        if debug then Log.override ();
        BExpr.enable_smart_constructors := if no_smart then `Off else `On;
        let gas = Option.value gas_opt ~default:1000 in
        let unroll = Option.value unroll_opt ~default:10 in
        let sfreq = Option.value sfreq ~default:100 in
        Log.compiler "gas %d" @@ lazy gas;
        Log.compiler "unroll %d" @@ lazy unroll;
        let prsr = if unroll < 1 then `Skip else `Use in
        let coq_gcl = P4Parse.tbl_abstraction_from_file includes source gas unroll false (not disable_header_validity) in
        Log.compiler "%s" @@ lazy "compiling to gpl...";
        let gpl = Tuple2.map ~f:(Translate.gcl_to_gpl) coq_gcl in
        let st = Clock.start () in
        Log.compiler_s "optimizing...";
        let gpl = ASTs.GPL.optimize_seq_pair gpl in
        Log.compiler_s "done optimizing; starting inference";
        let cpf = Qe.table_infer ~sfreq ~prsr ~fn gpl None None in
        Printf.printf "Result:\n%s\n%!Computedin %f:\n%!" (BExpr.to_smtlib cpf) (Clock.stop st)
    ]

let infer : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Infers control plane constraint from data plane"
    [%map_open
     let source = anon ("p4 source file" %: string) and
         includes = flag "-I" (listed string) ~doc:"includes directories" and
         debug = flag "-DEBUG" no_arg ~doc:"allow pure debug messages" and
         verbosity = flag "-v" (listed string) ~doc:"verbosity" and
         gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
         unroll_opt = flag "-u" (optional int) ~doc:"how much to unroll the parser" and
         no_smart = flag "--disable-smart" no_arg ~doc:"disable smart constructors" and
         solvers = flag "-s" (listed string) ~doc:"solving order" and
      disable_header_validity = flag "--no-hv" (no_arg) ~doc:"disable header validity checks"
         in
         fun () ->
         let open ASTs in
         Printexc.record_backtrace true;
         Log.parse_flags (String.concat verbosity);
         if debug then Log.override ();
         BExpr.enable_smart_constructors := if no_smart then `Off else `On;
         let gas = Option.value gas_opt ~default:1000 in
         let unroll = Option.value unroll_opt ~default:10 in
         let st = Clock.start () in
         Log.compiler "at %f start compiling..." @@ lazy (Clock.read st);
         let cmd = P4Parse.as_cmd_from_file includes source gas unroll false (not disable_header_validity) in
         Log.compiler "done in %f \noptimizing..." @@ lazy (Clock.stop st);
         let st = Clock.start () in
         let cmd_o = GCL.optimize cmd in
         Log.compiler "done in %f..." @@ lazy (Clock.stop st);
         Log.irs "Optimized program:\n%s" @@ lazy (GCL.to_string cmd_o);
         Log.compiler "cmd started with %d nodes" @@ lazy (GCL.size cmd);
         Log.compiler "it ended up with %d nodes" @@ lazy (GCL.size cmd_o);
         let cmd = cmd_o in
         (* Breakpoint.set true; *)
         let _ : [`CVC4 | `Z3 | `Z3Light ] list =
           List.map solvers ~f:(function
               | "CVC4" | "cvc4" | "c" -> `CVC4
               | "Z3" | "z3" | "z" -> `Z3
               | "z3-light" | "light" | "qe-light" -> `Z3Light
               |  _ -> failwith "unrecognized qe solver" ) in
         let (inf_dur, inf_res, _, _) =
           (* Bench.z3_infer false (cmd, BExpr.true_) *)
             Qe.subsolving (cmd, BExpr.true_)
         in
         Printf.printf "Done in %fms with calling the solver in inference phase. Got: \n%s\n%!"
           (inf_dur)
           inf_res
    ]

let verify : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Program verifier"
    [%map_open
     let source = anon ("p4 source file" %: string) and
         includes = flag "-I" (listed string) ~doc:"includes directories" and
         gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
         unroll_opt = flag "-u" (optional int) ~doc:"how much to unroll the parser"
     in
         fun () ->
         let open ASTs in
         let gas = Option.value gas_opt ~default:1000 in
         let unroll = Option.value unroll_opt ~default:10 in
         let cmd = P4Parse.as_cmd_from_file includes source gas unroll false true in
         let cmd_o = GCL.optimize cmd in
         let vc = passive_vc cmd_o in
         let (dvs, cvs) = BExpr.vars vc in
         if (Solver.check_unsat (cvs @ dvs) (BExpr.not_ vc)) then
           Printf.printf "valid\n%!"
         else
           Printf.printf "invalid\n%!"
   ]

let graph : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Generate the CFG graph"
    [%map_open
     let source = anon ("p4 source file" %: string) and
         filename = flag "--out" (optional string) ~doc: "the output .dot file " and
         includes = flag "-I" (listed string) ~doc:"includes directories" and
         gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler" and
         unroll_opt = flag "-u" (optional int) ~doc:"how much to unroll the parser" and
         tables = flag "--tables" no_arg ~doc:"only show tables"
     in
         fun () ->
         let open ASTs in
         let gas = Option.value gas_opt ~default:1000 in
         let unroll = Option.value unroll_opt ~default:10 in
         let gcl = P4Parse.tbl_abstraction_from_file includes source gas unroll false false in
         let gpl = Tuple.T2.map ~f:(Translate.gcl_to_gpl) gcl |> Util.uncurry GPL.seq in
         if tables then
           let tfg = TFG.project gpl in
           let grf = Qe.TFG_G.construct_graph tfg in
           Qe.TFG_G.print_graph grf filename;
           Printf.printf "%s has %s table-paths\n%!" source (Qe.TFG_G.count_cfg_paths grf |> Bigint.to_string)
         else
           let grf = Qe.GPL_G.construct_graph gpl in
           Qe.GPL_G.print_graph grf filename;
           Printf.printf "%s" (Qe.GPL_G.print_key grf);
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
    [("infer", infer);
     ("hoare", hoare);
     ("table", table_infer);
     ("verify", verify);
     ("graph", graph);
     ("compile", compile);
     ("smtlib", smtlib);
    ]

let () = Command_unix.run main    
