open Core
open Pbench
module Qe = Qe

let () = Memtrace.trace_if_requested ~context:"icecap" ()

let experiment : Command.t =
  let open Programs in 
  let open Command.Let_syntax in
  Command.basic ~summary:"runs hand-translated experiment"
  [%map_open
    let name = flag "-name" (required string) ~doc:"S experiment name"
    and out = flag "-out" (required string) ~doc:"F path to result info"
    and enum = flag "-enum" (no_arg) ~doc:"use naive enumeration method"
    and replay = flag "-replay" (no_arg) ~doc:"log timestamps for each path condition. Measure number of paths covered by each condition"
    in fun () -> 
      Log.override ();
      Printf.printf "%s\n" name;
      let program = match String.lowercase name with
      | "ecmp" -> ECMP.ecmp
      | "netpaxos_acceptor" -> NetpaxosAcceptor.netpaxos_acceptor
      | "resubmit" -> Resubmit.resubmit
      | "ndp_router" -> NDPRouter.ndp_router
      | "heavy_hitter_1" | "hh1" -> HeavyHitter1.heavy_hitter_1
      | "arp" -> Arp.arp
      | "07-multiprotocol" -> Multiprotocol.multiprotocol
      | "mc_nat" -> MCNat.mc_nat false
      | "mc_nat_fixed" -> MCNat.mc_nat true
      | "ts_switching" -> TSSwitching.ts_switching false
      | "ts_switching_fixed" -> TSSwitching.ts_switching true
      | "heavy_hitter_2" | "hh2" -> HeavyHitter2.heavy_hitter_2 false
      | "heavy_hitter_2_fixed" | "hh2_fixed" -> HeavyHitter2.heavy_hitter_2 true
      | "flowlet" -> Flowlet.flowlet false
      | "flowlet_fixed" -> Flowlet.flowlet true
      | "hula" -> Hula.hula false
      | "hula_fixed" -> Hula.hula true
      | "linearroad" -> Linearroad.linearroad false
      | "linearroad_fixed" -> Linearroad.linearroad true
      | "netchain" -> NetChain.netchain
      | "simple_nat" | "simplenat" -> SimpleNat.simple_nat
      | "fabric" -> Fabric.fabric false
      | "fabric_fixed" -> Fabric.fabric true
      | _ -> failwithf "unrecognized program:%s" name ()
      in
      let open DependentTypeChecker in
      let algorithm p = 
        HoareNet.infer p None None ~qe:(if enum then `Enum else `Conc)
      in
      let paths p =
        HoareNet.annotated_to_gpl p
        |> ASTs.GPL.count_paths
        |> Bigint.to_string
      in
      let st = Clock.start () in
      let phi = 
        try algorithm program with
        | Failure msg -> 
          if String.(msg = "unsolveable") then
            BExpr.false_
          else failwith msg
      in
      let num_cexs = !Qe.num_cexs |> Bigint.to_string in
      let time = Clock.stop st  |> Float.to_string in
      let filename f = Printf.sprintf "%s/%s_%s_%s" out name (if enum then "enum" else "cegps") f in
      Out_channel.write_all (filename "formula") ~data:(BExpr.to_smtlib phi);
      Out_channel.write_all (filename "size") ~data:(Int.to_string @@ BExpr.size phi);
      Out_channel.write_all (filename "tot_paths") ~data:(paths program);
      Out_channel.write_all (filename "count_paths") ~data:(num_cexs);
      Out_channel.write_all (filename "time") ~data:time;
      if replay then
        let time_series = Qe.replay (!Qe.data) (program |> HoareNet.annotated_to_gpl |> ASTs.GPL.encode_tables) in 
        let time_series_str = List.map time_series ~f:(fun (t,n) -> Printf.sprintf "%f, %d\n" t n) |> String.concat ~sep:"" in 
        Out_channel.write_all (filename "completion") ~data:(time_series_str)

  ]

let infer : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Infers control plane constraint from data plane"
    [%map_open
     let source = anon ("p4 source file" %: string)
     and includes = flag "-I" (listed string) ~doc:"includes directories"
     and debug = flag "-DEBUG" no_arg ~doc:"allow pure debug messages"
     and verbosity = flag "-v" (listed string) ~doc:"verbosity"
     and gas_opt = flag "-g" (optional int) ~doc:"how much gas to pass the compiler"
     and unroll_opt = flag "-u" (optional int) ~doc:"how much to unroll the parser"
     and no_smart = flag "--disable-smart" no_arg ~doc:"disable smart constructors"
     (* and solvers = flag "-s" (listed string) ~doc:"solving order" *)
     (* and disable_header_validity = flag "--no-hv" (no_arg) ~doc:"disable header validity checks" *)
     in fun () ->
       let open DependentTypeChecker in
       Printexc.record_backtrace true;
       Log.parse_flags (String.concat verbosity);
       if debug then Log.override ();
       BExpr.enable_smart_constructors := if no_smart then `Off else `On;
       let gas = Option.value gas_opt ~default:1000 in
       let unroll = Option.value unroll_opt ~default:10 in
       (* let cmd = P4Parse.as_cmd_from_file includes source gas unroll false (not disable_header_validity) in *)
       let prsr, pipe = P4Parse.minimal_frontend_from_file includes source gas unroll false in
       let hoarenet = HoareNet.seq prsr pipe in
       let hoarenet = HoareNet.normalize_names hoarenet in
       let hoarenet = HoareNet.zero_init hoarenet in
       let hoarenet = HoareNet.optimize hoarenet in
       let phi = HoareNet.infer hoarenet None None in
       Printf.printf "%s\n%!" @@ BExpr.to_smtlib phi

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
         let open DependentTypeChecker in
         let gas = Option.value gas_opt ~default:1000 in
         let unroll = Option.value unroll_opt ~default:10 in
         (* let cmd = P4Parse.as_cmd_from_file includes source gas unroll false true in *)
         let prsr, pipe = P4Parse.minimal_frontend_from_file includes source gas unroll false in
         let cmd_o = HoareNet.(optimize (seq prsr pipe)) in
         let vc = HoareNet.vc cmd_o in
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
         let gpl = Tuple.T2.map ~f:(Translate.gcl_to_gpl) gcl |> fst (**Util.uncurry GPL.seq in*) in
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

let micro : Command.t =
  let open Command.Let_syntax in
  let ternary : Command.t =
    Command.basic ~summary:"measure the performance effect of ternary matches on solve time"
    [%map_open
      let verbosity = flag "-v" (listed string) ~doc:"verbosity"
      and debug = flag "-D" no_arg ~doc:"Enable generic debug logging"
      and bitwidth = flag "--bitwidth" (optional int) ~doc:"B The bitwidth for all variables in the benchmark (default 32)"
      and max_keys = flag "--max-keys" (required int) ~doc:"K The maximum number of keys in any table"
      and max_tables = flag "--max-tables" (optional int) ~doc:"T the maximum number of tables (default 1)"
      in
      fun () ->
        Log.parse_flags (String.concat verbosity);
        if debug then Log.override ();
        let bitwidth = Option.value bitwidth ~default:32 in
        let max_tables = Option.value max_tables ~default:1 in
        let _ =
          Pbench.Micro.ternary_match_benchmark ~bitwidth ~max_tables ~max_keys
        in
        ()]
  in
  let detfwd : Command.t =
    Command.basic ~summary:"mesure the performance effect of pipeline length and the action complexity of tables"
    [%map_open
      let verbosity = flag "-v" (listed string) ~doc:"verbosity"
      and debug = flag "-D" no_arg ~doc:"Enable generic debug logging"
      and bitwidth = flag "--bitwidth" (optional int) ~doc:"B the bitwidth for all variables in the benchmark (default 32)"
      and max_tables = flag "--max-tables" (required int) ~doc:"T the maximum number of pipelined tables"
      and max_acts = flag "--max-acts" (required int) ~doc:"A the maximum number of actions in any table"
      and max_assigns = flag "--max-assigns" (optional int ) ~doc:"D the maximum number of forwarding assignments (default A)"
      in
      fun () ->
        Log.parse_flags (String.concat verbosity);
        if debug then Log.override ();
        let bitwidth = Option.value bitwidth ~default:32 in
        let max_assigns = Option.value max_assigns ~default:max_acts in
        let _ =
          Pbench.Micro.determined_forwarding ~bitwidth ~max_tables ~max_acts ~max_assigns
        in
        ()
    ]
  in
  let joins : Command.t =
    Command.basic ~summary:"measure the performance effect of join conditions"
    [%map_open
      let verbosity = flag "-v" (listed string) ~doc:"verbosity"
      and debug = flag "-D" no_arg ~doc:"Enable generic debug logging"
      and bitwidth = flag "--bitwidth" (optional int) ~doc:"B the bitwidth for all variables in the benchmark (default 32)"
      and max_joins = flag "--max-joins" (required int) ~doc:"J the maximum number of pipelined tables"
      and max_join_vars = flag "--max-join-vars" (required int) ~doc:"V the maximum number of join_vars in any table"
      in
      fun () ->
        Log.parse_flags (String.concat verbosity);
        if debug then Log.override ();
        let bitwidth = Option.value bitwidth ~default:32 in
        let _ =
          Pbench.Micro.join_conditions ~bitwidth ~max_joins ~max_join_vars
        in
        ()
    ]
  in
  Command.group ~summary:"Generate microbenchmark data"
    [ ("ternary", ternary);
      ("detfwd", detfwd);
      ("joins", joins)
    ]

let main =
  Command.group ~summary:"research toy for exploring verification & synthesis of p4 programs"
    [("infer", infer);
     ("verify", verify);
     ("graph", graph);
     ("smtlib", smtlib);
     ("micro", micro);
     ("exp", experiment)
    ]

let () = Command_unix.run main    
