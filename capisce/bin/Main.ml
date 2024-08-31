open Core
open Capisce
module Qe = Qe

let example (name : string) (prsr, ingr, egr) : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:("runs example " ^ name)
  [%map_open
    let out = flag "-out" (required string) ~doc:"F path to result info"
    and replay = flag "-replay" (no_arg) ~doc:"log timestamps for each path condition. Measure number of paths covered by each condition."
    and z3 = flag "-z3" (optional string) ~doc:("Z the path to the Z3 binary. default is " ^ !Solver.z3_path)
    and princess = flag "-princess" (optional string) ~doc:("P the path to the princess binary. default is " ^ !Solver.princess_path)
    and hv = flag "-hv" (no_arg) ~doc:"instrument example program to check the header validity property"
    and df = flag "-df" (no_arg) ~doc:"instrument example program to check the determined forwarding property"
    in fun () ->
      let program = Programs.V1ModelUtils.(linearize @@ pipeline_psm prsr ingr egr) in
      Solver.z3_path := Option.value z3 ~default:(!Solver.z3_path);
      Log.smt "Running z3 via %s" @@ lazy (Solver.z3_exe ());
      Solver.princess_path := Option.value princess ~default:(!Solver.princess_path);
      Log.smt "Running princess via %s" @@ lazy (Solver.princess_exe ());
      Printf.printf "%s\n" name;
      let open ASTs in
      let instrument gcl = 
        assert (not (hv && df));
        let gcl = if hv then GCL.assert_valids gcl else gcl in 
        let gcl = if df then GCL.track_assigns Programs.V1ModelUtils.standard_metadata.egress_spec gcl else gcl in 
        gcl
      in
      let algorithm = Qe.cegqe in
      let paths p =
        ASTs.GPL.count_paths p
        |> Bigint.to_string
      in
      let st = Clock.start () in
      let instrumented_and_specified_program =
        program |> 
        (if not hv then GPL.exactify else Fn.id ) |>
        GPL.encode_tables |> 
        instrument
      in
      let phi = 
        try 
        instrumented_and_specified_program
        |> algorithm
        with
        | Failure msg -> 
          if String.(msg = "unsolveable") then
            BExpr.false_
          else failwith msg
      in
      let time = Clock.stop st  |> Float.to_string in
      let num_cexs = !Qe.num_cexs |> Bigint.to_string in
      let filename f = Printf.sprintf "%s/%s_%s_%s" out name "cegps" f in
      Out_channel.write_all (filename "formula") ~data:(BExpr.to_smtlib phi);
      Out_channel.write_all (filename "size") ~data:(Int.to_string @@ BExpr.size phi);
      Out_channel.write_all (filename "tot_paths") ~data:(paths program);
      Out_channel.write_all (filename "count_paths") ~data:(num_cexs);
      Out_channel.write_all (filename "time") ~data:time;
      if replay then
        let time_series = Qe.replay (!Qe.data) instrumented_and_specified_program in 
        let time_series_str = List.map time_series ~f:(fun (t,n) -> Printf.sprintf "%f, %d\n" t n) |> String.concat ~sep:"" in 
        Out_channel.write_all (filename "completion") ~data:(time_series_str)
  ]

let smtlib : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:"Debugging frontend for smtlib parser"
    [%map_open
     let source = anon ("smtlib source file" %: string) in
         fun () ->
         let smtast = SmtParser.parse source () in
         let b = SmtAst.translate smtast ~cvs:[] ~dvs:[] in
         let b = BExpr.simplify b in
         Printf.printf "%s\n%!" (BExpr.to_smtlib b);
    ]

let command_for_each_example ~f =
  let open Programs in 
  let programs = [
    "ecmp", ECMP.ecmp false;
    "ecmp-fixed", ECMP.ecmp true;
    "netpaxos-acceptor", NetpaxosAcceptor.netpaxos_acceptor;
    "resubmit", Resubmit.resubmit;
    "ndp-router",  NDPRouter.ndp_router;
    "heavy-hitter-1", HeavyHitter1.heavy_hitter_1 false;
    "heavy-hitter-1-fixed", HeavyHitter1.heavy_hitter_1 true;
    "arp", Arp.arp;
    "07-multiprotocol", Multiprotocol.multiprotocol;
    "mc-nat", MCNat.mc_nat false;
    "mc-nat-fixed", MCNat.mc_nat true;
    "ts-switching", TSSwitching.ts_switching false;
    "ts-switching-fixed", TSSwitching.ts_switching true;
    "heavy-hitter-2", HeavyHitter2.heavy_hitter_2 false;
    "heavy-hitter-2-fixed", HeavyHitter2.heavy_hitter_2 true;
    "flowlet", Flowlet.flowlet false;
    "flowlet-fixed", Flowlet.flowlet true;
    "hula", Hula.hula false;
    "hula-fixed", Hula.hula true;
    "linearroad", Linearroad.linearroad false;
    "linearroad-fixed", Linearroad.linearroad true;
    "netchain", NetChain.netchain;
    "simple-nat", SimpleNat.simple_nat;
    "fabric", Fabric.fabric false;
    "fabric-fixed", Fabric.fabric true;
  ]
  in
  Command.group ~summary:"Example programs" @@
  let open List.Let_syntax in 
  let%map name, program = programs in 
  f name program

let run_examples = 
  command_for_each_example
  ~f:(fun name program -> 
    name, example name program
  )

let serialize (name : string) (prsr, ingr, egr) : Command.t =
  let open Command.Let_syntax in
  Command.basic ~summary:("serializes example " ^ name ^ " to the specified format")
  [%map_open
    let p4 = flag "-p4" no_arg ~doc:"set output format to p4"
    in fun () ->
    let serialized = if p4 then
      EmitP4.emit prsr ingr egr
    else 
      let open Programs.V1ModelUtils in 
      pipeline_psm prsr ingr egr |>
      linearize |>
      ASTs.GPL.to_string
    in
    serialized |> 
    Printf.printf "%s\n%!";
  ]

let serialize_examples =
  command_for_each_example
  ~f:(fun name pipeline -> 
      name, serialize name pipeline
    )

let main =
  Command.group ~summary:"research toy for exploring verification & synthesis of p4 programs"
    [("smtlib", smtlib);
     ("exp", run_examples);
     ("emit", serialize_examples)     
    ]

let () = Command_unix.run main    
