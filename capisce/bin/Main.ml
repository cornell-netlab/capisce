open Core
open Capisce
module Qe = Qe

let example (name : string) program : Command.t =
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
      Solver.z3_path := Option.value z3 ~default:(!Solver.z3_path);
      Log.smt "Using z3 binary at %s" @@ lazy (!Solver.z3_path);
      Solver.princess_path := Option.value princess ~default:(!Solver.princess_path);
      Log.smt "Using princess binary at %s" @@ lazy (!Solver.princess_path);
      Printf.printf "%s\n" name;
      let open DependentTypeChecker in
      let instrument p = 
        let p = if hv then HoareNet.assert_valids p else p in 
        let p = if df then HoareNet.track_assigns Programs.V1ModelUtils.standard_metadata.egress_spec p else p in 
        p
      in
      let algorithm p = 
        HoareNet.infer p None None ~qe:`Cegqe
      in
      let paths p =
        HoareNet.annotated_to_gpl p
        |> ASTs.GPL.count_paths
        |> Bigint.to_string
      in
      let st = Clock.start () in
      let phi = 
        try 
          program |> 
          instrument |>
          algorithm
        with
        | Failure msg -> 
          if String.(msg = "unsolveable") then
            BExpr.false_
          else failwith msg
      in
      let num_cexs = !Qe.num_cexs |> Bigint.to_string in
      let time = Clock.stop st  |> Float.to_string in
      let filename f = Printf.sprintf "%s/%s_%s_%s" out name "cegps" f in
      Out_channel.write_all (filename "formula") ~data:(BExpr.to_smtlib phi);
      Out_channel.write_all (filename "size") ~data:(Int.to_string @@ BExpr.size phi);
      Out_channel.write_all (filename "tot_paths") ~data:(paths program);
      Out_channel.write_all (filename "count_paths") ~data:(num_cexs);
      Out_channel.write_all (filename "time") ~data:time;
      if replay then
        let time_series = Qe.replay (!Qe.data) (program |> instrument |> HoareNet.annotated_to_gpl |> ASTs.GPL.encode_tables) in 
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

let examples =
  let open Programs in 
  let programs = [
    "ecmp", ECMP.ecmp;
    "netpaxos-acceptor", NetpaxosAcceptor.netpaxos_acceptor;
    "resubmit", Resubmit.resubmit;
    "ndp-router",  NDPRouter.ndp_router;
    "heavy-hitter-1", HeavyHitter1.heavy_hitter_1;
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
  name, example name program

let main =
  Command.group ~summary:"research toy for exploring verification & synthesis of p4 programs"
    [("smtlib", smtlib);
     ("exp", examples)
    ]

let () = Command_unix.run main    
