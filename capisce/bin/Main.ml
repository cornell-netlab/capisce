open Core
open Capisce
module Qe = Qe

let experiment : Command.t =
  let open Programs in 
  let open Command.Let_syntax in
  Command.basic ~summary:"runs hand-translated experiment"
  [%map_open
    let name = flag "-name" (required string) ~doc:"S experiment name"
    and out = flag "-out" (required string) ~doc:"F path to result info"
    and enum = flag "-enum" (no_arg) ~doc:"use naive enumeration method (DEPRECATED)"
    and replay = flag "-replay" (no_arg) ~doc:"log timestamps for each path condition. Measure number of paths covered by each condition."
    and z3 = flag "-z3" (optional string) ~doc:("Z the path to the Z3 binary. default is " ^ !Solver.z3_path)
    and princess = flag "-princess" (optional string) ~doc:("P the path to the princess binary. default is " ^ !Solver.princess_path)
    in fun () ->
      Solver.z3_path := Option.value z3 ~default:(!Solver.z3_path);
      Log.smt "Using z3 binary at %s" @@ lazy (!Solver.z3_path);
      Solver.princess_path := Option.value princess ~default:(!Solver.princess_path);
      Log.smt "Using princess binary at %s" @@ lazy (!Solver.princess_path);
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
        HoareNet.infer p None None ~qe:(if enum then `Enum else `Cegqe)
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

let main =
  Command.group ~summary:"research toy for exploring verification & synthesis of p4 programs"
    [("smtlib", smtlib);
     ("exp", experiment)
    ]

let () = Command_unix.run main    
