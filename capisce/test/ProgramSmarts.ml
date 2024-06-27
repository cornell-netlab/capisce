open Core
open Pbench


let includes = ["./examples/includes"]

let table_programs = [
  "ecmp_2_noselector.p4", `Quick;
  "netpaxos_acceptor_16_sized_ints.p4", `Quick;
  "resubmit.p4", `Quick;
  "heavy_hitter_1.p4", `Quick;
  "arp_no_consts_sized_ints_exitless.p4", `Quick;
  "07-MultiProtocol.p4", `Slow;
  "mc_nat_16.p4", `Quick;
  "ts_switching_16_no_range.p4", `Quick;
  "heavy_hitter_2_sized_ints.p4", `Quick;
  "flowlet_sized_ints.p4", `Quick;
]

let hoare_programs = [
  "hula_no_consts.p4", `Quick;
  "linearroad_16_sized_ints_no_range.p4", `Slow;
  "netchain_16_parser_unroll.p4", `Slow;
  "simple_nat.skip", `Slow;
]

let zero_annihilation () =
  let open ASTs in
  let open GCL in
  let open BExpr in
  let open Expr in
  let cmds = [
    assume @@ eq_ (var @@ Var.make "_symb$x" 1) @@ Expr.bvi 1 1;
    assert_ BExpr.false_
  ] in
  Alcotest.(check Equivalences.gcl) "Same program"
    (sequence cmds)
    (Seq cmds)

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "assume phi($x);0 ≠ 0" `Quick zero_annihilation
]
