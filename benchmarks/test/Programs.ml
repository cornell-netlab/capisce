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

let table_tests : unit Alcotest.test_case list =
  let open List.Let_syntax in
  let%map (filename, speed) = table_programs in
  let test () : unit =
    let filepath = "./examples/bf4_failing/" ^ filename in
    let gas = 1000 in
    let unroll = 10 in
    let coq_gcl = P4Parse.tbl_abstraction_from_file includes filepath gas unroll false false in
    let gpl = Tuple2.map ~f:(Translate.gcl_to_gpl) coq_gcl in
    let gpl = ASTs.GPL.optimize_seq_pair gpl in
    let _ : BExpr.t = Qe.table_infer ~sfreq:100 ~prsr:`Skip ~fn:None gpl in
    Alcotest.(check pass) "completed" true true
  in
  Alcotest.test_case ("table: " ^ filename) speed test

let hoare_tests : unit Alcotest.test_case list =
  let open DependentTypeChecker in
  let open List.Let_syntax in
  let%map (filename, speed) = hoare_programs in
  let test () : unit =
    let filepath = "./examples/bf4_failing/" ^ filename in
    let gas = 1000 in
    let unroll = 10 in
    let coq_gcl = P4Parse.tbl_abstraction_from_file includes filepath gas unroll false true in
    let (hprsr, hpipe) = Tuple2.map ~f:(Translate.gcl_to_hoare) coq_gcl in
    let hoarenet =  HoareNet.seq hprsr hpipe in
    let hoarenet = HoareNet.normalize_names hoarenet in
    let hoarenet = HoareNet.zero_init hoarenet in
    let hoarenet = HoareNet.optimize hoarenet in
    if  HoareNet.check_annotations hoarenet then
      let _ : BExpr.t = HoareNet.infer hoarenet None None in
      Alcotest.(check pass) "completed" true true
    else
      failwith "unsound annotations"
  in
  Alcotest.test_case ("hoare " ^ filename) speed test


let tests = table_tests @ hoare_tests
