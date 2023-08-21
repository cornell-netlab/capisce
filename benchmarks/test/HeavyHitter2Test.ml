open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type custom_metadata_t = {
  count_val1 : Var.t;
  count_val2 : Var.t;
  nhop_ipv4 : Var.t
}

let custom_metadata : custom_metadata_t = {
  count_val1 = Var.make "meta.custom_metadata.count_val2" 16;
  count_val2 = Var.make "meta.custom_metadata.count_val1" 16;
  nhop_ipv4 = Var.make "meta.custom_metadata.nhop_ipv4" 32;
}

type meta_t =  {
  custom_metadata : custom_metadata_t
}

let meta : meta_t = {custom_metadata}

let hh2_parser =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let parse_tcp =
    sequence [
      assign hdr.tcp.isValid btrue;
      transition_accept
    ]
  in
  let parse_ipv4 =
    sequence [
        assign hdr.ipv4.isValid btrue;
        (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
        ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 6 8))
          [ parse_tcp ]
          [ transition_accept ];
        transition_accept
      ]
  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
      ifte_seq (eq_ (var hdr.ethernet.etherType) (bvi 2048 16))
        [parse_ipv4]
        [transition_accept]
    ]

  in
  let start =
    sequence [
      assign hdr.ethernet.isValid bfalse;
      assign hdr.ipv4.isValid bfalse;
      assign hdr.tcp.isValid bfalse;
      parse_ethernet
    ]
  in
  start

let hh2_ingress fixed =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let set_heavy_hitter_count =
    [], Primitives.Action.[
        (* // Count the hash 1 for indexing *)
        assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid;
        assert_ @@ eq_ btrue @@ var hdr.tcp.isValid;
        (* hash(meta.custom_metadata.hash_val1, HashAlgorithm.csum16, (bit<16>)16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort }, (bit<32>)32w16); *)
        (* // Read the value in the register with that index *)
        (* heavy_hitter_counter1.read(meta.custom_metadata.count_val1, (bit<32>)meta.custom_metadata.hash_val1); *)
        (* // Incremet the value with 1 *)
        assign meta.custom_metadata.count_val1 @@ badd (var meta.custom_metadata.count_val1) (bvi 1 16);
        (* // Write the value back to the register with that index *)
        (* heavy_hitter_counter1.write((bit<32>)meta.custom_metadata.hash_val1, (bit<16>)meta.custom_metadata.count_val1); *)
        (* // Count the hash 2 for another indexing, similar to the first hash *)
        assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid;
        assert_ @@ eq_ btrue @@ var hdr.tcp.isValid;
        (* hash(meta.custom_metadata.hash_val2, HashAlgorithm.crc16, (bit<16>)16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort }, (bit<32>)32w16); *)
        (* heavy_hitter_counter2.read(meta.custom_metadata.count_val2, (bit<32>)meta.custom_metadata.hash_val2); *)
        assign meta.custom_metadata.count_val2 @@ badd (var meta.custom_metadata.count_val2) (bvi 1 16);
        (* heavy_hitter_counter2.write((bit<32>)meta.custom_metadata.hash_val2, (bit<16>)meta.custom_metadata.count_val2); *)
      ]
  in
  let set_heavy_hitter_count_table =
    instr_table (
      "set_heavy_hitter_count_table",
      [`Exact (Var.make "dummy" 1)], [set_heavy_hitter_count]
    )
  in
  let _drop =
    [], Primitives.Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let drop_heavy_hitter_table =
    instr_table (
      "drop_heavy_hitter_table",
      [],[_drop]
    )
  in
  let set_nhop  =
    let nhop_ipv4 = Var.make "nhop_ipv4" 32 in
    let port = Var.make "port" 9 in
    [nhop_ipv4; port], Primitives.Action.[
        assign meta.custom_metadata.nhop_ipv4 @@ var nhop_ipv4;
        assign standard_metadata.egress_spec @@ var port;
        assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8);
      ]
  in
  let ipv4_lpm =
    instr_table (
      "ipv4_lpm",
      [`Maskable hdr.ipv4.dstAddr], [set_nhop; _drop]
    )
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [dmac], Primitives.Action.[
        assign hdr.ethernet.dstAddr @@ var dmac
      ]
  in
  let forward =
    instr_table (
      "forward",
      [`Exact meta.custom_metadata.nhop_ipv4],[set_dmac; _drop]
    )
  in
  sequence [
    begin if fixed then assume @@ ands_ [
        eq_ btrue @@ var hdr.ipv4.isValid;
        eq_ btrue @@ var hdr.tcp.isValid;
      ]
    else skip end;
    set_heavy_hitter_count_table;
    ifte_seq (ands_ [
        ugt_ (var meta.custom_metadata.count_val1) (bvi 100 16);
        ugt_ (var meta.custom_metadata.count_val2) (bvi 100 16);
      ]) [
      drop_heavy_hitter_table;
    ] [
      ipv4_lpm;
      forward
    ]
  ]

let hh2_egress =
  (* HoareNet.skip *)
  let open HoareNet in
  let open Expr in
  let rewrite_mac =
    let smac = Var.make "smac" 48 in
    [smac], Primitives.Action.[
      assign hdr.ethernet.srcAddr @@ var smac
    ]
  in
  let _drop = [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let send_frame =
    instr_table ("send_frame",
                 [`Exact standard_metadata.egress_port],
                 [rewrite_mac; _drop]
                )
  in
  send_frame

let hh2 fixed =
  pipeline hh2_parser (hh2_ingress fixed) hh2_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations (hh2 true)
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer_buggy () =
  Printf.printf "GPL Program: %s ------\n" @@ HoareNet.to_string (hh2 false);
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (hh2 false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (hh2 true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (hh2 false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (hh2 true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Conc CPI is trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "heavy_hitter_2 annotations" `Quick test_annotations;
  Alcotest.test_case "heavy_hitter_2 infer enum buggy" `Quick test_infer_buggy;
  Alcotest.test_case "heavy_hitter_2 infer enum fixed" `Quick test_infer_fixed;
  Alcotest.test_case "heavy_hitter_2 infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "heavy_hitter_2 infer conc fixed" `Quick test_concolic_fixed;
]