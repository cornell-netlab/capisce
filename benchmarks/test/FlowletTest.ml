open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type ingress_metadata_t = {
  flow_ipg : Var.t;
  flowlet_lasttime : Var.t;
  flowlet_id : Var.t;
  ecmp_offset : Var.t;
  nhop_ipv4 : Var.t;
  flowlet_map_index : Var.t;
}

let ingress_metadata : ingress_metadata_t = {
  flow_ipg = Var.make "meta.ingress_metadata.flow_ipg" 32;
  flowlet_lasttime = Var.make "meta.ingress_metadata.flowlet_lasttime" 32;
  flowlet_id = Var.make "meta.ingress_metadata.flowlet_id" 16;
  ecmp_offset = Var.make "meta.ingress_metadata.ecmp_offset" 14;
  nhop_ipv4 = Var.make "meta.ingress_metadata.nhop_ipv4" 32;
  flowlet_map_index = Var.make "meta.ingress_metadata.flowlet_map_index" 13;
}

type intrinsic_metadata_t = {
  ingress_global_timestamp : Var.t
}

let intrinsic_metadata : intrinsic_metadata_t = {
  ingress_global_timestamp = Var.make "meta.intrinsic_metadata.ingress_global_timestamp" 48;
}

type meta_t =  {
  ingress_metadata : ingress_metadata_t;
  intrinsic_metadata : intrinsic_metadata_t;
}

let meta : meta_t = {ingress_metadata; intrinsic_metadata}

let flowlet_parser =
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

let flowlet_ingress fixed =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let lookup_flowlet_map = [], 
  Primitives.Action.[
      (* hash(meta.ingress_metadata.flowlet_map_index, HashAlgorithm.crc16, (bit<13>)13w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort }, (bit<13>)13w26); *)
      hash_  meta.ingress_metadata.flowlet_map_index "crc16" (bvi 0 13) [ var hdr.ipv4.srcAddr; var hdr.ipv4.dstAddr; var hdr.ipv4.protocol; var hdr.tcp.srcPort; var hdr.tcp.dstPort] (bvi 13 26) "lookup_flowlet_map";
      (* flowlet_id.read(meta.ingress_metadata.flowlet_id, (bit<32>)meta.ingress_metadata.flowlet_map_index); *)
      register_read "flowlet_id_lookup_flowlet_map" meta.ingress_metadata.flowlet_id (var meta.ingress_metadata.flowlet_map_index);
      [assign meta.ingress_metadata.flow_ipg @@ bslice 0 31 @@ var meta.intrinsic_metadata.ingress_global_timestamp];
      (* flowlet_lasttime.read(meta.ingress_metadata.flowlet_lasttime, (bit<32>)meta.ingress_metadata.flowlet_map_index); *)
      register_read "flowlet_lasttime_lookup_flowlet_map" meta.ingress_metadata.flowlet_lasttime (var meta.ingress_metadata.flowlet_map_index);
      [assign meta.ingress_metadata.flow_ipg @@ bsub (var meta.ingress_metadata.flow_ipg) (var meta.ingress_metadata.flowlet_lasttime)];
      (* flowlet_lasttime.write((bit<32>)meta.ingress_metadata.flowlet_map_index, (bit<32>)meta.intrinsic_metadata.ingress_global_timestamp); *)
      register_write "flowlet_lasttime_lookup_flowlet_map" (var meta.ingress_metadata.flowlet_map_index) (var meta.intrinsic_metadata.ingress_global_timestamp);
    ] |> List.concat
  in
  let flowlet = instr_table ("flowlet", [], [
    lookup_flowlet_map;
    nop (* Undefined default action, assuming nop *)
    ]) in
  let update_flowlet_id =
    [], Primitives.Action.[
        [assign meta.ingress_metadata.flowlet_id @@ badd (var meta.ingress_metadata.flowlet_id) (bvi 1 16)];
        (* flowlet_id.write((bit<32>)meta.ingress_metadata.flowlet_map_index, (bit<16>)meta.ingress_metadata.flowlet_id) *)
        register_write "flowlet_id_update_flowlet_id" (var meta.ingress_metadata.flowlet_map_index) (var meta.ingress_metadata.flowlet_id);
      ] |> List.concat
  in
  let new_flowlet = instr_table ("new_flowlet", [], [
    update_flowlet_id;
    nop (* Undefined default action, assuming nop *)
    ]) in
  let _drop = [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9;
    ]
  in
  let set_ecmp_select =
    let ecmp_base = Var.make "ecmp_base" 8 in
    let ecmp_count = Var.make "ecmp_count" 8 in
    [ecmp_base; ecmp_count],
      (* hash(meta.ingress_metadata.ecmp_offset, HashAlgorithm.crc16, (bit<10>)ecmp_base, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort, meta.ingress_metadata.flowlet_id }, (bit<20>)ecmp_count); *)
      hash_ meta.ingress_metadata.ecmp_offset "crc16" (var ecmp_base) [var hdr.ipv4.srcAddr; var hdr.ipv4.dstAddr; var hdr.ipv4.protocol; var hdr.tcp.srcPort; var hdr.tcp.dstPort; var meta.ingress_metadata.flowlet_id] (var ecmp_count) "set_ecmp_select";
  in
  let ecmp_group = instr_table (
      "ecmp_group",
      [`Maskable hdr.ipv4.dstAddr],
      [
        _drop; set_ecmp_select;
        nop (* Undefined default action, assuming nop *)
      ])
  in
  let set_nhop =
    let nhop_ipv4 = Var.make "nhop_ipv4" 32 in
    let port = Var.make "port" 9 in
    [nhop_ipv4; port], Primitives.Action.[
        assign meta.ingress_metadata.nhop_ipv4 @@ var nhop_ipv4;
        assign standard_metadata.egress_spec @@ var port;
        assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8);
    ]

  in
  let ecmp_nhop = instr_table (
      "ecmp_nhop",
      [`Exact meta.ingress_metadata.ecmp_offset],
      [
        _drop; set_nhop;
        nop (* Undefined default action, assuming nop *)
      ])
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [], Primitives.Action.[
        assign hdr.ethernet.dstAddr @@ var dmac
    ]
  in
  let forward = instr_table (
      "forward",
      [`Exact meta.ingress_metadata.nhop_ipv4],
      [
        set_dmac; _drop;
        nop (* Undefined default action, assuming nop *)
      ]) in
  sequence [
    begin if fixed then assume @@ ands_ [
        eq_ btrue @@ var hdr.ipv4.isValid;
        eq_ btrue @@ var hdr.tcp.isValid;
      ]
    else skip end;
    flowlet;
    ifte (ugt_ (var meta.ingress_metadata.flow_ipg) (bvi 50000 32))
      new_flowlet
      skip;
    ecmp_group;
    ecmp_nhop;
    forward
  ]

let flowlet_egress =
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
                 [
                  rewrite_mac; _drop;
                  nop (* Undefined default action, assuming nop *)
                  ])
  in
  send_frame

let flowlet fixed =
  pipeline flowlet_parser (flowlet_ingress fixed) flowlet_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations (flowlet true)
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer_buggy () =
  Printf.printf "GPL Program: %s ------\n" @@ HoareNet.to_string (flowlet false);
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (flowlet false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (flowlet true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (flowlet false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (flowlet true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Conc CPI is trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "flowlet annotations" `Quick test_annotations;
  Alcotest.test_case "flowlet infer enum buggy" `Quick test_infer_buggy;
  Alcotest.test_case "flowlet infer enum fixed" `Quick test_infer_fixed;
  Alcotest.test_case "flowlet infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "flowlet infer conc fixed" `Quick test_concolic_fixed;
]
