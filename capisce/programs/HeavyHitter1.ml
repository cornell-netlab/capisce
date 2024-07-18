open Core
open Capisce
open ASTs.GPL
open V1ModelUtils


type custom_metadata_t = {
  nhop_ipv4 : Var.t
}

let custom_metadata : custom_metadata_t = {
  nhop_ipv4 = Var.make "meta.routing_metadata.nhop_ipv4" 32
}

type metadata_t = {
  custom_metadata: custom_metadata_t
}
let meta : metadata_t = {custom_metadata}


let hh_parser =
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

let hh_ingress =
  (* let open BExpr in *)
  let open Expr in
  let count_action =
    let idx = Var.make "idx" 32 in
    [idx], [
      (* ip_src_counter.count((bit<32>) idx) *)
    ]
  in
  let _drop =
    [], Primitives.Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let count_table =
    table "count_table" [
      hdr.ipv4.srcAddr, Maskable
    ] [
      count_action; _drop;
      nop (* Unspecified default action, assuming noop *)
    ]
  in
  let set_nhop =
    let nhop_ipv4 = Var.make "set_nhop" 32 in
    let port = Var.make "port" 9 in
    [nhop_ipv4; port],
      Primitives.Action.[
        assign meta.custom_metadata.nhop_ipv4 @@ var nhop_ipv4;
        assign standard_metadata.egress_spec @@ var port;
        (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
        assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8)
      ]
  in
  let ipv4_lpm =
    table "ipv4_lpm" [
      hdr.ipv4.dstAddr, Maskable
    ] [
      set_nhop; _drop;
      nop (* Unspecified default action, assuming noop *)
    ]
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [dmac], Primitives.Action.[
        (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
        assign hdr.ethernet.dstAddr @@ var dmac
      ]
  in
  let forward =
    table "forward" [
      meta.custom_metadata.nhop_ipv4, Exact
    ] [
      set_dmac; _drop;
      nop (* Unspecified default action, assuming noop *)
    ]
  in
  sequence [
    count_table;
    ipv4_lpm;
    forward
  ]

let hh_egress =
  (* let open BExpr in *)
  let open Expr in
  let rewrite_mac =
    let smac = Var.make "smac" 48 in
    [smac], Primitives.Action.[
      assign hdr.ethernet.srcAddr @@ var smac
    ]
  in
  let _drop =
    [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let send_frame =
    table "send_frame" 
      [
        standard_metadata.egress_port, Exact
      ] [
        rewrite_mac; _drop;
        nop (* Unspecified default action, assuming noop *)
      ]
  in
  sequence [
    send_frame
  ]

let heavy_hitter_1 =
  pipeline hh_parser hh_ingress hh_egress
