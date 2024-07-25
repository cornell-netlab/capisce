open Core
open Capisce
open ASTs.GPL
open V1ModelUtils

let ts_switching_parser =
  let open BExpr in
  let open Expr in
  let parse_rtp =
    sequence [
      assign hdr.rtp.isValid btrue;
      transition_accept
    ]
  in
  let parse_udp =
    sequence [
      assign hdr.udp.isValid btrue;
      parse_rtp;
    ]
  in
  let parse_ipv4 =
    sequence [
        assign hdr.ipv4.isValid btrue;
        ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 17 8))
          [ parse_udp ]
          [ transition_accept ];
        transition_accept
      ]
  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      ifte_seq (eq_ (var hdr.ethernet.etherType) (bvi 2048 16))
        [parse_ipv4]
        [transition_accept]
    ]

  in
  let start =
    sequence [
      assign hdr.ethernet.isValid bfalse;
      assign hdr.ipv4.isValid bfalse;
      assign hdr.udp.isValid bfalse;
      assign hdr.rtp.isValid bfalse;
      parse_ethernet
    ]
  in
  start

let ts_switching_psm =
  let open EmitP4.Parser in 
  let open Expr in 
  of_state_list [
    noop_state "start" "parse_ethernet"
    ;
    state "parse_ethernet" hdr.ethernet.isValid @@
    select hdr.ethernet.etherType [
      bvi 2048 16, "parse_ipv4"
    ] "accept"
    ;
    state "parse_ipv4" hdr.ipv4.isValid @@
    select hdr.ipv4.protocol [
      bvi 17 8, "parse_udp"
    ] "accept"
    ;
    state "parse_udp" hdr.udp.isValid @@
    direct "parse_rtp"
    ;
    state "parse_rtp" hdr.rtp.isValid @@
    direct "accept"
  ]

let ts_switching_ingress fixed =
  let open BExpr in
  let open Expr in
  let _drop_0 = [], Primitives.Action.[
      (* my_direct_counter.count() *)
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let take_video_0 =
    let dst_ip = Var.make "dst_ip" 32 in
    [], Primitives.Action.[
        (* my_direct_counter.count() *)
        assign standard_metadata.egress_spec @@ bvi 1 9;
        assign hdr.ipv4.dstAddr @@ var dst_ip
      ]
  in
  let schedule_table =
    table "schedule_table"
      [ 
        hdr.ipv4.dstAddr, Exact;
        hdr.rtp.timestamp, Maskable
      ] [
        take_video_0; _drop_0;
        nop   (* Unspecified default action, assuming nop *)
      ]
  in
  sequence [
    if fixed then assume @@ ands_ [
        eq_ btrue @@ var hdr.rtp.isValid;
      ]
    else skip;
    schedule_table
  ]


let ts_switching_egress =
  skip

let ts_switching fixed =
  ts_switching_psm, ts_switching_ingress fixed, ts_switching_egress
