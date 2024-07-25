open Core
open Capisce
open ASTs.GPL
open V1ModelUtils

type intrinsic_metadata_t = {
  mcast_grp : Var.t;
  egress_rid : Var.t
}

let intrinsic_metadata : intrinsic_metadata_t = {
  mcast_grp = Var.make "meta.intrinsic_metadata.mcast_grp" 16;
  egress_rid = Var.make "meta.intrinsic_metadata.egress_rid" 16;
}

type meta_t =  {
  intrinsic_metadata : intrinsic_metadata_t
}

let meta : meta_t = {intrinsic_metadata}

let mc_nat_parser =
  let open BExpr in
  let open Expr in
  let parse_udp =
    sequence [
      assign hdr.udp.isValid btrue;
      transition_accept
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
      parse_ethernet
    ]
  in
  start

let mc_nat_psm =
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
      bvi 17 8, "parse_udp";
    ] "accept"
    ;
    state "parse_udp" hdr.udp.isValid @@
    direct "accept"
  ]

let mc_nat_ingress fixed =
  let open BExpr in
  let open Expr in
  let _drop = [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let set_output_mcg =
    let mcast_group = Var.make "mcast_group" 16 in
    [mcast_group], Primitives.Action.[
        assign meta.intrinsic_metadata.mcast_grp @@ var mcast_group
      ]
  in
  let set_mcg =
    table "set_mcg"
         [ hdr.ipv4.dstAddr, Exact ]
         [set_output_mcg; _drop;
          nop (*Unspecified default action, assuming nop*)
         ]
  in
  sequence [
    if fixed then assume @@ eq_ btrue @@ var hdr.ipv4.isValid else skip;
    set_mcg
  ]


let mc_nat_egress =
  (* let open BExpr in *)
  let open Expr in
  let _drop = [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let do_nat =
    let dst_ip = Var.make "dst_ip" 32 in
    [dst_ip], Primitives.Action.[
        assign hdr.ipv4.dstAddr @@ var dst_ip;
        assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8)
      ]
  in
  let nat_table =
    table "nat_table"
      [ meta.intrinsic_metadata.egress_rid, Exact;
        hdr.ipv4.dstAddr, Exact
      ] [
        do_nat; _drop;
        nop (*Unspecified default action, assuming nop*)
      ]
  in
  sequence [
    nat_table
  ]


let mc_nat fixed =
  mc_nat_psm, mc_nat_ingress fixed, mc_nat_egress
