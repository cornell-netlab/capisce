open Core
open Capisce
open ASTs.GPL
open V1ModelUtils


type meta_t = {
    do_forward : Var.t;
    ipv4_sa : Var.t;
    ipv4_da : Var.t;
    tcp_sp : Var.t;
    tcp_dp : Var.t;
    nhop_ipv4 : Var.t;
    if_ipv4_addr : Var.t;
    if_mac_addr : Var.t;
    is_ext_if : Var.t;
    tcpLength : Var.t;
    if_index : Var.t;
    initial_egress_spec : Var.t
}

let meta : meta_t =
  let f x b = Var.make (Printf.sprintf "meta.meta.%s" x) b in
  {
    do_forward = f "do_forward" 1;
    ipv4_sa = f "ipv4_sa" 32;
    ipv4_da = f "ipv4_da" 32;
    tcp_sp = f "tcp_sp" 16;
    tcp_dp = f "tcp_dp" 16;
    nhop_ipv4 = f "nhop_ipv4" 32;
    if_ipv4_addr = f "if_ipv4_addr" 32;
    if_mac_addr = f "if_mac_addr" 48;
    is_ext_if = f "is_ext_if" 1;
    tcpLength = f "tcpLength" 16;
    if_index = f "if_index" 8;
    initial_egress_spec = f "initial_egress_spec" 9;
}

type metadata_t = {
    meta : meta_t
}

let meta : metadata_t = {
    meta;
}


let simple_nat_parser =
  let open Expr in
  let parse_tcp =
    sequence [
      assign hdr.tcp.isValid btrue;
      assign meta.meta.tcp_sp @@ var hdr.tcp.srcPort;
      assign meta.meta.tcp_dp @@ var hdr.tcp.dstPort;
      transition_accept
    ]
  in
  let parse_ipv4 =
    sequence [
      assign hdr.ipv4.isValid btrue;
      assign meta.meta.ipv4_sa @@ var hdr.ipv4.srcAddr;
      assign meta.meta.ipv4_da @@ var hdr.ipv4.dstAddr;
      assign meta.meta.tcpLength @@ bsub (var hdr.ipv4.totalLen) (bvi 20 16);
      select (var hdr.ipv4.protocol) [
        bvi 6 8, parse_tcp
      ] transition_accept
    ]

  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      select (var hdr.ethernet.etherType) [
        bvi 2048 16, parse_ipv4
      ] transition_accept
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

let simple_nat_ingress =
  let open BExpr in
  let open Expr in
  let open Primitives in
  let _drop = [], [mark_to_drop] in
  let set_if_info =
    let ipv4_addr = Var.make "ipv4_addr" 32 in
    let mac_addr = Var.make "mac_addr" 48 in
    let is_ext = Var.make "is_ext" 1 in
    [ipv4_addr; mac_addr; is_ext],
    Action.[
      assign meta.meta.if_ipv4_addr @@ var ipv4_addr;
      assign meta.meta.if_mac_addr @@ var mac_addr;
      assign meta.meta.is_ext_if @@ var is_ext
    ]
  in
  let if_info = 
    table "if_info" 
      [
        meta.meta.if_index, Exact
      ] [
        set_if_info; _drop;
        nop (* Unspecified default action, assuming nop *)
      ]
  in
  let nat_miss_int_to_ext = [], [
        (* clone3(CloneType.I2E, (bit<32>)32w250, { standard_metadata }); *)
    ]
  in
  let nat_miss_ext_to_int = [], Action.[
      assign meta.meta.do_forward @@ bvi 0 1;
      mark_to_drop;
    ]
  in
  let nat_hit_int_to_ext = [], [
      (* clone3(CloneType.I2E, (bit<32>)32w250, { standard_metadata }); *)
    ]
  in
  let nat_hit_ext_to_int =
    let dstAddr = Var.make "dstAddr" 32 in
    let dstPort = Var.make "dstPort" 16 in
    [dstAddr; dstPort],
    Action.[
        assign meta.meta.do_forward btrue;
        assign meta.meta.ipv4_da @@ var dstAddr;
        assign meta.meta.tcp_dp @@ var dstPort;
      ]
  in
  let nat_no_nat = [], Action.[
      assign meta.meta.do_forward btrue;
    ]
  in
  let nat =
    table "nat"
      [ meta.meta.is_ext_if, Exact;
        hdr.ipv4.isValid, Exact;
        hdr.tcp.isValid, Exact;
        hdr.ipv4.srcAddr, Maskable;
        hdr.ipv4.dstAddr, Maskable;
        hdr.tcp.srcPort, Maskable;
        hdr.tcp.dstPort, Maskable
      ]
      [ _drop;
        nat_miss_int_to_ext;
        nat_miss_ext_to_int;
        nat_hit_int_to_ext;
        nat_hit_ext_to_int;
        nat_no_nat;
        nop; (*Unspeecified default action assuming nop*)
      ]
  in
  let set_nhop =
    let nhop_ipv4 = Var.make "nhop_ipv4" 32 in
    let port = Var.make "port" 9 in
    [nhop_ipv4; port],
    Action.[
      assign meta.meta.nhop_ipv4 @@ var nhop_ipv4;
      assign standard_metadata.egress_spec @@ var port;
      assign hdr.ipv4.ttl @@ bsub (var hdr.ipv4.ttl) (bvi 1 8);
    ]
  in
  let ipv4_lpm = 
    table "ipv4_lpm" 
    [
      meta.meta.ipv4_da, MaskableDegen
    ] [
      set_nhop; _drop;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [dmac], Action.[
        assign hdr.ethernet.dstAddr @@ var dmac
    ]
  in
  let forward = 
    table "forward" [
      meta.meta.nhop_ipv4, Exact
    ] [
      set_dmac; _drop;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  sequence [
    if_info;
    nat;
    ifte_seq (eq_ (var meta.meta.do_forward) btrue) [
      ifte_seq (not_ (eq_ (var hdr.ipv4.ttl) (bvi 0 8))) [
        ipv4_lpm;
        forward
      ] []
    ] []
  ]


let simple_nat_egress =
  let open BExpr in
  let open Expr in
  let open Primitives in
  let _drop =
    [], Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let do_rewrites =
    let smac = Var.make "smac" 48 in
    [smac], Action.[
      assign hdr.cpu_header.isValid bfalse;
      assign hdr.ethernet.srcAddr @@ var smac;
      assign hdr.ipv4.srcAddr @@ var meta.meta.ipv4_sa;
      assign hdr.ipv4.dstAddr @@ var meta.meta.ipv4_da;
      assign hdr.tcp.srcPort @@ var meta.meta.tcp_sp;
      assign hdr.tcp.dstPort @@ var meta.meta.tcp_dp;
    ]
  in
  let send_frame =
    table "send_frame"
      [standard_metadata.egress_port, Exact]
      [
        do_rewrites; _drop;
        nop (*Unspecified default action, assuming nop*)
      ]
  in
  let do_cpu_encap = [], Action.[
      assign hdr.cpu_header.isValid btrue;
      assign hdr.cpu_header.preamble @@ bvi 0 64;
      assign hdr.cpu_header.device @@ bvi 0 8;
      assign hdr.cpu_header.reason @@ bvi 171 8; (*0xab*)
      assign hdr.cpu_header.if_index @@ var meta.meta.if_index
    ]
  in
  let send_to_cpu =
    table "send_to_cpu" [] [
      do_cpu_encap;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  ifte_seq (eq_ (var standard_metadata.instance_type) (bvi 0 32)) [
    send_frame
  ] [
    send_to_cpu
  ]

let simple_nat =
  pipeline simple_nat_parser simple_nat_ingress simple_nat_egress
