open Core
open Capiscelib
open DependentTypeChecker
open V1ModelUtils

type ingress_metadata_t = {
  drop : Var.t;
  egress_port : Var.t;
  packet_type : Var.t;
  fwded : Var.t;
}

let ing_metadata = {
  drop = Var.make "meta.ing_metadata.drop" 1;
  egress_port = Var.make "meta.ing_metadata.egress_port" 9;
  packet_type = Var.make "meta.ing_metadata.packet_type" 4;
  fwded = Var.make "forwarded" 1;
}

type my_metadata_t = {ing_metadata : ingress_metadata_t}
let meta : my_metadata_t = {ing_metadata}

let multiproto_parser =
  let open HoareNet in
  let open Expr in
  (* start *)
  let parse_icmp =
    sequence [
      assign hdr.icmp.isValid btrue;
      transition_accept
    ]
  in
  let parse_tcp =
    sequence [
      assign hdr.icmp.isValid btrue;
      transition_accept
    ]
  in
  let parse_udp =
    sequence [
      assign hdr.udp.isValid btrue;
      transition_accept
    ]
  in
  let parse_ipv4 =
    let discriminee =
      (* bconcat (var hdr.ipv4.fragOffset) @@ *)
      bconcat (var hdr.ipv4.ihl) @@
      (var hdr.ipv4.protocol)
    in
    let icmp_case =
      (*13w0x0 &&& 13w0x0,*)
      bconcat (bvi 5 4) @@
      bvi 1 8
    in
    let tcp_case =
      bconcat (bvi 5 4) @@
      bvi 6 8
    in
    let udp_case =
      bconcat (bvi 5 4) @@
      (bvi 17 8)
    in
    sequence [
      assign hdr.ipv4.isValid btrue;
      select discriminee [
        icmp_case, parse_icmp;
        tcp_case, parse_tcp;
        udp_case, parse_udp;
      ] transition_accept
    ]
  in
  let parse_ipv6 =
    sequence [
      assign hdr.ipv6.isValid btrue;
      select (var hdr.ipv6.nextHdr) [
        bvi  1 8, parse_icmp;
        bvi  6 8, parse_tcp;
        bvi 17 8, parse_udp
      ] transition_accept
    ]
  in
  let parse_vlan_tag =
    sequence [
      assign hdr.vlan_tag.isValid btrue;
      select (var hdr.vlan_tag.etherType) [
        bvi  2048 16, parse_ipv4;
        bvi 34525 16, parse_ipv6
      ] transition_accept
    ]
  in
  let start =
    sequence [
      assign meta.ing_metadata.fwded bfalse;
      assign hdr.ethernet.isValid bfalse;
      assign hdr.ipv4.isValid bfalse;
      assign hdr.tcp.isValid bfalse;
      assign hdr.ethernet.isValid btrue;
      select (var hdr.ethernet.etherType) [
        bvi 33024 16, parse_vlan_tag;
        bvi 37120 16, parse_vlan_tag;
        bvi  2048 16, parse_ipv4;
        bvi 34525 16, parse_ipv6;
      ] transition_accept
    ]
  in
  start

let multiproto_ingress =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let open Primitives in
  let packet_type i =
    [], Action.[
        assign meta.ing_metadata.packet_type @@ bvi i 4
      ]
  in
  let l2_packet   = packet_type 0 in
  let ipv4_packet = packet_type 1 in
  let ipv6_packet = packet_type 2 in
  let mpls_packet = packet_type 3 in
  let mim_packet  = packet_type 4 in
  let ethertype_match =
    instr_table ("ethertype_match",
                 [`Exact hdr.ethernet.etherType],
                 [l2_packet;
                  ipv4_packet; ipv6_packet;
                  mpls_packet; mim_packet; 
                  nop (* Unspecified default action, assuming  noop *)
                 ]
                )
  in
  let _drop = [], Action.[
      assign meta.ing_metadata.drop btrue
    ]
  in
  let set_egress_port =
    let egress_port = Var.make "egress_port" 9 in
    [egress_port], Action.[
        assign meta.ing_metadata.egress_port @@ var egress_port
      ]
  in
  let _match name key =
    instr_table (name, [`Exact key], [nop; set_egress_port])
  in
  let ipv4_match = _match "ipv4_match" hdr.ipv4.dstAddr in
  let ipv6_match = _match "ipv6_match" hdr.ipv6.dstAddr in
  let l2_match   = _match "l2_match"   hdr.ethernet.dstAddr in
  let _check name key =
    instr_table (name, [`Exact key], [nop; _drop])
    (*  none of the check tables have specified default actions, assuming noop *)
    (*  no change made since they already have   noop *)
  in
  let  tcp_check = _check "tcp_check"  hdr.tcp.dstPort in
  let  udp_check = _check "udp_check"  hdr.udp.dstPort in
  let icmp_check = _check "icmp_check" hdr.icmp.type_ in
  let discard = [], Action.[
      assign meta.ing_metadata.fwded btrue;
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let send_packet = [], Action.[
      assign meta.ing_metadata.fwded btrue;
      assign standard_metadata.egress_spec @@ var meta.ing_metadata.egress_port
    ]
  in
  let set_egress =
    instr_table ("set_egress",
                  [`Exact meta.ing_metadata.drop],
                  [
                    discard; send_packet;
                    nop; (*  unspecified default action, assuming noop *)
                  ]
                )
  in
  sequence [
    ethertype_match;
    select (var @@ Var.make "_symb$ethertype_match$action" 3) [
      bvi 1 3, ipv4_match;
      bvi 3 3, ipv6_match;
      bvi 2 3, ipv6_match;
    ] l2_match;
    ifte_seq (eq_ btrue @@ var hdr.tcp.isValid) [
      tcp_check
    ] [
      ifte_seq (eq_ btrue @@ var hdr.udp.isValid) [
        udp_check;
      ] [
        ifte (eq_ btrue @@ var hdr.icmp.isValid)
          icmp_check
          skip
      ]
    ];
    set_egress;
    assert_ @@ eq_ btrue @@ var meta.ing_metadata.fwded; 
  ]

let multiproto_egress =
  let open HoareNet in
  skip

let multiprotocol =
  pipeline multiproto_parser multiproto_ingress multiproto_egress
  |> HoareNet.assert_valids
