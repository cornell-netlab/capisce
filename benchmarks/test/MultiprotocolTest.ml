open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type ingress_metadata_t = {
  drop : Var.t;
  egress_port : Var.t;
  packet_type : Var.t
}

let ing_metadata = {
  drop = Var.make "meta.ing_metadata.drop" 1;
  egress_port = Var.make "meta.ing_metadata.egress_port" 9;
  packet_type = Var.make "meta.ing_metadata.packet_type" 4;
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
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let send_packet = [], Action.[
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
    set_egress
  ]

let multiproto_egress =
  let open HoareNet in
  skip

let multiproto =
  pipeline multiproto_parser multiproto_ingress multiproto_egress
  |> HoareNet.assert_valids

let funky_path () =
  let open ASTs.GCL in
  let open BExpr in
  let open Expr in
  sequence [
    (* parse_result:=(_ bv0 1); *)
    (* hdr.ethernet.isValid:=(_ bv0 1); *)
    (* hdr.ipv4.isValid:=(_ bv0 1); *)
    (* hdr.tcp.isValid:=(_ bv0 1); *)
    (* hdr.ethernet.isValid:=(_ bv1 1); *)
    (* assert_ (= (_ bv1 1) hdr.ethernet.isValid); *)
    assume (eq_ (bvi 33024 16) (var hdr.ethernet.etherType));
    (* hdr.vlan_tag.isValid:=(_ bv1 1); *)
    (* assert_ (= (_ bv1 1) hdr.vlan_tag.isValid); *)
    (* assume (not  (= (_ bv2048 16) hdr.vlan_tag.etherType)); *)
    (* assert_ (= (_ bv1 1) hdr.vlan_tag.isValid); *)
    (* assume (= (_ bv34525 16) hdr.vlan_tag.etherType); *)
    (* hdr.ipv6.isValid:=(_ bv1 1); *)
    (* assert_ (= (_ bv1 1) hdr.ipv6.isValid); *)
    (* assume (not  (= (_ bv1 8) hdr.ipv6.nextHdr)); *)
    (* assert_ (= (_ bv1 1) hdr.ipv6.isValid); *)
    (* assume (not  (= (_ bv6 8) hdr.ipv6.nextHdr)); *)
    (* assert_ (= (_ bv1 1) hdr.ipv6.isValid); *)
    (* assume (= (_ bv17 8) hdr.ipv6.nextHdr); *)
    (* hdr.udp.isValid:=(_ bv1 1); *)
    (* parse_result:=(_ bv1 1); *)
    (* assume (= parse_result (_ bv1 1)); *)
    (* assert_ (= (_ bv1 1) hdr.ethernet.isValid); *)
    assume (eq_ (var @@ Var.make "_symb$ethertype_match$match_0" 16) (var hdr.ethernet.etherType));
    (* assume (= _symb$ethertype_match$action (_ bv1 3)); *)
    (* meta.ing_metadata.packet_type:=(_ bv3 4); *)
    (* assume (= (_ bv1 3) _symb$ethertype_match$action); *)
    (* assert_ (= (_ bv1 1) hdr.ipv4.isValid); *)
    (* assume (= _symb$ipv4_match$match_0 hdr.ipv4.dstAddr); *)
    (* assume (= _symb$ipv4_match$action (_ bv0 1)); *)
    (* meta.ing_metadata.egress_port:=_symb$ipv4_match$0$egress_port; *)
    (* assume (not  (= (_ bv1 1) hdr.tcp.isValid)); *)
    (* assume (= (_ bv1 1) hdr.udp.isValid); *)
    (* assert_ (= (_ bv1 1) hdr.udp.isValid); *)
    (* assume (= _symb$udp_check$match_0 hdr.udp.dstPort); *)
    (* assume (bvuge _symb$udp_check$action (_ bv1 1)); *)
    (* assume (= _symb$set_egress$match_0 meta.ing_metadata.drop); *)
    (* assume (= _symb$set_egress$action (_ bv0 1)); *)
    (* standard_metadata.egress_spec:=meta.ing_metadata.egress_port; *)
    (* assume (= standard_metadata.egress_spec (_ bv511 9)) *)
  ]
  |> simplify_path
  |> Alcotest.(check Equivalences.gcl)
    "programs are equivalent"
    @@ sequence [
      assume (eq_ (bvi 33024 16) (var hdr.ethernet.etherType));
      assume (eq_ (var @@ Var.make "_symb$ethertype_match$match_0" 16) (bvi 33024 16));
    ]

let test_annotations () =
  HoareNet.check_annotations multiproto
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer () =
  HoareNet.infer ~qe:`Enum multiproto None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is not true"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc multiproto None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is not true"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "07-Multiprotocol path simplification" `Quick funky_path;
  Alcotest.test_case "07-Multiprotocol annotations" `Quick test_annotations;
  Alcotest.test_case "07-Multiprotocol infer enum" `Slow test_infer;
  Alcotest.test_case "07-Multiprotocol infer conc" `Quick test_concolic;
]
