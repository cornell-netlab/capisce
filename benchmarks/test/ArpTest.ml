open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type my_metadata_t = {
    dst_ipv4 : Var.t;
    mac_da : Var.t;
    mac_sa : Var.t;
    egress_port : Var.t;
    my_mac : Var.t;
}

let meta : my_metadata_t = {
  dst_ipv4 = Var.make "meta.dst_ipv4" 32;
  mac_da = Var.make "meta.mac_da" 48;
  mac_sa = Var.make "meta.mac_sa" 48;
  egress_port = Var.make "meta.egress_port" 9;
  my_mac = Var.make "meta.my_mac" 48;
}

let arp_parser =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  (* start *)
  sequence [
    assign hdr.ethernet.isValid bfalse;
    assign hdr.ipv4.isValid bfalse;
    assign hdr.tcp.isValid bfalse;
    (*parse ethenet*)
    assign hdr.ethernet.isValid btrue;
    (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
    ifte_seq (eq_ (var hdr.ethernet.etherType) (bvi 2048 16))
      [ (* parse ipv4 *)
        assign hdr.ipv4.isValid btrue;
        (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
        assign meta.dst_ipv4 @@ var hdr.ipv4.dstAddr;
        (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
        ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 1 8))
          [ (* parse icmp *)
            assign hdr.icmp.isValid btrue;
            transition_accept ]
          [ transition_accept ]
      ]
      [ (* parse_arp *)
        ifte_seq (eq_ (var hdr.ethernet.etherType) (bvi 2054 16))
        [ (*parse_arp*)
          assign hdr.arp.isValid btrue;
          (* assert_ @@ eq_ btrue @@ var hdr.arp.isValid; *)
          ifte_seq (ands_ [
              eq_ (bvi 1    16) (var hdr.arp.htype);
              eq_ (bvi 2048 16) (var hdr.arp.ptype);
              eq_ (bvi 6     8) (var hdr.arp.hlen);
              eq_ (bvi 4     8) (var hdr.arp.plen);
            ]) [
            (* parse_arp_ipv4 *)
            assign hdr.arp_ipv4.isValid btrue;
            (* assert_ @@ eq_ btrue @@ var hdr.arp_ipv4.isValid; *)
            assign meta.dst_ipv4 @@ var hdr.arp_ipv4.tpa;
          ] [transition_accept]
        ]
        [transition_accept]
      ]
  ]

let arp_ingress =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let open Primitives in
  let set_dst_info =
    let mac_da = Var.make "mac_da" 48 in
    let mac_sa = Var.make "mac_sa" 48 in
    let egress_port = Var.make "egress_port" 9 in
    [mac_da; mac_sa; egress_port],
    Action.[
      assign meta.mac_da @@ var mac_da;
      assign meta.mac_sa @@ var mac_sa;
      assign meta.egress_port @@ var egress_port
    ]
  in
  let drop =
    [],
    Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9;
      assign zombie.exited btrue;
    ]
  in
  let ipv4_lpm =
    instr_table ("ipv4_lpm", [`MaskableDegen meta.dst_ipv4], [set_dst_info; drop])
  in
  let forward_ipv4 = [], Action.[
      (* assert_ (eq_ btrue (var hdr.ethernet.isValid)); *)
      assign hdr.ethernet.dstAddr @@ var meta.mac_da;
      (* assert_ (eq_ btrue (var hdr.ethernet.isValid)); *)
      assign hdr.ethernet.srcAddr @@ var meta.mac_sa;
      (* assert_ (eq_ btrue (var hdr.ipv4.isValid)); *)
      assign hdr.ipv4.ttl @@ bsub (var hdr.ipv4.ttl) (bvi 1 8);
      assign standard_metadata.egress_spec @@ var meta.egress_port;
    ] in
  let send_arp_reply = [], Action.[
      assign hdr.ethernet.dstAddr @@ var hdr.arp_ipv4.sha;
      assign hdr.ethernet.srcAddr @@ var meta.mac_da;

      assign hdr.arp.oper         @@ bvi 2 16;

      assign hdr.arp_ipv4.tha     @@ var hdr.arp_ipv4.sha;
      assign hdr.arp_ipv4.tpa     @@ var hdr.arp_ipv4.spa;
      assign hdr.arp_ipv4.sha     @@ var meta.mac_da;
      assign hdr.arp_ipv4.spa     @@ var meta.dst_ipv4;

      assign standard_metadata.egress_spec @@ var standard_metadata.ingress_port
    ] in
  let send_icmp_reply =
    let tmp_mac = Var.make "tmp_mac" 48 in
    let tmp_ip = Var.make "tmp_ip" 32  in
    [], Action.[
        assign tmp_mac              @@ var hdr.ethernet.dstAddr;
        assign hdr.ethernet.dstAddr @@ var hdr.ethernet.srcAddr;
        assign hdr.ethernet.srcAddr @@ var tmp_mac;

        assign tmp_ip               @@ var hdr.ipv4.dstAddr;
        assign hdr.ipv4.dstAddr     @@ var hdr.ipv4.srcAddr;
        assign hdr.ipv4.srcAddr     @@ var tmp_ip;

        assign hdr.icmp.type_       @@ bvi 0 8;
        assign hdr.icmp.checksum    @@ bvi 0 16;

        assign standard_metadata.egress_spec @@ var standard_metadata.ingress_port;
    ]
  in
  let forward =
    instr_table ("forward",
                 [`Exact hdr.arp.isValid;
                  `MaskableDegen hdr.arp.oper;
                  `Exact hdr.arp_ipv4.isValid;
                  `Exact hdr.ipv4.isValid;
                  `Exact hdr.icmp.isValid;
                  `Maskable hdr.icmp.type_],
                 [forward_ipv4; send_arp_reply; send_icmp_reply; drop])
  in
  sequence [
    assign meta.my_mac @@ bvi 000102030405 48;
    ifte_seq (eq_ btrue @@ var zombie.exited) [] [
      ipv4_lpm;
      forward
    ]
  ]

let arp_egress =
  let open HoareNet in
  (* let open BExpr in *)
  (* let open Expr in *)
  skip


let arp =
  pipeline arp_parser arp_ingress arp_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations arp
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer () =
  HoareNet.infer ~qe:`Enum arp None None
  |> Alcotest.(check (neg Equivalences.smt_equiv))
    "CPI is sat"
    BExpr.false_

let test_concolic () =
  HoareNet.infer ~qe:`Conc arp None None
  |> Alcotest.(check (neg Equivalences.smt_equiv))
    "CPI is sat"
    BExpr.false_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "arp annotations" `Quick test_annotations;
  Alcotest.test_case "arp infer enum" `Slow test_infer;
  Alcotest.test_case "arp infer conc" `Quick test_concolic;
]
