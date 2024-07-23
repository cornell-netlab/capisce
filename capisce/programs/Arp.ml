open Core
open Capisce
open ASTs.GPL
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

let arp_psm =
  let open EmitP4 in 
  let open Parser in 
  let open ASTs.GCL in
  let open Expr in 
  of_state_list
  [ {name = "start";
     body = assign hdr.ethernet.isValid btrue;
     transition = 
      select (hdr.ethernet.etherType) [
        bvi 2048 16, "parse_ipv4";
        bvi 2054 16, "parse_arp";
      ] "accept";
    };
    { name = "parse_arp";
      body = assign hdr.arp.isValid btrue;
      transition = {
        discriminee = 
          List.map ~f:Expr.var
          [hdr.arp.htype; hdr.arp.ptype; hdr.arp.hlen; hdr.arp.plen];
        cases = [
          [bvi 1 16; bvi 2048 16; bvi 6 16; bvi 4 16], "parse_arp_ipv4"
        ];
        default = "accept"

      }
    };
    { name = "parse_arp_ipv4";
      body = sequence [
        assign hdr.arp_ipv4.isValid btrue;
        assign meta.dst_ipv4 @@ var hdr.arp_ipv4.tpa;
      ];
      transition = default "accept"
    };
    { name = "parse_ipv4" ;
      body = sequence [
        assign hdr.ethernet.isValid btrue;
        assign meta.dst_ipv4 @@ var hdr.ipv4.dstAddr
      ];
      transition = 
        select (hdr.ipv4.protocol) [
          bvi 1 8, "parse_icmp"
        ] "accept"; 
    };
    { name = "parse_icmp";
      body = assign hdr.icmp.isValid btrue;
      transition = default "accept"
    }
  ]

let arp_ingress =
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
    table "ipv4_lpm" [
      meta.dst_ipv4, MaskableDegen
    ] [
      set_dst_info; drop (*default*)
    ]
  in
  let forward_ipv4 = [], Action.[
      assign hdr.ethernet.dstAddr @@ var meta.mac_da;
      assign hdr.ethernet.srcAddr @@ var meta.mac_sa;
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
    table "forward"
      [hdr.arp.isValid, Exact;
      hdr.arp.oper, MaskableDegen;
      hdr.arp_ipv4.isValid, Exact;
      hdr.ipv4.isValid, Exact;
      hdr.icmp.isValid, Exact;
      hdr.icmp.type_, Maskable
      ]
      [ forward_ipv4; send_arp_reply; send_icmp_reply;
        drop (* default *)
      ]
  in
  sequence [
    assign meta.my_mac @@ bvi 000102030405 48;
    ifte_seq (eq_ btrue @@ var zombie.exited) [
    ] [
      ipv4_lpm;
      forward
    ]
  ]

let arp_egress =
  sequence [
    assign hdr.ethernet.isValid bfalse;
  ]


let arp =
  pipeline_psm arp_psm arp_ingress arp_egress
