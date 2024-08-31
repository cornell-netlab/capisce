open Core
open Capisce
open ASTs.GPL
open V1ModelUtils

(* type my_metadata_t = {
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
} *)

let psm =
  let open EmitP4.Parser in 
  let open Expr in 
  of_state_list [
    state "start" hdr.ethernet.isValid @@
    select hdr.ethernet.etherType [
      bvi 2048 16, "parse_ipv4";
    ] "accept"
    ;
    state "parse_ipv4" hdr.ipv4.isValid @@
    direct "accept"
    ;
  ]

let ingress =
  let open Expr in
  let open Primitives in
  let set = 
    let s = Var.make "s" 48 in 
    [s], Action.[
      assign hdr.ethernet.srcAddr @@ var s
    ]
  in 
  let nop = [], [] in 
  let t1 = table "t1" 
    [
      hdr.ethernet.etherType, Exact;      
    ] [
      set; nop
    ]
  in
  let mayfail = [], Action.[
    assign hdr.ipv4.ttl @@ bsub (var hdr.ipv4.ttl) (bvi 1 8);
  ] in 
  let t2 = table "t2"
    [
      hdr.ethernet.srcAddr, Exact; 
    ] [
      mayfail; nop
    ]
  in
  sequence [
    t1;
    t2;
    assign standard_metadata.egress_spec @@ bvi 511 9
  ]

let egress = skip


let example =
  psm, ingress, egress
