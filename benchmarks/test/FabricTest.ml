open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type lookup_metadata_t = {
    is_ipv4 : Var.t;
    ipv4_src : Var.t;
    ipv4_dst : Var.t;
    ip_proto : Var.t;
    l4_sport : Var.t;
    l4_dport : Var.t;
    icmp_type : Var.t;
    icmp_code : Var.t;
    vlan_valid : Var.t;
}

let lkp :  lookup_metadata_t = 
  let m = access "fabric_metadata.lkp" in
  {
    is_ipv4 = m "is_ipv4" 1;
    ipv4_src = m "ipv4_src" 32;
    ipv4_dst = m "ipv4_dst" 32;
    ip_proto = m "ip_proto" 8;
    l4_sport = m "l4_sport" 16;
    l4_dport = m "l4_dport" 16;
    icmp_type = m "icmp_type" 8;
    icmp_code = m "icmp_code" 8;
    vlan_valid = m "vlan_valid" 1;
  }

type fabric_metadata_t ={
  lkp : lookup_metadata_t;
  ip_eth_type : Var.t;
  vlan_id : Var.t; 
  vlan_pri : Var.t;
  vlan_cfi : Var.t;
  mpls_label : Var.t;
  mpls_ttl : Var.t;
  skip_forwarding : Var.t;
  skip_next : Var.t;
  fwd_type : Var.t;
  next_id : Var.t;
  is_multicast : Var.t;
  is_controller_packet_out : Var.t;
  ip_proto : Var.t;
  l4_sport : Var.t;
  l4_dport : Var.t;
  ipv4_src_addr : Var.t;
  ipv4_dst_addr : Var.t;
  slice_id : Var.t;
  packet_color : Var.t;
  tc : Var.t;
  dscp : Var.t;
  port_type : Var.t;
}

let fabric_metadata : fabric_metadata_t =
  let f = access "fabric_metadata" in
  {
    lkp;
    ip_eth_type = f "ip_eth_type" 16;
    vlan_id = f "vlan_id" 12;
    vlan_pri = f "vlan_pri" 3;
    vlan_cfi= f "vlan_cfi" 1;
    mpls_label = f "mpls_label" 20;
    mpls_ttl = f "mpls_ttl" 8;
    skip_forwarding = f "skip_forwarding" 1;
    skip_next = f "skip_next" 1;
    fwd_type = f "fwd_type" 3;
    next_id = f "next_id" 32;
    is_multicast =f "is_multicast" 1;
    is_controller_packet_out = f "is_controller_packet_out" 1;
    ip_proto = f "ip_proto" 8;
    l4_sport = f "l4_sport" 16;
    l4_dport = f "l4_dport" 16;
    ipv4_src_addr = f "ipv4_src_addr" 32;
    ipv4_dst_addr = f "ipv4_dst_addr" 32;
    slice_id = f "slice_id" 4;
    packet_color = f "packet_color" 2;
    tc = f "tc" 2;
    dscp = f "dscp" 6;
    port_type = f "port_type" 2;
  }

type gtpu_t =  {
  isValid : Var.t;
  version : Var.t;
  pt : Var.t;
  spare : Var.t;
  ex_flag : Var.t;
  seq_flag : Var.t;
  npdu_flag : Var.t;
  msgtype : Var.t;
  msglen : Var.t;
  teid : Var.t;
}

let gtpu : gtpu_t = 
  let f = access "hdr.gtpu" in
  {
    isValid = f "isValid" 1;
    version = f "version" 3;
    pt = f "pt" 1;
    spare = f "spare" 1;
    ex_flag = f "ex_flag" 1;
    seq_flag = f "seq_flag" 1;
    npdu_flag = f "npdu_flag" (1);
    msgtype = f "msgtype" 8; 
    msglen = f "msglen" 16;
    teid = f "teid" 32;
  }

type gtpu_options_t = {
  isValid : Var.t;
  seq_num : Var.t;
  n_pdu_num : Var.t;
  next_ext : Var.t;
}

let gtpu_options : gtpu_options_t =
  let f = access "hdr.gtpu_options" in
  {
    isValid = f "isValid" 1;
    seq_num = f "seq_num" 16;
    n_pdu_num = f "n_pdu_num" 8;
    next_ext = f "next_ext" 8;
  }

type gtpu_ext_psc_t = {
  isValid : Var.t;
  len : Var.t;
  type_ : Var.t;
  spare0 : Var.t;
  ppp : Var.t;
  rqi : Var.t;
  qfi : Var.t;
  next_ext : Var.t;
}

let gtpu_ext_psc : gtpu_ext_psc_t = 
  let f = access "hdr.gtpu_ext_psc" in
  {
    isValid = f "isValid" 1;
    len = f "len" 8;
    type_ = f "type" 4;
    spare0 = f "spare0" 4;
    ppp = f "ppp" 1;
    rqi = f "rqi" 1;
    qfi = f "qfi" 6;
    next_ext = f "next_ext" 8;
  }

type eth_type_t = {
  isValid  : Var.t;
  value : Var.t;
}

let eth_type : eth_type_t = 
  let f = access "hdr.eth_type" in
  {
    isValid = f "isValid" 1;
    value = f "value" 16;
  }

type packet_out_header_t = {
  isValid : Var.t;
  egress_port : Var.t;
  do_forwarding : Var.t;
  _pad : Var.t;
}

let packet_out : packet_out_header_t =
  let f = access "hdr.packet_out" in
  {
    isValid = f "isValid" 1;
    egress_port = f "egress_port" 9;
    do_forwarding = f "do_forwarding" 1; 
    _pad = f "_pad" 6;
  }

type packet_in_header_t = {
  isValid : Var.t;
  ingress_port : Var.t;
  _pad : Var.t;
}

let packet_in : packet_in_header_t =
  let f = access "hdr.packet_in" in
  {
    isValid = f "isValid" 1;
    ingress_port = f "ingress_port" 9;
    _pad = f "_pad" 6;
  }

type vlan_tag_t = {
  isValid : Var.t;
  eth_type : Var.t;
  pri : Var.t;
  cfi : Var.t;
  vlan_id : Var.t;
}

let vlan_tag : vlan_tag_t = 
  let f = access "hdr.vlan_tag" in
  {
    isValid = f "isValid" 1;
    eth_type = f "eth_type" 16;
    pri = f "pri" 3;
    cfi = f "cfi" 1;
    vlan_id = f "vlan_id" 12
  }

let inner_vlan_tag : vlan_tag_t = 
  let f = access "hdr.inner_vlan_tag" in
  {
    isValid = f "isValid" 1;
    eth_type = f "eth_type" 16;
    pri = f "pri" 3;
    cfi = f "cfi" 1;
    vlan_id = f "vlan_id" 12
  }

let inner_ipv4 : ipv4_t =
  let f = access "hdr.inner_ipv4" in
  {
    isValid = f "isValid" 1;
    version = f "version" 4;
    protocol = f "protocol" 8;
    ttl = f "ttl" 8;
    dstAddr = f "dstAddr" 32;
    srcAddr = f "srcAddr" 32;
    totalLen = f "totalLen" 16;
    ihl = f "ihl" 4;
    dscp = f "dscp" 6;
  }

let inner_tcp =
  let f = access "hdr.inner_tcp" in
  {
    isValid = f "isValid" 1;
    dstPort = f "dstPort" 16;
    srcPort = f "srcPort" 16
  } 
  
let inner_udp : udp_t =
  let f = access "hdr.inner_udp" in
  {
    isValid = f "isValid" 1;
    dstPort = f "dstPort" 16;
    checksum = f "checksum" 16;
    length = f "length" 16;
    srcPort = f "srcPort" 16
  }

let inner_icmp : icmp_t = 
  let f = access "hdr.inner_icmp" in
  {
    isValid = f "isValid" 1;
    type_ = f "type" 8;
    checksum = f "checksum" 16;
  }



type hdr_t = {
  ethernet : ethernet_t;
  vlan_tag : vlan_tag_t;
  inner_vlan_tag : vlan_tag_t;
  eth_type : eth_type_t;
  mpls : mpls_t;
  gtpu : gtpu_t;
  gtpu_options : gtpu_options_t;
  gtpu_ext_psc : gtpu_ext_psc_t;
  inner_ipv4 : ipv4_t;
  inner_tcp : tcp_t;
  inner_udp : udp_t;
  inner_icmp : icmp_t;
  ipv4 : ipv4_t;
  udp : udp_t;
  tcp : tcp_t;
  icmp : icmp_t;
  packet_out : packet_out_header_t;
  packet_in : packet_in_header_t;
}

let hdr : hdr_t = {
  ethernet;
  vlan_tag;
  inner_vlan_tag;
  eth_type;
  mpls;
  gtpu;
  gtpu_options;
  gtpu_ext_psc;
  inner_ipv4;
  inner_tcp;
  inner_udp;
  inner_icmp;
  ipv4;
  tcp;
  udp;
  icmp;
  packet_out;
  packet_in
}
let fabric_parser =
  let open HoareNet in
  let open Expr in
  let look_eth = Var.make "look_eth" 16 in
  let look_mpls = Var.make "look_mpls" 4 in
  let last_ipv4_dscp = Var.make "last_ipv4_dscp" 6 in
  let parse_tcp = sequence [
    assign hdr.tcp.isValid btrue;
    assign fabric_metadata.l4_sport @@ var hdr.tcp.srcPort;
    assign fabric_metadata.l4_dport @@ var hdr.tcp.dstPort;
    transition_accept    
  ] in
  let parse_inner_tcp = sequence [
    assign hdr.inner_tcp.isValid btrue;
    transition_accept    
  ] in
  let parse_inner_udp = sequence [
    assign hdr.inner_udp.isValid btrue;
    transition_accept    
  ] in
  let parse_inner_icmp = sequence [
    assign hdr.inner_icmp.isValid btrue;
    transition_accept    
  ] in
  let parse_inner_ipv4 = sequence [
    assign hdr.inner_ipv4.isValid btrue;
    assign last_ipv4_dscp @@ var hdr.inner_ipv4.dscp;
    select (var hdr.inner_ipv4.protocol) [
      bvi 6 8, parse_inner_tcp;
      bvi 17 8, parse_inner_udp;
      bvi 1 8, parse_inner_icmp;
    ] transition_accept
  ] in
  let gtpu_ext_len = Var.make "gtpu_ext_len" 8 in
  let parse_gtpu_ext_psc = sequence [
    assign hdr.gtpu_ext_psc.isValid btrue;
    assign hdr.gtpu_ext_psc.len @@ var gtpu_ext_len;
    select (var hdr.gtpu_ext_psc.next_ext) [
      bvi 0 8, parse_inner_ipv4;
    ] transition_accept
  ] in
  let parse_gtpu_options = sequence [
    assign hdr.gtpu_options.isValid btrue;
    select (bconcat (var hdr.gtpu_options.next_ext) (var gtpu_ext_len)) [
      bconcat (bvi 133 8) (bvi 1 8), parse_gtpu_ext_psc
    ] transition_accept
  ] in
  let gtpu_version = Var.make "gtpu_version" 3 in
  let gtpu_msgtype = Var.make "gtpu_msgtype" 8 in
  let parse_gtpu = sequence [
    assign hdr.gtpu.isValid btrue;
    assign hdr.gtpu.version @@ var gtpu_version;
    assign hdr.gtpu.msgtype @@ var gtpu_msgtype;
    select (bconcat (var hdr.gtpu.ex_flag) @@ bconcat (var hdr.gtpu.seq_flag) (var hdr.gtpu.npdu_flag)) [
      bconcat bfalse @@ bconcat bfalse bfalse, parse_inner_ipv4
    ] parse_gtpu_options
  ] in
  let parse_udp = sequence[
    assign hdr.udp.isValid btrue;
    assign fabric_metadata.l4_sport @@ var hdr.udp.srcPort;
    assign fabric_metadata.l4_dport @@ var hdr.udp.dstPort;
    select (bconcat (var hdr.udp.dstPort) @@ bconcat (var gtpu_version) (var gtpu_msgtype)) [
      bconcat (bvi 2152 16) @@ bconcat (bvi 1 3) (bvi 255 8), parse_gtpu;
    ] parse_gtpu
  ] in
  let parse_icmp = sequence [
    assign hdr.icmp.isValid btrue;
    transition_accept
  ] in
  let parse_ipv4 = sequence [
    assign hdr.ipv4.isValid btrue;
    assign hdr.ipv4.version @@ var look_mpls;
    assign fabric_metadata.ip_proto @@ var hdr.ipv4.protocol;
    assign fabric_metadata.ip_eth_type @@ bvi 2048 16;
    assign fabric_metadata.ipv4_src_addr @@ var hdr.ipv4.srcAddr;
    assign fabric_metadata.ipv4_dst_addr @@ var hdr.ipv4.dstAddr;
    assign last_ipv4_dscp @@ var hdr.ipv4.dscp;
    select (var hdr.ipv4.protocol) [
      bvi 6 8, parse_tcp;
      bvi 17 8, parse_udp;
      bvi 1 8, parse_icmp;
    ] transition_accept
  ] in
  let parse_mpls = sequence [
    assign hdr.mpls.isValid btrue;
    assign fabric_metadata.mpls_label @@ var hdr.mpls.label;
    assign fabric_metadata.mpls_ttl @@ var hdr.mpls.ttl;
    select (var look_mpls) [
      bvi 4 4, parse_ipv4;
    ] transition_accept (*parse_ethernet*)
  ] in
  let parse_eth_type = sequence [
    assign hdr.eth_type.isValid btrue;
    assign hdr.eth_type.value @@ var look_eth;
    select (var hdr.eth_type.value) [
      bvi 34887 16, parse_mpls;
      bvi 2048 16, parse_ipv4;
    ] transition_accept
  ] 
  in
  let look_vlan = Var.make "look_vlan" 16 in
  let parse_inner_vlan_tag = sequence [
    assign hdr.inner_vlan_tag.isValid btrue;
    assign hdr.inner_vlan_tag.eth_type @@ var look_vlan;
    parse_eth_type
  ] in
  let parse_vlan_tag = sequence [
    assign hdr.vlan_tag.isValid btrue;
    select (var look_vlan)  [
      bvi 33024 16, parse_inner_vlan_tag;
    ] parse_eth_type 
  ] in
  let parse_ethernet = sequence [
    assign hdr.ethernet.isValid btrue;
    assign fabric_metadata.vlan_id @@ bvi 4094 12;
    select (var look_eth) [
      bvi 34984 16, parse_vlan_tag;
      bvi 37120 16, parse_vlan_tag;
      bvi 33024 16, parse_vlan_tag;
    ] parse_eth_type
  ] in
  let look_packet_out = Var.make "look_packet_out" 1 in
  let parse_packet_out_and_accept = sequence [
    assign hdr.packet_out.isValid bfalse;
    assign hdr.packet_out.do_forwarding @@ var look_packet_out; 
    transition_accept
  ] in
  let strip_packet_out = parse_ethernet in  
  let check_packet_out = sequence [
    select (var look_packet_out) [
      bfalse, parse_packet_out_and_accept;
    ] strip_packet_out
  ] in
  let start = sequence [
    assign last_ipv4_dscp @@ bvi 0 6;   
    select (var standard_metadata.ingress_port) [
      bvi 510 9, check_packet_out;
    ] parse_ethernet
  ] in
  start

let fabric_ingress _ =
  let open HoareNet in
  let open Expr in
  sequence [
    lkp_md_init;
    slice_tc_classifier;
    ifte_seq (eq_ bfalse (var fabric_metadata.is_controller_packet_out)) [
      filtering;
      ifte (eq_ bfalse (var fabric_metadata.skip_forwarding))
        forwarding skip;
      ifte (eq_ bfalse (var fabric_metadata.skip_next))
        prev_next skip;
      acl;
      ifte (eq_ bfalse (var fabric_metadata.skip_next))
        next skip;
      qos;
    ] []
  ]

let fabric_egress =
  let open HoareNet in
  let open Expr in
  sequence [
    pkt_io_egress;
    ifte_seq (eq_ bfalse (fabric_metadata.is_controller_packet_out)) [
      egress_next;
      dscp_rewriter;{}
    ] [
  ]

let fabric fixed =
  pipeline fabric_parser (fabric_ingress fixed) fabric_egress
  (* pipeline HoareNet.skip (netschain_ingress fixed) HoareNet.skip *)
  |> HoareNet.assert_valids

let test_infer_timeout () =
  HoareNet.infer ~qe:`Enum (fabric true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc (fabric true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is not trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "Fabric infer enum unannotated" `Slow test_infer_timeout;
  Alcotest.test_case "Fabric infer concolic with annotation" `Quick test_concolic;
]
