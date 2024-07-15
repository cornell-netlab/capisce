open Core
open Capisce
open DependentTypeChecker
open V1ModelUtils
open Primitives

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
    code = f "code" 8;
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
  let parse_eth_type_1 = sequence [
    assign hdr.eth_type.isValid btrue;
    assign hdr.eth_type.value @@ var look_eth;
    select (var hdr.eth_type.value) [
      bvi 34887 16, assume BExpr.false_;
      bvi 2048 16, parse_ipv4;
    ] transition_accept
  ] 
  in
  let look_vlan = Var.make "look_vlan" 16 in
  let parse_inner_vlan_tag_1 = sequence [
    assign hdr.inner_vlan_tag.isValid btrue;
    assign hdr.inner_vlan_tag.eth_type @@ var look_vlan;
    parse_eth_type_1
  ] in
  let parse_vlan_tag_1 = sequence [
    assign hdr.vlan_tag.isValid btrue;
    select (var look_vlan)  [
      bvi 33024 16, parse_inner_vlan_tag_1;
    ] parse_eth_type_1 
  ] in
  let parse_ethernet_1 = sequence [
    assign hdr.ethernet.isValid btrue;
    assign fabric_metadata.vlan_id @@ bvi 4094 12;
    select (var look_eth) [
      bvi 34984 16, parse_vlan_tag_1;
      bvi 37120 16, parse_vlan_tag_1;
      bvi 33024 16, parse_vlan_tag_1;
    ] parse_eth_type_1
  ] in
  let parse_mpls = sequence [
    assign hdr.mpls.isValid btrue;
    assign fabric_metadata.mpls_label @@ var hdr.mpls.label;
    assign fabric_metadata.mpls_ttl @@ var hdr.mpls.ttl;
    select (var look_mpls) [
      bvi 4 4, parse_ipv4;
    ] parse_ethernet_1
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
    assign hdr.packet_out.isValid btrue;
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

let lkp_md_init =  
  let open HoareNet in
  let open Expr in
  let open BExpr in
  sequence [
    assign fabric_metadata.lkp.is_ipv4 @@ bfalse;
    assign fabric_metadata.lkp.ipv4_src @@ bvi 0 32;
    assign fabric_metadata.lkp.ipv4_dst @@ bvi 0 32;
    assign fabric_metadata.lkp.ip_proto @@ bvi 0 8;
    assign fabric_metadata.lkp.l4_sport @@ bvi 0 16;
    assign fabric_metadata.lkp.l4_dport @@ bvi 0 16;
    assign fabric_metadata.lkp.icmp_type @@ bvi 0 8;
    assign fabric_metadata.lkp.icmp_code @@ bvi 0 8;
    ifte_seq (eq_ btrue @@ var hdr.inner_ipv4.isValid) [
      assign fabric_metadata.lkp.is_ipv4 btrue;
      assign fabric_metadata.lkp.ipv4_src @@ var hdr.inner_ipv4.srcAddr;
      assign fabric_metadata.lkp.ipv4_dst @@ var hdr.inner_ipv4.dstAddr;
      assign fabric_metadata.lkp.ip_proto @@ var hdr.inner_ipv4.protocol;
      ifte_seq (eq_ btrue @@ var hdr.inner_tcp.isValid)[
        assign fabric_metadata.lkp.l4_sport @@ var hdr.inner_tcp.srcPort;
        assign fabric_metadata.lkp.l4_dport @@ var hdr.inner_tcp.dstPort;
      ] [
        ifte_seq (eq_ btrue @@ var hdr.inner_udp.isValid)[
          assign fabric_metadata.lkp.l4_sport @@ var hdr.inner_udp.srcPort;
         assign fabric_metadata.lkp.l4_dport @@ var hdr.inner_udp.dstPort;
        ] [
          ifte_seq (eq_ btrue @@ var hdr.inner_icmp.isValid)[
            assign fabric_metadata.lkp.icmp_type @@ var hdr.inner_icmp.type_;
           assign fabric_metadata.lkp.icmp_code @@ var hdr.inner_icmp.code;
          ] []
        ]
      ]  
    ] [ 
      ifte_seq (eq_ btrue @@ var hdr.ipv4.isValid) [
        assign fabric_metadata.lkp.is_ipv4 btrue;
        assign fabric_metadata.lkp.ipv4_src @@ var hdr.ipv4.srcAddr;
        assign fabric_metadata.lkp.ipv4_dst @@ var hdr.ipv4.dstAddr;
        assign fabric_metadata.lkp.ip_proto @@ var hdr.ipv4.protocol;
        ifte_seq (eq_ btrue @@ var hdr.tcp.isValid)[
          assign fabric_metadata.lkp.l4_sport @@ var hdr.tcp.srcPort;
          assign fabric_metadata.lkp.l4_dport @@ var hdr.tcp.dstPort;
         ] [
          ifte_seq (eq_ btrue @@ var hdr.udp.isValid)[
            assign fabric_metadata.lkp.l4_sport @@ var hdr.udp.srcPort;
            assign fabric_metadata.lkp.l4_dport @@ var hdr.udp.dstPort;
          ] [
            ifte_seq (eq_ btrue @@ var hdr.icmp.isValid)[
              assign fabric_metadata.lkp.icmp_type @@ var hdr.icmp.type_;
              assign fabric_metadata.lkp.icmp_code @@ var hdr.icmp.code;
          ] []
        ]
      ]
      ] [ ]
    ]
  ]

let slice_tc_classifier =
  let open HoareNet in
  let open Expr in
  let open Primitives in  
  let set_slice_id_tc =
    let slice_id = Var.make "slice_id" 4 in
    let tc = Var.make "tc" 2 in
    [slice_id; tc], Action.[
      assign fabric_metadata.slice_id @@ var slice_id;
      assign fabric_metadata.tc @@ var tc;
      (* classifier_stats.count() *)
    ] 
  in
  let trust_dscp = [], Action.[
    assign fabric_metadata.slice_id @@ bslice 2 5 @@ var hdr.ipv4.dscp;
    assign fabric_metadata.tc @@ bslice 0 1 @@ var hdr.ipv4.dscp;
  (* classifier_stats.count() *)
  ] in
  let set_slice_id_tc_default =

    [], Action.[
      assign fabric_metadata.slice_id @@ bvi 0 4;
      assign fabric_metadata.tc @@ bvi 0 2;
      (* classifier_stats.count() *)
    ] 
  in
  let classifier =
    instr_table ("classifier",  
      [ 
        `Exact standard_metadata.ingress_port
      ; `Exact fabric_metadata.lkp.ipv4_src
      ; `Exact fabric_metadata.lkp.ipv4_dst
      ; `Exact fabric_metadata.lkp.ip_proto
      ; `Exact fabric_metadata.lkp.l4_sport
      ; `Exact fabric_metadata.lkp.l4_dport
      ],
      [set_slice_id_tc; trust_dscp;
      (* default *)
      set_slice_id_tc_default
      ]
     )
  in
  classifier

let filtering = 
  let open HoareNet in
  let open Expr in
  let open BExpr in
  let deny = [], Action.[
    assign fabric_metadata.skip_forwarding @@ btrue;
    assign fabric_metadata.skip_next @@ btrue;
    assign fabric_metadata.port_type @@ bvi 0 2;
    (* ingress_port_vlan_counter.count *)
  ] in
  let permit =
    let port_type = Var.make "port_type" 2 in
    [port_type], Action.[
      assign fabric_metadata.port_type @@ var port_type;
      (* ingress_port_vlan_counter.count *)
    ] in
  let permit_with_internal_vlan = 
    let vlan_id = Var.make "vlan_id" 12 in
    let port_type = Var.make "port_type" 2 in
    [vlan_id; port_type], Action.[
      assign fabric_metadata.vlan_id @@ var vlan_id;
      (* permit(port_type) *)
      assign fabric_metadata.port_type @@ var port_type;
    ] in
  let ingress_port_vlan = 
    instr_table ("ingress_port_vlan",
      [
        `Exact standard_metadata.ingress_port;
        `Exact hdr.vlan_tag.isValid ;
        `Maskable hdr.vlan_tag.vlan_id;
      ], [
        deny; (* default *)
        permit; permit_with_internal_vlan;
      ]
    )
  in
  let set_forwarding_type = 
    let fwd_type = Var.make "fwd_type" 3 in
    [fwd_type], Action.[
      assign fabric_metadata.fwd_type @@ var fwd_type;
      (* fwd_classifier_counter.count() *)
    ]
  in
  let set_forwarding_type_bridging = 
    [], Action.[
      assign fabric_metadata.fwd_type @@ bvi 0 3;
      (* fwd_classifier_counter.count() *)
    ]
  in
  let fwd_classifier = 
    instr_table ("fwd_classifier", [
      `Exact standard_metadata.ingress_port;
      `Exact hdr.ethernet.dstAddr;
      `Exact hdr.eth_type.value;
      `Exact fabric_metadata.ip_eth_type;  
      ],[
        set_forwarding_type; 
        set_forwarding_type_bridging (*default*)
      ]
    )
    in
  sequence [
    ifte_seq (eq_ btrue @@ var hdr.vlan_tag.isValid) [
      assign fabric_metadata.vlan_id @@ var hdr.vlan_tag.vlan_id;
      assign fabric_metadata.vlan_pri @@ var hdr.vlan_tag.pri;
      assign fabric_metadata.vlan_cfi @@ var hdr.vlan_tag.cfi;
    ] [];
    ifte_seq (eq_ btrue @@ var hdr.mpls.isValid) [
      assign fabric_metadata.mpls_ttl @@ badd (bvi 64 8) (bvi 1 8);
    ] [];
    ingress_port_vlan;
    fwd_classifier
  ]

let forwarding = 
  let open HoareNet in
  let open Expr in
  let open BExpr in
  let set_next_id_bridging = 
    let next_id = Var.make "next_id" 32 in
    [next_id], Action.[
      (* set_next_id(next_id) *)
      assign fabric_metadata.next_id @@ var next_id;
      (* bridging_counter.count() *)
    ] in
  let nop = [],[] in
  let bridging = 
    instr_table ("bridging",
      [
        `Exact fabric_metadata.vlan_id;
        `Exact hdr.ethernet.dstAddr;
      ] , [
        set_next_id_bridging; 
        nop (*defaultonly*)
      ]
    )
  in
  let pop_mpls_and_next =
    let next_id = Var.make "next_id" 32 in
    [next_id], Action.[
      assign fabric_metadata.mpls_label @@ bvi 0 20;
      (* set_next_id(next_id);       *)
      assign fabric_metadata.next_id @@ var next_id;
      (* mpls_counter.count() *)
    ] in
  let mpls = 
    instr_table ("mpls",
      [
        `Exact fabric_metadata.mpls_label; 
      ], [
        pop_mpls_and_next; 
        nop (* nop *)
      ]
    )
  in
  let set_next_id_routing_v4 = 
    let next_id = Var.make "next_id" 32 in
    [next_id], Action.[
      assign fabric_metadata.next_id @@ var next_id;
    ] in
  let nop_routing_v4 = [],[] in
  let routing_v4 = 
      instr_table ("routing_v4",
        [
          `Exact fabric_metadata.ipv4_dst_addr;
        ],[
          set_next_id_routing_v4; nop_routing_v4; 
          nop (*defaultonly*)
        ]
      )
  in
  ifte (eq_ (bvi 0 3) @@ var fabric_metadata.fwd_type) bridging @@
  ifte (eq_ (bvi 1 3) @@ var fabric_metadata.fwd_type) mpls @@
  ifte (eq_ (bvi 2 3) @@ var fabric_metadata.fwd_type) routing_v4 @@
  skip

let pre_next =
  let open HoareNet in
  let open Expr in
  let nop = [],[] in
  let set_mpls_label =
    let label = Var.make "label" 20 in
    [label], Action.[
      assign fabric_metadata.mpls_label @@ var label;
      (* next_mpls_counter.count() *)
    ]
  in
  let next_mpls = 
    instr_table ("next_mpls",
      [
        `Exact fabric_metadata.next_id; 
      ], [
        set_mpls_label; nop
      ]
    )
  in
  let set_vlan = 
    let vlan_id = Var.make "vlan_id" 12 in
    [vlan_id], Action.[
      assign fabric_metadata.vlan_id @@ var vlan_id;
      (* next_vlan_counter.count() *)
    ] in
  let next_vlan = 
    instr_table ( "next_vlan", 
      [
        `Exact fabric_metadata.next_id; 
      ], [
        set_vlan; 
        nop (* defaultonly *)
      ]
    ) in  
  sequence [
    next_mpls;
    next_vlan
  ]

let acl fixed = 
  let open HoareNet in
  let open Expr in
  let set_next_id_acl =
    let next_id = Var.make "next_id" 32 in
    [next_id], Action.[
      assign fabric_metadata.next_id @@ var next_id;
      (* acl_counter.count() *)
    ] in
  let punt_to_cpu =
    [], Action.[
      assign standard_metadata.egress_spec @@ bvi 510 9;  
      assign fabric_metadata.skip_next @@ btrue;
      (* acl_counter.count(); *)
    ]
  in
  let set_clone_session_id =
    let clone_id = Var.make "clone_id" 32 in
    [clone_id], [
      (* clone3(CloneType.I2E, clone_id, { standard_metadata.ingress_port }); *)
      (* acl_counter.count(); *)
    ]
  in
  let drop = [], Action.[
    mark_to_drop;
    assign fabric_metadata.skip_next btrue;
    (* acl_counter.count(); *)
  ] in
  let nop_acl = [], [ (* acl_counter.count(); *) ] in
  let acl =
    instr_table  ("acl",
      [ 
        `MaskableDegen standard_metadata.ingress_port;
        `MaskableDegen hdr.ethernet.dstAddr;     
        `MaskableDegen hdr.ethernet.srcAddr;         
        `Maskable      hdr.vlan_tag.vlan_id;          
        `MaskableDegen hdr.eth_type.value;            
        `MaskableDegen fabric_metadata.lkp.ipv4_src;        
        `MaskableDegen fabric_metadata.lkp.ipv4_dst;
        `MaskableDegen fabric_metadata.lkp.ip_proto;
        if fixed 
        then `MaskableDegen fabric_metadata.lkp.icmp_type
        else `Maskable      hdr.icmp.type_;
        if fixed
        then `MaskableDegen fabric_metadata.lkp.icmp_code
        else `Maskable      hdr.icmp.code;
        `MaskableDegen fabric_metadata.lkp.l4_sport;
        `MaskableDegen fabric_metadata.lkp.l4_dport;
        `MaskableDegen fabric_metadata.port_type;
      ], [
        set_next_id_acl;
        punt_to_cpu;
        set_clone_session_id;
        drop;
        nop_acl; (*default*)
      ]
    ) 
  in
  acl

let next =
  let open HoareNet in
  let open Expr in
  let output x = Action.(assign standard_metadata.egress_spec x) in
  let output_xconnect = 
    let port_num = Var.make "port_num" 9 in
    [port_num], [
      output @@ var port_num;
      (* xconnect_counter.count() *)
    ]
  in
  let set_next_id_xconnect =
    let next_id = Var.make "next_id" 32 in
    [next_id], Action.[
      assign fabric_metadata.next_id @@ var next_id;
      (* xconnect_counter.count() *)
    ] 
  in
  let nop = [],[] in
  let xconnect =
    instr_table ("xconnect",
      [
        `Exact standard_metadata.ingress_port;
        `Exact fabric_metadata.next_id;
      ], [
        output_xconnect; set_next_id_xconnect; 
        nop; (* default*)
      ]
    )
  in
  let output_hashed =
    let port_num = Var.make "port_num" 9 in
    [port_num], [
      output @@ var port_num;
      (* hashed_counter.count() *)
    ]
  in
  let routing_hashed =
    let port_num = Var.make "port_num" 9 in
    let smac = Var.make "smac" 48 in
    let dmac = Var.make "dmac" 48 in
    [port_num;smac;dmac], Action.[
      assign hdr.ethernet.srcAddr @@ var smac;
      assign hdr.ethernet.dstAddr @@ var dmac;
      output @@ var port_num;
      (* hashed_counter.count() *)
    ]
  in
  let hashed =
    instr_table ("hashed",
      [
        `Exact fabric_metadata.next_id;
        (* `Exact fabric_metadata.ipv4_src_addr; (* selector *)
        `Exact fabric_metadata.ipv4_dst_addr; (* selector *)
        `Exact fabric_metadata.ip_proto; (* selector *)
        `Exact fabric_metadata.l4_sport; (* selector *)
        `Exact fabric_metadata.l4_dport; selector *)
      ], [
        output_hashed; routing_hashed; 
        nop (*defaultonly*)
      ]
    )
  in
  let set_mcast_group_id =
    let group_id = Var.make "group_id" 32 in
    [group_id], Action.[
      assign standard_metadata.mcast_grp @@ var group_id;
      assign fabric_metadata.is_multicast @@ btrue;
      (* multicast_counter.count() *)
    ]
  in
  let multicast = 
    instr_table ("multicast",
    [
      `Exact fabric_metadata.next_id;
    ], [
      set_mcast_group_id; 
      nop (* multicast *)
    ])
  in
  sequence [
    xconnect;
    hashed;
    multicast;
  ]

let qos =  
  let open HoareNet in
  let open Expr in
  let slice_tc = Var.make "slice_tc" 6 in
  let meter_havoc = Var.make "meter_havoc" 2 in
  let set_queue = 
      let qid = Var.make "qid" 5 in
      [qid], [
        (* queues_stats.count() *)
      ]
  in
  let meter_drop = [], [
    mark_to_drop
    (* queues_stats.count() *)
  ] in
  let set_queue_default = 
      [], [
        (* queues_stats.count() *)
      ]
  in
  let queues =
    instr_table ("queues",
    [
      `Exact fabric_metadata.slice_id;
      `Exact fabric_metadata.tc;
      `Exact fabric_metadata.packet_color;
    ], [
      set_queue; meter_drop;
      set_queue_default
    ])
  in
  sequence [
    assign slice_tc @@ bconcat (var fabric_metadata.slice_id) (var fabric_metadata.tc);
    (* slice_tc_meter.execute_meter((bit<32>)slice_tc, fabric_metadata.packet_color); *)
    assign fabric_metadata.packet_color @@ var meter_havoc;
    assign fabric_metadata.dscp @@ var slice_tc;
    queues 
  ]

let pkt_io_ingress =
  let open HoareNet in
  let open Expr in
  let open BExpr in
  ifte_seq (eq_ btrue @@ var hdr.packet_out.isValid) [
    assign standard_metadata.egress_spec @@ var hdr.packet_out.egress_port;
    assign hdr.packet_out.isValid bfalse;
    assign fabric_metadata.is_controller_packet_out btrue;
    exit_; 
  ] []

let fabric_ingress fixed =
  let open HoareNet in
  let open Expr in
  let open BExpr in
  sequence [
    lkp_md_init;
    pkt_io_ingress; check_exit @@
    slice_tc_classifier;
    ifte_seq (eq_ bfalse (var fabric_metadata.is_controller_packet_out)) [
      filtering;
      ifte (eq_ bfalse (var fabric_metadata.skip_forwarding))
        forwarding skip;
      ifte (eq_ bfalse (var fabric_metadata.skip_next))
        pre_next skip;
      acl fixed;
      ifte (eq_ bfalse (var fabric_metadata.skip_next))
        next skip;
      qos;
    ] []
  ]

let pkt_io_egress =  
  let open HoareNet in
  let open Expr in
  let open BExpr in
  sequence [
    ifte_seq (eq_ btrue @@ var fabric_metadata.is_controller_packet_out) [
      exit_
    ] [];
    check_exit @@
    ifte_seq (eq_ (bvi 510 9) @@ var standard_metadata.egress_port) [
      assign hdr.packet_in.isValid btrue;
      assign hdr.packet_in.ingress_port @@ var standard_metadata.ingress_port;
      exit_
    ] []
  ]

let egress_next =
  let open HoareNet in
  let open Expr in
  let open BExpr in
  let push_vlan = [], Action.[
    assign hdr.vlan_tag.isValid btrue;
    havoc hdr.vlan_tag.cfi "push_vlan_havoc_cfi";
    havoc hdr.vlan_tag.pri "push_vlan_havoc_pri";
    havoc hdr.vlan_tag.eth_type "push_vlan_havoc_eth_type";
    havoc hdr.vlan_tag.vlan_id "push_vlan_havoc_vlan_id";
    assign hdr.vlan_tag.cfi @@ var fabric_metadata.vlan_cfi;
    assign hdr.vlan_tag.pri @@ var fabric_metadata.vlan_pri;
    assign hdr.vlan_tag.eth_type @@ bvi 33024 16;
    assign hdr.vlan_tag.vlan_id @@ var fabric_metadata.vlan_id;
    (* egress_vlan_counter.count() *)
  ] in
  let pop_vlan = [], Action.[
    assign hdr.vlan_tag.isValid bfalse;
    (* egress_vlan_counter.count() *)
  ] in
  let drop = [], [
    mark_to_drop
    (* egress_vlan_counter.count() *)
  ] in
  let egress_vlan =
    instr_table("egress_vlan", 
      [
        `Exact fabric_metadata.vlan_id;
        `Exact standard_metadata.egress_port;
      ], [
        push_vlan; pop_vlan; 
        drop (*defaultonly*)
      ]
    )
  in
  sequence [
    ifte_seq (and_
        (eq_ btrue @@ var fabric_metadata.is_multicast) 
        (var standard_metadata.ingress_port |> eq_ @@ var standard_metadata.egress_port)
      ) [
        of_action mark_to_drop
      ] [];
    ifte_seq (var fabric_metadata.mpls_label |> eq_ @@ bvi 0 20) [
      ifte_seq (eq_ btrue @@ var hdr.mpls.isValid) 
        [
          assign hdr.mpls.isValid bfalse;
          assign hdr.eth_type.value @@ var fabric_metadata.ip_eth_type
        ]
        [];
    ] [
      assign hdr.mpls.isValid btrue;
      havoc hdr.mpls.label "egress_havoc_label" |> of_action;
      havoc hdr.mpls.tc "egress_havoc_tc" |> of_action;
      havoc hdr.mpls.bos "egress_havoc_bos" |> of_action;
      havoc hdr.mpls.ttl "egress_havoc_ttl" |> of_action;
      assign hdr.mpls.label @@ var fabric_metadata.mpls_label;
      assign hdr.mpls.tc @@ bvi 0 3;
      assign hdr.mpls.bos @@ bvi  1 1;
      assign hdr.mpls.ttl @@ var fabric_metadata.mpls_ttl;
      assign hdr.eth_type.value @@ bvi 34887 16;
    ];
    egress_vlan;
    ifte_seq (eq_ btrue @@ var hdr.mpls.isValid) [
      assign hdr.mpls.ttl @@ bsub (var hdr.mpls.ttl) (bvi 1 8);
      ifte_seq (var hdr.mpls.ttl |> eq_ @@ bvi 0 8) [
        of_action mark_to_drop
      ] []
    ] [
      ifte_seq (and_ 
        (eq_ btrue @@ var hdr.ipv4.isValid)
        (not_ @@ eq_ (bvi 0 3) @@ var fabric_metadata.fwd_type)
      ) [
        assign hdr.ipv4.ttl @@ bsub (var hdr.ipv4.ttl) (bvi 1 8);
        ifte_seq (var hdr.ipv4.ttl |> eq_ @@ bvi 0 8) [
          of_action mark_to_drop
        ] []
      ] []
    ]
  ]

let dscp_rewriter =
  let open HoareNet in
  let open Expr in
  let open BExpr in
  let tmp_dscp = Var.make "tmp_dscp" 6 in
  let rewriter_action_run = Var.make "rewriter_action_run" 2 in
  let action idx = Action.(assign rewriter_action_run @@ bvi idx 2) in
  let rewrite = [], [action 0] in
  let clear = [], Action.[
    action 1; 
    assign tmp_dscp @@ bvi 0 6;
  ] in
  let nop = [], [action 2] in
  let rewriter = 
    instr_table ("rewriter",[
      `Exact standard_metadata.egress_port;
    ],[
     rewrite; clear; 
     nop (*defaultonly*)
    ])
  in
  let rewrite_or_clear =
    ifte (eq_ btrue @@ var hdr.ipv4.isValid) 
      (assign hdr.inner_ipv4.dscp @@ var tmp_dscp)
      skip
  in
  sequence [
    assign tmp_dscp @@ var fabric_metadata.dscp;
    assign rewriter_action_run @@ bvi 3 2;
    rewriter;
    select (var rewriter_action_run) [
      bvi 0 2,rewrite_or_clear;
      bvi 1 2,rewrite_or_clear;
    ] skip
  ]

let fabric_egress =
  let open HoareNet in
  let open Expr in
  let open BExpr in
  sequence [
    pkt_io_egress; 
    check_exit @@
    ifte_seq (eq_ bfalse @@ var fabric_metadata.is_controller_packet_out) [
      egress_next;
      dscp_rewriter;
    ] []
  ]

let fabric fixed =
  pipeline fabric_parser (fabric_ingress fixed) fabric_egress
