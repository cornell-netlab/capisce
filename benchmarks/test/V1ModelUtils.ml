open Core
open Pbench
open DependentTypeChecker

type ethernet_t = {
  isValid : Var.t;
  etherType : Var.t;
  dstAddr : Var.t;
  srcAddr : Var.t
}

let ethernet = {
  isValid = Var.make "hdr.ethernet.isValid" 1;
  etherType = Var.make "hdr.ethernet.etherType" 16;
  dstAddr = Var.make "hdr.ethernet.dstAddr" 48;
  srcAddr = Var.make "hdr.ethernet.srcAddr" 48;
}

type ipv4_t = {
  isValid : Var.t;
  protocol : Var.t;
  ttl : Var.t;
  dstAddr : Var.t;
  srcAddr : Var.t;
  totalLen : Var.t;
  ihl : Var.t

}

let ipv4 = {
  isValid = Var.make "hdr.ipv4.isValid" 1;
  protocol = Var.make "hdr.ipv4.protocol" 8;
  ttl = Var.make "hdr.ipv4.ttl" 8;
  dstAddr = Var.make "hdr.ipv4.dstAddr" 32;
  srcAddr = Var.make "hdr.ipv4.srcAddr" 32;
  totalLen = Var.make "hdr.ipv4.totalLen" 16;
  ihl = Var.make "hdr.ipv4.ihl" 4;
}

type ipv6_t = {
  isValid : Var.t;
  nextHdr : Var.t;
  dstAddr : Var.t;
}
let ipv6 : ipv6_t = {
  isValid = Var.make "hdr.ipv6.isValid" 1 ;
  dstAddr = Var.make "hdr.ipv6.dstAddr" 48;
  nextHdr = Var.make "hdr.ipv6.nextHdr" 8 ;
}

type vlan_tag_t = {
  isValid : Var.t;
  etherType : Var.t;
}

let vlan_tag : vlan_tag_t = {
  isValid = Var.make "hdr.vlan_tag.isValid" 1;
  etherType = Var.make "hdr.vlan_tag.etherType" 16;
}

type arp_t = {
  isValid : Var.t;
  htype : Var.t;
  ptype : Var.t;
  hlen : Var.t;
  plen : Var.t;
  oper : Var.t
}

let arp : arp_t = {
  isValid = Var.make "hdr.arp.isValid" 1;
  htype = Var.make "hdr.arp.htype" 16;
  ptype = Var.make "hdr.arp.ptype" 16;
  hlen = Var.make "hdr.arp.hlen" 8;
  plen = Var.make "hdr.arp.plen" 8;
  oper = Var.make "hdr.arp.oper" 16;
}

type arp_ipv4_t = {
  isValid : Var.t;
  sha : Var.t;
  spa : Var.t;
  tha : Var.t;
  tpa : Var.t;
}

let arp_ipv4 : arp_ipv4_t = {
  isValid = Var.make "hdr.arp_ipv4.isValid" 1;
  sha = Var.make "hdr.arp_ipv4.sha" 48;
  spa = Var.make "hdr.arp_ipv4.spa" 32;
  tha = Var.make "hdr.arp_ipv4.tha" 48;
  tpa = Var.make "hdr.arp_ipv4.tpa" 32
}

type tcp_t = {
  isValid : Var.t;
  dstPort : Var.t;
  srcPort : Var.t;
}

let tcp = {
  isValid = Var.make "hdr.tcp.isValid" 1;
  dstPort = Var.make "hdr.tcp.dstPort" 16;
  srcPort = Var.make "hdr.tcp.srcPort" 16
}

type udp_t = {
  isValid : Var.t;
  dstPort : Var.t;
  checksum : Var.t;
  length : Var.t

}

let udp : udp_t = {
  isValid = Var.make "hdr.udp.isValid" 1;
  dstPort = Var.make "hdr.udp.dstPort" 16;
  checksum = Var.make "hdr.udp.checksum" 16;
  length = Var.make "hdr.udp.length" 16;
}

type icmp_t = {
  isValid : Var.t;
  type_ : Var.t;
  checksum : Var.t;
}

let icmp : icmp_t = {
  isValid = Var.make "hdr.icmp.isValid" 1;
  type_ = Var.make "hdr.icmp.type" 8;
  checksum = Var.make "hdr.icmp.checksum" 16;
}

(* for netpaxos_acceptor *)
type paxos_t = {
  isValid : Var.t;
  msgtype : Var.t;
  proposal : Var.t;
  vproposal : Var.t
}

let paxos : paxos_t = {
  isValid = Var.make "hdr.paxos.isValid" 1;
  msgtype = Var.make "hdr.paxos.msgtype" 16;
  proposal = Var.make "hdr.paxos.proposal" 16;
  vproposal = Var.make "hdr.paxos.vproposal" 16;
}

(* used in ndp_router *)
type ndp_t = {
  isValid : Var.t;
  flags : Var.t
}

let ndp : ndp_t = {
  isValid = Var.make "hdr.ndp.isValid" 1;
  flags = Var.make "hdr.ndp.flags" 16;
}
type rtp_t = {
  isValid : Var.t;
  timestamp : Var.t
}
let rtp : rtp_t = {
  isValid = Var.make "hdr.rtp.isValid" 1;
  timestamp = Var.make "hdr.rtp.timestamp" 32;
}

type cpu_header_t = {
  isValid : Var.t;
  preamble : Var.t;
  device : Var.t;
  reason : Var.t;
  if_index : Var.t
}

let cpu_header : cpu_header_t = {
  isValid = Var.make "hdr.cpu_header.isValid" 1;
  preamble = Var.make "hdr.cpu_header.preamble" 64;
  device = Var.make "hdr.cpu_header.device" 8;
  reason = Var.make "hdr.cpu_header.reason" 8;
  if_index = Var.make "hdr.cpu_header.if_index" 8;
}

type hdr_t = {
  ethernet : ethernet_t;
  ipv4 : ipv4_t;
  ipv6 : ipv6_t;
  vlan_tag : vlan_tag_t;
  tcp : tcp_t;
  icmp : icmp_t;
  udp : udp_t;
  ndp : ndp_t;
  paxos : paxos_t;
  arp : arp_t;
  arp_ipv4 : arp_ipv4_t;
  rtp : rtp_t;
  cpu_header : cpu_header_t
}

let hdr = {ethernet;
           ipv4; ipv6; vlan_tag;
           tcp; udp; icmp;
           paxos; ndp;
           arp; arp_ipv4;
           rtp; cpu_header;
          }

type zombie_t = {
  parse_result : Var.t;
  exited : Var.t;
}

let zombie : zombie_t = {
  parse_result = Var.make "parse_result" 1;
  (* 1 means successful 0 means failed *)
  exited = Var.make "exited" 1;
  (* 1 means `exit` was executed *)
}

type standard_metadata_t = {
  egress_spec : Var.t;
  egress_port : Var.t;
  ingress_port : Var.t;
  deq_qdepth : Var.t;
  instance_type : Var.t;
}

let standard_metadata = {
  egress_spec = Var.make "standard_metadata.egress_spec" 9;
  egress_port = Var.make "standard_metadata.egress_port" 9;
  ingress_port = Var.make "standard_metadata.ingress_port" 9;
  deq_qdepth = Var.make "standard_metadata.deq_qdepth" 19;
  instance_type = Var.make "standard_metadata.instance_type" 32;
}

let ifte guard tru fls =
  let open HoareNet in
  let open BExpr in
  choice_seqs [
    [assume guard; tru];
    [assume @@ not_ guard; fls]
  ]

let ifte_seq guard true_seqs false_seqs =
  let open HoareNet in
  let open BExpr in
  choice_seqs [
    assume guard::true_seqs;
    assume (not_ guard) :: false_seqs
  ]

let btrue = Expr.bvi 1 1
let bfalse = Expr.bvi 0 1

let transition_accept =
  let open HoareNet in
  assign zombie.parse_result btrue

let select discriminee cases default : HoareNet.t =
  List.fold_right cases ~init:default
    ~f:(fun (value, state) cont ->
        ifte (BExpr.eq_ value discriminee) state cont
      )

let mark_to_drop =
  let open Primitives in
  Action.assign_ @@
  Assign.assign standard_metadata.egress_spec @@
  Expr.bvi 511 9

let pipeline prsr ingr egr =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let pipe =
    sequence [
      assign zombie.parse_result bfalse;
      prsr;
      ifte_seq (eq_ (var zombie.parse_result) (bvi 1 1)) [
        ingr;
        ifte_seq (eq_ (var standard_metadata.egress_spec) (bvi 511 9)) [] [
          assign standard_metadata.egress_port (var standard_metadata.egress_spec);
          egr
        ]
      ] [skip]
    ]
  in
  triple true_ pipe true_
