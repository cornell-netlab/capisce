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
  srcAddr : Var.t
}

let ipv4 = {
  isValid = Var.make "hdr.ipv4.isValid" 1;
  protocol = Var.make "hdr.ipv4.protocol" 8;
  ttl = Var.make "hdr.ipv4.ttl" 8;
  dstAddr = Var.make "hdr.ipv4.dstAddr" 32;
  srcAddr = Var.make "hdr.ipv4.srcAddr" 32;
}

type tcp_t = {
  isValid : Var.t;
}

let tcp = {
  isValid = Var.make "hdr.ipv4.isValid" 1;
}

type udp_t = {
  isValid : Var.t;
  dstPort : Var.t;
  checksum : Var.t
}

let udp : udp_t = {
  isValid = Var.make "hdr.udp.isValid" 1;
  dstPort = Var.make "hdr.udp.dstPort" 16;
  checksum = Var.make "hdr.udp.checksum" 16;
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

type hdr_t = {
  ethernet : ethernet_t;
  ipv4 : ipv4_t;
  tcp : tcp_t;
  udp : udp_t;
  paxos : paxos_t;
}

let hdr = {ethernet; ipv4; tcp; udp; paxos}

type zombie_t = {
  parse_result : Var.t
}

let zombie : zombie_t = {
  parse_result = Var.make "parse_result" 1;
  (* 1 means successful 0 means failed *)
}

type standard_metadata_t = {
  egress_spec : Var.t;
  egress_port : Var.t;
  ingress_port : Var.t;
}

let standard_metadata = {
  egress_spec = Var.make "standard_metadata.egress_spec" 9;
  egress_port = Var.make "standard_metadata.egress_spec" 9;
  ingress_port = Var.make "standard_metadata.ingress_port" 9;
}

let pipeline prsr ingr egr =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let pipe =
    sequence [
      prsr;
      assume @@ eq_ (var zombie.parse_result) (bvi 1 1);
      ingr;
      assume @@ not_ (eq_ (var standard_metadata.egress_spec) (bvi 0 9));
      assign standard_metadata.egress_port (var standard_metadata.egress_spec);
      egr
    ]
  in
  triple true_ pipe true_


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
