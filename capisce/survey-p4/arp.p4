
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header arp_t {
  bit<16> ptype;
  bit<8> plen;
  bit<16> oper;
  bit<16> htype;
  bit<8> hlen;
}
header arp_ipv4_t {
  bit<32> tpa;
  bit<48> tha;
  bit<32> spa;
  bit<48> sha;
}
header ethernet_t {
  bit<48> srcAddr;
  bit<16> etherType;
  bit<48> dstAddr;
}
header icmp_t {
  bit<8> type;
  bit<16> checksum;
}
header ipv4_t {
  bit<8> ttl;
  bit<32> srcAddr;
  bit<8> protocol;
  bit<32> dstAddr;
}
// Assemble headers in a single struct
struct my_headers_t {
  arp_t arp;
  arp_ipv4_t arp_ipv4;
  ethernet_t ethernet;
  icmp_t icmp;
  ipv4_t ipv4;
}

  
// METADATA


struct my_metadata_t {

  bit<48> my_mac;
  bit<48> mac_sa;
  bit<48> mac_da;
  bit<9> egress_port;
  bit<32> dst_ipv4;

}
// PARSER

parser MyParser(
  packet_in packet,
  out my_headers_t hdr,
  inout my_metadata_t meta,
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions

  // Parser state machine


  state parse_arp {
    packet.extract(hdr.arp);
    transition select(hdr.arp.htype,hdr.arp.ptype,hdr.arp.hlen,hdr.arp.plen){
      (16w1,16w2048,8w6,8w4) : parse_arp_ipv4;
      default : accept;
    }

  }
    

  state parse_arp_ipv4 {
    packet.extract(hdr.arp_ipv4);
    meta.dst_ipv4 = hdr.arp_ipv4.tpa;
    transition accept;
  }
    

  state parse_icmp {
    packet.extract(hdr.icmp);
    transition accept;
  }
    

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    meta.dst_ipv4 = hdr.ipv4.dstAddr;
    transition select(hdr.ipv4.protocol){
      (8w1) : parse_icmp;
      default : accept;
    }

  }
    

  state start {
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType){
      (16w2048) : parse_ipv4;
      (16w2054) : parse_arp;
      default : accept;
    }

  }
    
}

// INGRESS

control MyIngress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
  bit<9> egress_port;
  bit<1> exited;
  bit<48> mac_da;
  bit<48> mac_sa;
  bit<32> tmp_ip;
  bit<48> tmp_mac;

  // Action Definitions
  action forward_action_0(){
    hdr.ethernet.dstAddr = meta.mac_da;
    hdr.ethernet.srcAddr = meta.mac_sa;
    hdr.ipv4.ttl = (hdr.ipv4.ttl - 8w1);
    standard_metadata.egress_spec = meta.egress_port;
  }

  action forward_action_1(){
    hdr.ethernet.dstAddr = hdr.arp_ipv4.sha;
    hdr.ethernet.srcAddr = meta.mac_da;
    hdr.arp.oper = 16w2;
    hdr.arp_ipv4.tha = hdr.arp_ipv4.sha;
    hdr.arp_ipv4.tpa = hdr.arp_ipv4.spa;
    hdr.arp_ipv4.sha = meta.mac_da;
    hdr.arp_ipv4.spa = meta.dst_ipv4;
    standard_metadata.egress_spec = standard_metadata.ingress_port;
  }

  action forward_action_2(){
    tmp_mac = hdr.ethernet.dstAddr;
    hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
    hdr.ethernet.srcAddr = tmp_mac;
    tmp_ip = hdr.ipv4.dstAddr;
    hdr.ipv4.dstAddr = hdr.ipv4.srcAddr;
    hdr.ipv4.srcAddr = tmp_ip;
    hdr.icmp.type = 8w0;
    hdr.icmp.checksum = 16w0;
    standard_metadata.egress_spec = standard_metadata.ingress_port;
  }

  action forward_action_3(){
    standard_metadata.egress_spec = 9w511;
    exited = 1w1;
  }

  action ipv4_lpm_action_0(bit<48> mac_da,bit<48> mac_sa,bit<9> egress_port){
    meta.mac_da = mac_da;
    meta.mac_sa = mac_sa;
    meta.egress_port = egress_port;
  }

  action ipv4_lpm_action_1(){
    standard_metadata.egress_spec = 9w511;
    exited = 1w1;
  }

  // Table Definitions

  table forward {
    key = {
      hdr.arp.isValid() : exact;
      hdr.arp.oper : exact;
      hdr.arp_ipv4.isValid() : exact;
      hdr.ipv4.isValid() : exact;
      hdr.icmp.isValid() : exact;
      hdr.icmp.type : ternary;
    }
    actions = {
      forward_action_0;
      forward_action_1;
      forward_action_2;
      forward_action_3;
    }
  }
    
  table ipv4_lpm {
    key = {
      meta.dst_ipv4 : exact;
    }
    actions = {
      ipv4_lpm_action_0;
      ipv4_lpm_action_1;
    }
  }
    

  apply {
    // Pipeline
    meta.my_mac = 48w102030405;
    if ((1w1 == exited)) {} else {
      ipv4_lpm.apply();
      forward.apply();
    }

  }
}
  
// EGRESS

control MyEgress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions

  // Action Definitions

  // Table Definitions


  apply {
    // Pipeline

  }
}
  
// OTHER
control MyVerifyChecksum(
    inout my_headers_t   hdr,
    inout my_metadata_t  meta)
{
    apply {     }
}

control MyComputeChecksum(
    inout my_headers_t  hdr,
    inout my_metadata_t meta)
{
    apply {   }
}
control MyDeparser(
    packet_out      packet,
    in my_headers_t hdr)
{
    apply {
    }
}
V1Switch(
    MyParser(),
    MyVerifyChecksum(),
    MyIngress(),
    MyEgress(),
    MyComputeChecksum(),
    MyDeparser()
) main;
  
