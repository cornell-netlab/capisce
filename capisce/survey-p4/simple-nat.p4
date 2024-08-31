
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header cpu_header_t {
  bit<8> reason;
  bit<64> preamble;
  bit<8> if_index;
  bit<8> device;
}
header ethernet_t {
  bit<48> srcAddr;
  bit<16> etherType;
  bit<48> dstAddr;
}
header ipv4_t {
  bit<8> ttl;
  bit<16> totalLen;
  bit<32> srcAddr;
  bit<8> protocol;
  bit<32> dstAddr;
}
header tcp_t {
  bit<16> srcPort;
  bit<16> dstPort;
}
// Assemble headers in a single struct
struct my_headers_t {
  cpu_header_t cpu_header;
  ethernet_t ethernet;
  ipv4_t ipv4;
  tcp_t tcp;
}

  
// METADATA



struct meta_t {

  bit<16> tcp_sp;
  bit<16> tcp_dp;
  bit<16> tcpLength;
  bit<32> nhop_ipv4;
  bit<1> is_ext_if;
  bit<32> ipv4_sa;
  bit<32> ipv4_da;
  bit<48> if_mac_addr;
  bit<32> if_ipv4_addr;
  bit<8> if_index;
  bit<1> do_forward;

}
struct my_metadata_t {
  meta_t meta;


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


  state parse_ethernet {
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType){
      (16w2048) : parse_ipv4;
      default : accept;
    }

  }
    

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    meta.meta.ipv4_sa = hdr.ipv4.srcAddr;
    meta.meta.ipv4_da = hdr.ipv4.dstAddr;
    meta.meta.tcpLength = (hdr.ipv4.totalLen - 16w20);
    transition select(hdr.ipv4.protocol){
      (8w6) : parse_tcp;
      default : accept;
    }

  }
    

  state parse_tcp {
    packet.extract(hdr.tcp);
    transition accept;
  }
    

  state start {

    transition parse_ethernet;
  }
    
}

// INGRESS

control MyIngress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
  bit<48> dmac;
  bit<32> dstAddr;
  bit<16> dstPort;
  bit<32> ipv4_addr;
  bit<1> is_ext;
  bit<48> mac_addr;
  bit<32> nhop_ipv4;
  bit<9> port;

  // Action Definitions
  action forward_action_0(bit<48> dmac){
    hdr.ethernet.dstAddr = dmac;
  }

  action forward_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action forward_action_2(){

  }

  action if_info_action_0(bit<32> ipv4_addr,bit<48> mac_addr,bit<1> is_ext){
    meta.meta.if_ipv4_addr = ipv4_addr;
    meta.meta.if_mac_addr = mac_addr;
    meta.meta.is_ext_if = is_ext;
  }

  action if_info_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action if_info_action_2(){

  }

  action ipv4_lpm_action_0(bit<32> nhop_ipv4,bit<9> port){
    meta.meta.nhop_ipv4 = nhop_ipv4;
    standard_metadata.egress_spec = port;
    hdr.ipv4.ttl = (hdr.ipv4.ttl - 8w1);
  }

  action ipv4_lpm_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action ipv4_lpm_action_2(){

  }

  action nat_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action nat_action_1(){

  }

  action nat_action_2(){
    meta.meta.do_forward = 1w0;
    standard_metadata.egress_spec = 9w511;
  }

  action nat_action_3(){

  }

  action nat_action_4(bit<32> dstAddr,bit<16> dstPort){
    meta.meta.do_forward = 1w1;
    meta.meta.ipv4_da = dstAddr;
    meta.meta.tcp_dp = dstPort;
  }

  action nat_action_5(){
    meta.meta.do_forward = 1w1;
  }

  action nat_action_6(){

  }

  // Table Definitions

  table forward {
    key = {
      meta.meta.nhop_ipv4 : exact;
    }
    actions = {
      forward_action_0;
      forward_action_1;
      forward_action_2;
    }
  }
    
  table if_info {
    key = {
      meta.meta.if_index : exact;
    }
    actions = {
      if_info_action_0;
      if_info_action_1;
      if_info_action_2;
    }
  }
    
  table ipv4_lpm {
    key = {
      meta.meta.ipv4_da : exact;
    }
    actions = {
      ipv4_lpm_action_0;
      ipv4_lpm_action_1;
      ipv4_lpm_action_2;
    }
  }
    
  table nat {
    key = {
      meta.meta.is_ext_if : exact;
      hdr.ipv4.isValid() : exact;
      hdr.tcp.isValid() : exact;
      hdr.ipv4.srcAddr : ternary;
      hdr.ipv4.dstAddr : ternary;
      hdr.tcp.srcPort : ternary;
      hdr.tcp.dstPort : ternary;
    }
    actions = {
      nat_action_0;
      nat_action_1;
      nat_action_2;
      nat_action_3;
      nat_action_4;
      nat_action_5;
      nat_action_6;
    }
  }
    

  apply {
    // Pipeline
    if_info.apply();
    nat.apply();
    if (!(meta.meta.do_forward == 1w1)) {} else {
      if ((hdr.ipv4.ttl == 8w0)) {} else {
        ipv4_lpm.apply();
        forward.apply();
      }

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
  bit<48> smac;

  // Action Definitions
  action send_frame_action_0(bit<48> smac){
    hdr.cpu_header.setInvalid();
    hdr.ethernet.srcAddr = smac;
    hdr.ipv4.srcAddr = meta.meta.ipv4_sa;
    hdr.ipv4.dstAddr = meta.meta.ipv4_da;
    hdr.tcp.srcPort = meta.meta.tcp_sp;
    hdr.tcp.dstPort = meta.meta.tcp_dp;
  }

  action send_frame_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action send_frame_action_2(){

  }

  action send_to_cpu_action_0(){
    hdr.cpu_header.setValid();
    hdr.cpu_header.preamble = 64w0;
    hdr.cpu_header.device = 8w0;
    hdr.cpu_header.reason = 8w171;
    hdr.cpu_header.if_index = meta.meta.if_index;
  }

  action send_to_cpu_action_1(){

  }

  // Table Definitions

  table send_frame {
    key = {
      standard_metadata.egress_port : exact;
    }
    actions = {
      send_frame_action_0;
      send_frame_action_1;
      send_frame_action_2;
    }
  }
    
  table send_to_cpu {
    key = {
    }
    actions = {
      send_to_cpu_action_0;
      send_to_cpu_action_1;
    }
  }
    

  apply {
    // Pipeline
    if (!(standard_metadata.instance_type == 32w0)) {
      send_to_cpu.apply();
    } else {
      send_frame.apply();
    }

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
  
