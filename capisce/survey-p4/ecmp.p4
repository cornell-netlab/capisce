
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header ethernet_t {
  bit<48> srcAddr;
  bit<16> etherType;
  bit<48> dstAddr;
}
header ipv4_t {
  bit<8> ttl;
  bit<8> protocol;
  bit<32> dstAddr;
}
header tcp_t {

}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  tcp_t tcp;
}

  
// METADATA



struct routing_metadata_t {

  bit<32> nhop_ipv4;

}
struct my_metadata_t {
  routing_metadata_t routing_metadata;


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


  state parse_ipv4 {
    packet.extract(hdr.ipv4);
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
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType){
      (16w2048) : parse_ipv4;
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
  bit<48> dmac;
  bit<32> nhop_ipv4;
  bit<9> port;

  // Action Definitions
  action ecmp_group_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action ecmp_group_action_1(bit<32> nhop_ipv4,bit<9> port){
    meta.routing_metadata.nhop_ipv4 = nhop_ipv4;
    standard_metadata.egress_spec = port;
    hdr.ipv4.ttl = (hdr.ipv4.ttl + 8w255);
  }

  action ecmp_group_action_2(){

  }

  action forward_action_0(bit<48> dmac){
    hdr.ethernet.dstAddr = dmac;
  }

  action forward_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action forward_action_2(){

  }

  // Table Definitions

  table ecmp_group {
    key = {
      hdr.ipv4.dstAddr : ternary;
    }
    actions = {
      ecmp_group_action_0;
      ecmp_group_action_1;
      ecmp_group_action_2;
    }
  }
    
  table forward {
    key = {
      meta.routing_metadata.nhop_ipv4 : exact;
    }
    actions = {
      forward_action_0;
      forward_action_1;
      forward_action_2;
    }
  }
    

  apply {
    // Pipeline
    if (!((hdr.ipv4.isValid() ? 1w1 : 1w0) == 1w1)) {} else {
      if (!(hdr.ipv4.ttl > 8w0)) {} else {
        ecmp_group.apply();
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
    hdr.ethernet.srcAddr = smac;
  }

  action send_frame_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  // Table Definitions

  table send_frame {
    key = {
      standard_metadata.egress_port : exact;
    }
    actions = {
      send_frame_action_0;
      send_frame_action_1;
    }
  }
    

  apply {
    // Pipeline
    send_frame.apply();
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
  
