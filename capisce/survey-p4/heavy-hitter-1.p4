
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
  bit<32> srcAddr;
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


  state parse_ethernet {
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType){
      (16w2048) : parse_ipv4;
      default : accept;
    }

  }
    

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
  bit<32> idx;
  bit<9> port;
  bit<32> set_nhop;

  // Action Definitions
  action count_table_action_0(bit<32> idx){

  }

  action count_table_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action count_table_action_2(){

  }

  action forward_action_0(bit<48> dmac){
    hdr.ethernet.dstAddr = dmac;
  }

  action forward_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action forward_action_2(){

  }

  action ipv4_lpm_action_0(bit<32> set_nhop,bit<9> port){
    meta.routing_metadata.nhop_ipv4 = set_nhop;
    standard_metadata.egress_spec = port;
    hdr.ipv4.ttl = (hdr.ipv4.ttl + 8w255);
  }

  action ipv4_lpm_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action ipv4_lpm_action_2(){

  }

  // Table Definitions

  table count_table {
    key = {
      hdr.ipv4.srcAddr : ternary;
    }
    actions = {
      count_table_action_0;
      count_table_action_1;
      count_table_action_2;
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
    
  table ipv4_lpm {
    key = {
      hdr.ipv4.dstAddr : ternary;
    }
    actions = {
      ipv4_lpm_action_0;
      ipv4_lpm_action_1;
      ipv4_lpm_action_2;
    }
  }
    

  apply {
    // Pipeline
    count_table.apply();
    ipv4_lpm.apply();
    forward.apply();
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

  action send_frame_action_2(){

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
  
