
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
  bit<16> srcPort;
  bit<16> dstPort;
}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  tcp_t tcp;
}

  
// METADATA



struct ingress_metadata_t {

  bit<32> nhop_ipv4;
  bit<13> flowlet_map_index;
  bit<32> flowlet_lasttime;
  bit<16> flowlet_id;
  bit<32> flow_ipg;
  bit<14> ecmp_offset;

}

struct intrinsic_metadata_t {

  bit<48> ingress_global_timestamp;

}
struct my_metadata_t {
  ingress_metadata_t ingress_metadata;
  intrinsic_metadata_t intrinsic_metadata;


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
    packet.extract(hdr.ethernet);
    transition accept;
  }
    
}

// INGRESS

control MyIngress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
  bit<13> DEVNULL_flowlet_id_lookup_flowlet_map;
  bit<13> DEVNULL_flowlet_id_update_flowlet_id_index;
  bit<16> DEVNULL_flowlet_id_update_flowlet_id_value;
  bit<13> DEVNULL_flowlet_lasttime_lookup_flowlet_map;
  bit<13> DEVNULL_flowlet_lasttime_lookup_flowlet_map_index;
  bit<48> DEVNULL_flowlet_lasttime_lookup_flowlet_map_value;
  bit<48> dmac;
  bit<8> ecmp_base;
  bit<8> ecmp_count;
  bit<16> flowlet_id_lookup_flowlet_map;
  bit<32> flowlet_lasttime_lookup_flowlet_map;
  bit<13> lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index;
  bit<32> lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_0;
  bit<32> lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_1;
  bit<8> lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_2;
  bit<16> lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_3;
  bit<16> lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_4;
  bit<32> nhop_ipv4;
  bit<9> port;
  bit<14> set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset;
  bit<32> set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_0;
  bit<32> set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_1;
  bit<8> set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_2;
  bit<16> set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_3;
  bit<16> set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_4;
  bit<16> set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_5;

  // Action Definitions
  action ecmp_group_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action ecmp_group_action_1(bit<8> ecmp_base,bit<8> ecmp_count){
    set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_0 = hdr.ipv4.srcAddr;
    set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_1 = hdr.ipv4.dstAddr;
    set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_2 = hdr.ipv4.protocol;
    set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_3 = hdr.tcp.srcPort;
    set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_4 = hdr.tcp.dstPort;
    set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset_5 = meta.ingress_metadata.flowlet_id;


    meta.ingress_metadata.ecmp_offset = set_ecmp_select_hash_crc16_meta__ingress_metadata__ecmp_offset;
  }

  action ecmp_group_action_2(){

  }

  action ecmp_nhop_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action ecmp_nhop_action_1(bit<32> nhop_ipv4,bit<9> port){
    meta.ingress_metadata.nhop_ipv4 = nhop_ipv4;
    standard_metadata.egress_spec = port;
    hdr.ipv4.ttl = (hdr.ipv4.ttl + 8w255);
  }

  action ecmp_nhop_action_2(){

  }

  action flowlet_action_0(){
    lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_0 = hdr.ipv4.srcAddr;
    lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_1 = hdr.ipv4.dstAddr;
    lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_2 = hdr.ipv4.protocol;
    lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_3 = hdr.tcp.srcPort;
    lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index_4 = hdr.tcp.dstPort;


    meta.ingress_metadata.flowlet_map_index = lookup_flowlet_map_hash_crc16_meta__ingress_metadata__flowlet_map_index;
    DEVNULL_flowlet_id_lookup_flowlet_map = meta.ingress_metadata.flowlet_map_index;
    meta.ingress_metadata.flowlet_id = flowlet_id_lookup_flowlet_map;
    meta.ingress_metadata.flow_ipg = meta.intrinsic_metadata.ingress_global_timestamp[31:0];
    DEVNULL_flowlet_lasttime_lookup_flowlet_map = meta.ingress_metadata.flowlet_map_index;
    meta.ingress_metadata.flowlet_lasttime = flowlet_lasttime_lookup_flowlet_map;
    meta.ingress_metadata.flow_ipg = (meta.ingress_metadata.flow_ipg - meta.ingress_metadata.flowlet_lasttime);
    DEVNULL_flowlet_lasttime_lookup_flowlet_map_index = meta.ingress_metadata.flowlet_map_index;
    DEVNULL_flowlet_lasttime_lookup_flowlet_map_value = meta.intrinsic_metadata.ingress_global_timestamp;
  }

  action flowlet_action_1(){

  }

  action forward_action_0(){
    hdr.ethernet.dstAddr = dmac;
  }

  action forward_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action forward_action_2(){

  }

  action new_flowlet_action_0(){
    meta.ingress_metadata.flowlet_id = (meta.ingress_metadata.flowlet_id + 16w1);
    DEVNULL_flowlet_id_update_flowlet_id_index = meta.ingress_metadata.flowlet_map_index;
    DEVNULL_flowlet_id_update_flowlet_id_value = meta.ingress_metadata.flowlet_id;
  }

  action new_flowlet_action_1(){

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
    
  table ecmp_nhop {
    key = {
      meta.ingress_metadata.ecmp_offset : exact;
    }
    actions = {
      ecmp_nhop_action_0;
      ecmp_nhop_action_1;
      ecmp_nhop_action_2;
    }
  }
    
  table flowlet {
    key = {
    }
    actions = {
      flowlet_action_0;
      flowlet_action_1;
    }
  }
    
  table forward {
    key = {
      meta.ingress_metadata.nhop_ipv4 : exact;
    }
    actions = {
      forward_action_0;
      forward_action_1;
      forward_action_2;
    }
  }
    
  table new_flowlet {
    key = {
    }
    actions = {
      new_flowlet_action_0;
      new_flowlet_action_1;
    }
  }
    

  apply {
    // Pipeline
    flowlet.apply();
    if (!(meta.ingress_metadata.flow_ipg > 32w50000)) {} else {
      new_flowlet.apply();
    }

    ecmp_group.apply();
    ecmp_nhop.apply();
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
  
