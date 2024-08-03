
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



struct custom_metadata_t {

  bit<32> nhop_ipv4;
  bit<16> hash_val2;
  bit<16> hash_val1;
  bit<16> count_val2;
  bit<16> count_val1;

}
struct my_metadata_t {
  custom_metadata_t custom_metadata;


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
  bit<16> DEVNULL_heavy_hitter_counter1_set_heavy_hitter_count;
  bit<16> DEVNULL_heavy_hitter_counter1_set_heavy_hitter_count_index;
  bit<16> DEVNULL_heavy_hitter_counter1_set_heavy_hitter_count_value;
  bit<16> DEVNULL_heavy_hitter_counter2_set_heavy_hitter_count;
  bit<16> DEVNULL_heavy_hitter_counter2_set_heavy_hitter_count_index;
  bit<16> DEVNULL_heavy_hitter_counter2_set_heavy_hitter_count_value;
  bit<48> dmac;
  bit<16> heavy_hitter_counter1_set_heavy_hitter_count;
  bit<16> heavy_hitter_counter2_set_heavy_hitter_count;
  bit<32> nhop_ipv4;
  bit<9> port;
  bit<16> set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2;
  bit<32> set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_0;
  bit<32> set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_1;
  bit<8> set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_2;
  bit<16> set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_3;
  bit<16> set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_4;
  bit<16> set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1;
  bit<32> set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_0;
  bit<32> set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_1;
  bit<8> set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_2;
  bit<16> set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_3;
  bit<16> set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_4;

  // Action Definitions
  action drop_heavy_hitter_table_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action drop_heavy_hitter_table_action_1(){

  }

  action forward_action_0(bit<48> dmac){
    hdr.ethernet.dstAddr = dmac;
  }

  action forward_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action forward_action_2(){

  }

  action ipv4_lpm_action_0(bit<32> nhop_ipv4,bit<9> port){
    meta.custom_metadata.nhop_ipv4 = nhop_ipv4;
    standard_metadata.egress_spec = port;
    hdr.ipv4.ttl = (hdr.ipv4.ttl + 8w255);
  }

  action ipv4_lpm_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action ipv4_lpm_action_2(){

  }

  action set_heavy_hitter_count_table_action_0(){
    set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_0 = hdr.ipv4.srcAddr;
    set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_1 = hdr.ipv4.dstAddr;
    set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_2 = hdr.ipv4.protocol;
    set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_3 = hdr.tcp.srcPort;
    set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1_4 = hdr.tcp.dstPort;


    meta.custom_metadata.hash_val1 = set_heavy_hitter_count_hash_csum16_meta__custom_metadata__hash_val1;
    DEVNULL_heavy_hitter_counter1_set_heavy_hitter_count = meta.custom_metadata.hash_val1;
    meta.custom_metadata.count_val2 = heavy_hitter_counter1_set_heavy_hitter_count;
    meta.custom_metadata.count_val2 = (meta.custom_metadata.count_val2 + 16w1);
    DEVNULL_heavy_hitter_counter1_set_heavy_hitter_count_index = meta.custom_metadata.hash_val1;
    DEVNULL_heavy_hitter_counter1_set_heavy_hitter_count_value = meta.custom_metadata.count_val2;
    set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_0 = hdr.ipv4.srcAddr;
    set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_1 = hdr.ipv4.dstAddr;
    set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_2 = hdr.ipv4.protocol;
    set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_3 = hdr.tcp.srcPort;
    set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2_4 = hdr.tcp.dstPort;


    meta.custom_metadata.hash_val2 = set_heavy_hitter_count_hash_crc16_meta__custom_metadata__hash_val2;
    DEVNULL_heavy_hitter_counter2_set_heavy_hitter_count = meta.custom_metadata.hash_val2;
    meta.custom_metadata.count_val1 = heavy_hitter_counter2_set_heavy_hitter_count;
    meta.custom_metadata.count_val1 = (meta.custom_metadata.count_val1 + 16w1);
    DEVNULL_heavy_hitter_counter2_set_heavy_hitter_count_index = meta.custom_metadata.hash_val2;
    DEVNULL_heavy_hitter_counter2_set_heavy_hitter_count_value = meta.custom_metadata.count_val1;
  }

  action set_heavy_hitter_count_table_action_1(){

  }

  // Table Definitions

  table drop_heavy_hitter_table {
    key = {
    }
    actions = {
      drop_heavy_hitter_table_action_0;
      drop_heavy_hitter_table_action_1;
    }
  }
    
  table forward {
    key = {
      meta.custom_metadata.nhop_ipv4 : exact;
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
    
  table set_heavy_hitter_count_table {
    key = {
    }
    actions = {
      set_heavy_hitter_count_table_action_0;
      set_heavy_hitter_count_table_action_1;
    }
  }
    

  apply {
    // Pipeline
    set_heavy_hitter_count_table.apply();
    if (!((meta.custom_metadata.count_val2 > 16w100) && (meta.custom_metadata.count_val1 > 16w100))) {
      ipv4_lpm.apply();
      forward.apply();
    } else {
      drop_heavy_hitter_table.apply();
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
  
