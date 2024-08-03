
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header ethernet_t {
  bit<16> etherType;
}
header ipv4_t {
  bit<8> ttl;
  bit<8> protocol;
  bit<32> dstAddr;
}
header udp_t {

}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  udp_t udp;
}

  
// METADATA



struct intrinsic_metadata_t {

  bit<16> mcast_grp;
  bit<16> egress_rid;

}
struct my_metadata_t {
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
      (8w17) : parse_udp;
      default : accept;
    }

  }
    

  state parse_udp {
    packet.extract(hdr.udp);
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
  bit<16> mcast_group;

  // Action Definitions
  action set_mcg_action_0(bit<16> mcast_group){
    meta.intrinsic_metadata.mcast_grp = mcast_group;
  }

  action set_mcg_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action set_mcg_action_2(){

  }

  // Table Definitions

  table set_mcg {
    key = {
      hdr.ipv4.dstAddr : exact;
    }
    actions = {
      set_mcg_action_0;
      set_mcg_action_1;
      set_mcg_action_2;
    }
  }
    

  apply {
    // Pipeline

    set_mcg.apply();
  }
}
  
// EGRESS

control MyEgress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
  bit<32> dst_ip;

  // Action Definitions
  action nat_table_action_0(bit<32> dst_ip){
    hdr.ipv4.dstAddr = dst_ip;
    hdr.ipv4.ttl = (hdr.ipv4.ttl + 8w255);
  }

  action nat_table_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action nat_table_action_2(){

  }

  // Table Definitions

  table nat_table {
    key = {
      meta.intrinsic_metadata.egress_rid : exact;
      hdr.ipv4.dstAddr : exact;
    }
    actions = {
      nat_table_action_0;
      nat_table_action_1;
      nat_table_action_2;
    }
  }
    

  apply {
    // Pipeline
    nat_table.apply();
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
  
