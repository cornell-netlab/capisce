
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header ethernet_t {
  bit<16> etherType;
}
header ipv4_t {
  bit<8> protocol;
  bit<32> dstAddr;
}
header rtp_t {
  bit<32> timestamp;
}
header udp_t {

}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  rtp_t rtp;
  udp_t udp;
}

  
// METADATA


struct my_metadata_t {


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
    

  state parse_rtp {
    packet.extract(hdr.rtp);
    transition accept;
  }
    

  state parse_udp {
    packet.extract(hdr.udp);
    transition parse_rtp;
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
  bit<32> dst_ip;

  // Action Definitions
  action schedule_table_action_0(){
    standard_metadata.egress_spec = 9w1;
    hdr.ipv4.dstAddr = dst_ip;
  }

  action schedule_table_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action schedule_table_action_2(){

  }

  // Table Definitions

  table schedule_table {
    key = {
      hdr.ipv4.dstAddr : exact;
      hdr.rtp.timestamp : ternary;
    }
    actions = {
      schedule_table_action_0;
      schedule_table_action_1;
      schedule_table_action_2;
    }
  }
    

  apply {
    // Pipeline

    schedule_table.apply();
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
  
