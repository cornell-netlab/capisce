
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header ethernet_t {

}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
}

  
// METADATA



struct mymeta_t {

  bit<8> f2;
  bit<8> f1;

}
struct my_metadata_t {
  mymeta_t mymeta;


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
  bit<9> port;

  // Action Definitions
  action t_ingress_1_action_0(){

  }

  action t_ingress_1_action_1(){
    standard_metadata.egress_spec = port;
  }

  action t_ingress_2_action_0(){

  }

  action t_ingress_2_action_1(){
    meta.mymeta.f1 = 8w1;
  }

  // Table Definitions

  table t_ingress_1 {
    key = {
      meta.mymeta.f1 : exact;
    }
    actions = {
      t_ingress_1_action_0;
      t_ingress_1_action_1;
    }
  }
    
  table t_ingress_2 {
    key = {
      meta.mymeta.f2 : exact;
    }
    actions = {
      t_ingress_2_action_0;
      t_ingress_2_action_1;
    }
  }
    

  apply {
    // Pipeline
    t_ingress_1.apply();
    t_ingress_2.apply();
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
  
