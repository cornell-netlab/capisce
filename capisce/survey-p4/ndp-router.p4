
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
  bit<16> totalLen;
  bit<8> protocol;
  bit<32> dstAddr;
}
header ndp_t {
  bit<16> flags;
}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  ndp_t ndp;
}

  
// METADATA



struct meta_t {

  bit<16> register_tmp;
  bit<16> ndpflags;

}

struct routing_metadata_t {

  bit<32> nhop_ipv4;

}
struct my_metadata_t {
  meta_t meta;
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
      (8w199) : parse_ndp;
      default : accept;
    }

  }
    

  state parse_ndp {
    packet.extract(hdr.ndp);
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
  bit<9> DEVNULL_buffersense_readbuffer;
  bit<9> DEVNULL_buffersense_set_dmac;
  bit<9> DEVNULL_buffersense_setpriolow;
  bit<9> DEVNULL_buffersense_setpriolow_index;
  bit<16> DEVNULL_buffersense_setpriolow_value;
  bit<16> buffersense_readbuffer;
  bit<16> buffersense_set_dmac;
  bit<16> buffersense_setpriolow;
  bit<48> dmac;
  bit<32> nhop_ipv4;
  bit<9> port;

  // Action Definitions
  action directtoprio_action_0(){
    standard_metadata.egress_spec = 9w1;
    meta.meta.ndpflags = hdr.ndp.flags;
  }

  action directtoprio_action_1(){

  }

  action forward_action_0(bit<48> dmac){
    hdr.ethernet.dstAddr = dmac;
    DEVNULL_buffersense_set_dmac = standard_metadata.egress_port;
    meta.meta.register_tmp = buffersense_set_dmac;
  }

  action forward_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action forward_action_2(){

  }

  action ipv4_lpm_action_0(bit<32> nhop_ipv4,bit<9> port){
    meta.routing_metadata.nhop_ipv4 = nhop_ipv4;
    standard_metadata.egress_port = port;
    hdr.ipv4.ttl = (hdr.ipv4.ttl + 8w255);
  }

  action ipv4_lpm_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action ipv4_lpm_action_2(){

  }

  action readbuffersense_action_0(){
    DEVNULL_buffersense_readbuffer = standard_metadata.egress_port;
    meta.meta.register_tmp = buffersense_readbuffer;
  }

  action readbuffersense_action_1(){

  }

  action setprio_action_0(){
    standard_metadata.egress_spec = 9w0;
    DEVNULL_buffersense_setpriolow = standard_metadata.egress_port;
    meta.meta.register_tmp = buffersense_setpriolow;
    DEVNULL_buffersense_setpriolow_index = standard_metadata.egress_port;
    DEVNULL_buffersense_setpriolow_value = (meta.meta.register_tmp + 16w1);
  }

  action setprio_action_1(){
    hdr.ipv4.totalLen = 16w20;
    standard_metadata.egress_spec = 9w1;
  }

  action setprio_action_2(){

  }

  // Table Definitions

  table directtoprio {
    key = {
      meta.meta.register_tmp : exact;
    }
    actions = {
      directtoprio_action_0;
      directtoprio_action_1;
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
    
  table readbuffersense {
    key = {
      meta.meta.register_tmp : exact;
    }
    actions = {
      readbuffersense_action_0;
      readbuffersense_action_1;
    }
  }
    
  table setprio {
    key = {
      meta.meta.register_tmp : exact;
    }
    actions = {
      setprio_action_0;
      setprio_action_1;
      setprio_action_2;
    }
  }
    

  apply {
    // Pipeline
    if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {
      standard_metadata.egress_spec = 9w511;
    } else {
      if (!(hdr.ipv4.ttl > 8w0)) {
        standard_metadata.egress_spec = 9w511;
      } else {
        ipv4_lpm.apply();
        if (!(1w1 == (hdr.ndp.isValid() ? 1w1 : 1w0))) {
          readbuffersense.apply();
          setprio.apply();
        } else {
          if (!(hdr.ndp.flags > 16w1)) {
            readbuffersense.apply();
            setprio.apply();
          } else {
            directtoprio.apply();
          }

        }

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
  bit<9> DEVNULL_buffersense_decreasereg;
  bit<9> DEVNULL_buffersense_decreasereg_index;
  bit<16> DEVNULL_buffersense_decreasereg_value;
  bit<16> buffersense_decreasereg;
  bit<48> smac;

  // Action Definitions
  action dec_counter_action_0(){
    DEVNULL_buffersense_decreasereg = standard_metadata.egress_port;
    meta.meta.register_tmp = buffersense_decreasereg;
    DEVNULL_buffersense_decreasereg_index = standard_metadata.egress_port;
    DEVNULL_buffersense_decreasereg_value = ((meta.meta.register_tmp - 16w1) + (7w0 ++ standard_metadata.egress_spec));
  }

  action dec_counter_action_1(){

  }

  action dec_counter_action_2(){

  }

  action send_frame_action_0(bit<48> smac){
    hdr.ethernet.srcAddr = smac;
  }

  action send_frame_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action send_frame_action_2(){

  }

  // Table Definitions

  table dec_counter {
    key = {
      meta.meta.ndpflags : exact;
    }
    actions = {
      dec_counter_action_0;
      dec_counter_action_1;
      dec_counter_action_2;
    }
  }
    
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
    dec_counter.apply();
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
  
