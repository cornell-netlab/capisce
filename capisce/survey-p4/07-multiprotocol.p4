
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header ethernet_t {
  bit<16> etherType;
  bit<48> dstAddr;
}
header icmp_t {
  bit<8> type;
}
header ipv4_t {
  bit<8> protocol;
  bit<4> ihl;
  bit<32> dstAddr;
}
header ipv6_t {
  bit<8> nextHdr;
  bit<48> dstAddr;
}
header tcp_t {
  bit<16> dstPort;
}
header udp_t {
  bit<16> dstPort;
}
header vlan_tag_t {
  bit<16> etherType;
}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  icmp_t icmp;
  ipv4_t ipv4;
  ipv6_t ipv6;
  tcp_t tcp;
  udp_t udp;
  vlan_tag_t vlan_tag;
}

  
// METADATA



struct ing_metadata_t {

  bit<4> packet_type;
  bit<9> egress_port;
  bit<1> drop;

}
struct my_metadata_t {
  ing_metadata_t ing_metadata;


}
// PARSER

parser MyParser(
  packet_in packet,
  out my_headers_t hdr,
  inout my_metadata_t meta,
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
  bit<1> forwarded;

  // Parser state machine


  state parse_icmp {
    packet.extract(hdr.icmp);
    transition accept;
  }
    

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    transition select(hdr.ipv4.ihl,hdr.ipv4.protocol){
      (4w5,8w1) : parse_icmp;
      (4w5,8w6) : parse_tcp;
      (4w5,8w17) : parse_udp;
      default : accept;
    }

  }
    

  state parse_ipv6 {
    packet.extract(hdr.ipv6);
    transition select(hdr.ipv6.nextHdr){
      (8w1) : parse_icmp;
      (8w6) : parse_tcp;
      (8w17) : parse_udp;
      default : accept;
    }

  }
    

  state parse_tcp {
    packet.extract(hdr.tcp);
    transition accept;
  }
    

  state parse_udp {
    packet.extract(hdr.udp);
    transition accept;
  }
    

  state parse_vlan_tag {
    packet.extract(hdr.vlan_tag);
    transition select(hdr.vlan_tag.etherType){
      (16w2048) : parse_ipv4;
      (16w34525) : parse_ipv6;
      default : accept;
    }

  }
    

  state start {
    forwarded = 1w0;
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType){
      (16w33024) : parse_vlan_tag;
      (16w37120) : parse_vlan_tag;
      (16w2048) : parse_ipv4;
      (16w34525) : parse_ipv6;
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
  bit<3> ethertype_action_run;
  bit<1> forwarded;

  // Action Definitions
  action ethertype_match_action_0(){
    meta.ing_metadata.packet_type = 4w0;
    ethertype_action_run = 3w0;
  }

  action ethertype_match_action_1(){
    meta.ing_metadata.packet_type = 4w1;
    ethertype_action_run = 3w1;
  }

  action ethertype_match_action_2(){
    meta.ing_metadata.packet_type = 4w2;
    ethertype_action_run = 3w2;
  }

  action ethertype_match_action_3(){
    meta.ing_metadata.packet_type = 4w3;
    ethertype_action_run = 3w3;
  }

  action ethertype_match_action_4(){
    meta.ing_metadata.packet_type = 4w4;
    ethertype_action_run = 3w4;
  }

  action ethertype_match_action_5(){

  }

  action icmp_check_action_0(){

  }

  action icmp_check_action_1(){
    meta.ing_metadata.drop = 1w1;
  }

  action ipv4_match_action_0(){

  }

  action ipv4_match_action_1(bit<9> egress_port){
    meta.ing_metadata.egress_port = egress_port;
  }

  action ipv6_match_action_0(){

  }

  action ipv6_match_action_1(bit<9> egress_port){
    meta.ing_metadata.egress_port = egress_port;
  }

  action l2_match_action_0(){

  }

  action l2_match_action_1(bit<9> egress_port){
    meta.ing_metadata.egress_port = egress_port;
  }

  action set_egress_action_0(){
    forwarded = 1w1;
    standard_metadata.egress_spec = 9w511;
  }

  action set_egress_action_1(){
    forwarded = 1w1;
    standard_metadata.egress_spec = meta.ing_metadata.egress_port;
  }

  action set_egress_action_2(){

  }

  action tcp_check_action_0(){

  }

  action tcp_check_action_1(){
    meta.ing_metadata.drop = 1w1;
  }

  action udp_check_action_0(){

  }

  action udp_check_action_1(){
    meta.ing_metadata.drop = 1w1;
  }

  // Table Definitions

  table ethertype_match {
    key = {
      hdr.ethernet.etherType : exact;
    }
    actions = {
      ethertype_match_action_0;
      ethertype_match_action_1;
      ethertype_match_action_2;
      ethertype_match_action_3;
      ethertype_match_action_4;
      ethertype_match_action_5;
    }
  }
    
  table icmp_check {
    key = {
      hdr.icmp.type : exact;
    }
    actions = {
      icmp_check_action_0;
      icmp_check_action_1;
    }
  }
    
  table ipv4_match {
    key = {
      hdr.ipv4.dstAddr : exact;
    }
    actions = {
      ipv4_match_action_0;
      ipv4_match_action_1;
    }
  }
    
  table ipv6_match {
    key = {
      hdr.ipv6.dstAddr : exact;
    }
    actions = {
      ipv6_match_action_0;
      ipv6_match_action_1;
    }
  }
    
  table l2_match {
    key = {
      hdr.ethernet.dstAddr : exact;
    }
    actions = {
      l2_match_action_0;
      l2_match_action_1;
    }
  }
    
  table set_egress {
    key = {
      meta.ing_metadata.drop : exact;
    }
    actions = {
      set_egress_action_0;
      set_egress_action_1;
      set_egress_action_2;
    }
  }
    
  table tcp_check {
    key = {
      hdr.tcp.dstPort : exact;
    }
    actions = {
      tcp_check_action_0;
      tcp_check_action_1;
    }
  }
    
  table udp_check {
    key = {
      hdr.udp.dstPort : exact;
    }
    actions = {
      udp_check_action_0;
      udp_check_action_1;
    }
  }
    

  apply {
    // Pipeline
    ethertype_match.apply();
    if (!(3w1 == ethertype_action_run)) {
      if (!(3w2 == ethertype_action_run)) {
        if (!(3w3 == ethertype_action_run)) {
          l2_match.apply();
        } else {
          ipv6_match.apply();
        }

      } else {
        ipv6_match.apply();
      }

    } else {
      ipv4_match.apply();
    }

    if (!(1w1 == (hdr.tcp.isValid() ? 1w1 : 1w0))) {
      if (!(1w1 == (hdr.udp.isValid() ? 1w1 : 1w0))) {
        if (!(1w1 == (hdr.icmp.isValid() ? 1w1 : 1w0))) {} else {
          icmp_check.apply();
        }

      } else {
        udp_check.apply();
      }

    } else {
      tcp_check.apply();
    }

    set_egress.apply();

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
  
