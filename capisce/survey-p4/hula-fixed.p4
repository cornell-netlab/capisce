
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header ethernet_t {
  bit<48> srcAddr;
  bit<16> etherType;
  bit<48> dstAddr;
}
header hula_t {
  bit<15> qdepth;
  bit<1> dir;
  bit<32> digest;
}
header ipv4_t {
  bit<8> ttl;
  bit<32> srcAddr;
  bit<8> protocol;
  bit<32> dstAddr;
}
header srcRoute_0__t {
  bit<15> port;
  bit<1> bos;
}
header srcRoute_1__t {
  bit<1> bos;
}
header srcRoute_2__t {
  bit<1> bos;
}
header srcRoute_3__t {
  bit<1> bos;
}
header srcRoute_4__t {
  bit<1> bos;
}
header srcRoute_5__t {
  bit<1> bos;
}
header srcRoute_6__t {
  bit<1> bos;
}
header srcRoute_7__t {
  bit<1> bos;
}
header udp_t {
  bit<16> srcPort;
}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  hula_t hula;
  ipv4_t ipv4;
  srcRoute_0__t srcRoute_0_;
  srcRoute_1__t srcRoute_1_;
  srcRoute_2__t srcRoute_2_;
  srcRoute_3__t srcRoute_3_;
  srcRoute_4__t srcRoute_4_;
  srcRoute_5__t srcRoute_5_;
  srcRoute_6__t srcRoute_6_;
  srcRoute_7__t srcRoute_7_;
  udp_t udp;
}

  
// METADATA


struct my_metadata_t {

  bit<32> index;

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
      (16w9029) : parse_hula;
      default : accept;
    }

  }
    

  state parse_hula {
    packet.extract(hdr.hula);
    transition parse_srcRouting__0;
  }
    

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    transition select(hdr.ipv4.protocol){
      (8w17) : parse_udp;
      default : accept;
    }

  }
    

  state parse_srcRouting__0 {
    packet.extract(hdr.srcRoute_0_);
    hdr.srcRoute_7_.bos = 1w1;
    transition select(hdr.srcRoute_0_.bos){
      (1w1) : parse_ipv4;
      default : parse_srcRouting__1;
    }

  }
    

  state parse_srcRouting__1 {
    packet.extract(hdr.srcRoute_1_);
    hdr.srcRoute_7_.bos = 1w1;
    transition select(hdr.srcRoute_1_.bos){
      (1w1) : parse_ipv4;
      default : parse_srcRouting__2;
    }

  }
    

  state parse_srcRouting__2 {
    packet.extract(hdr.srcRoute_2_);
    hdr.srcRoute_7_.bos = 1w1;
    transition select(hdr.srcRoute_2_.bos){
      (1w1) : parse_ipv4;
      default : parse_srcRouting__3;
    }

  }
    

  state parse_srcRouting__3 {
    packet.extract(hdr.srcRoute_3_);
    hdr.srcRoute_7_.bos = 1w1;
    transition select(hdr.srcRoute_3_.bos){
      (1w1) : parse_ipv4;
      default : parse_srcRouting__4;
    }

  }
    

  state parse_srcRouting__4 {
    packet.extract(hdr.srcRoute_4_);
    hdr.srcRoute_7_.bos = 1w1;
    transition select(hdr.srcRoute_4_.bos){
      (1w1) : parse_ipv4;
      default : parse_srcRouting__5;
    }

  }
    

  state parse_srcRouting__5 {
    packet.extract(hdr.srcRoute_5_);
    hdr.srcRoute_7_.bos = 1w1;
    transition select(hdr.srcRoute_5_.bos){
      (1w1) : parse_ipv4;
      default : parse_srcRouting__6;
    }

  }
    

  state parse_srcRouting__6 {
    packet.extract(hdr.srcRoute_6_);
    hdr.srcRoute_7_.bos = 1w1;
    transition select(hdr.srcRoute_6_.bos){
      (1w1) : parse_ipv4;
      default : parse_srcRouting__7;
    }

  }
    

  state parse_srcRouting__7 {
    packet.extract(hdr.srcRoute_7_);
    hdr.srcRoute_7_.bos = 1w1;
    transition parse_ipv4;
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
  bit<32> DEVNULL_dstindec_nhop_reg_hula_set_nhop_index;
  bit<9> DEVNULL_dstindec_nhop_reg_hula_set_nhop_value;
  bit<32> DEVNULL_dstindex_nhop_reg_hula_get_nhop;
  bit<16> DEVNULL_flow_port_reg_ingress_index;
  bit<9> DEVNULL_flow_port_reg_ingress_value;
  bit<32> DEVNULL_srcindex_digest_reg_change_best_path_at_dst;
  bit<15> DEVNULL_srcindex_qdepth_reg_change_best_path_at_dst;
  bit<32> DEVNULL_srcindex_qdepth_reg_ingress;
  bit<32> DEVNULL_srcindex_qdepth_reg_ingress1;
  bit<32> DEVNULL_srcindex_qdepth_reg_ingress_index;
  bit<15> DEVNULL_srcindex_qdepth_reg_ingress_value;
  bit<1> _symb$hula_fwd$action;
  bit<48> dstAddr;
  bit<16> dstindex_nhop_reg_hula_get_nhop;
  bit<16> flow_hash;
  bit<16> flow_hash_ingress_hash_crc16_flow_hash;
  bit<32> flow_hash_ingress_hash_crc16_flow_hash_0;
  bit<32> flow_hash_ingress_hash_crc16_flow_hash_1;
  bit<16> flow_hash_ingress_hash_crc16_flow_hash_2;
  bit<32> index;
  bit<32> old_digest;
  bit<15> old_qdepth;
  bit<16> port;
  bit<32> srcindex_digest_reg_change_best_path_at_dst;
  bit<32> srcindex_qdepth_reg_change_best_path_at_dst;
  bit<15> srcindex_qdepth_reg_ingress;
  bit<32> srcindex_qdepth_reg_ingress1;
  bit<16> tmp;

  // Action Definitions
  action dmac_action_0(bit<48> dstAddr){
    hdr.ethernet.srcAddr = hdr.ethernet.dstAddr;
    hdr.ethernet.dstAddr = dstAddr;
  }

  action dmac_action_1(){

  }

  action hula_bwd_action_0(bit<32> index){
    DEVNULL_dstindec_nhop_reg_hula_set_nhop_index = index;
    DEVNULL_dstindec_nhop_reg_hula_set_nhop_value = standard_metadata.ingress_port;
  }

  action hula_bwd_action_1(){

  }

  action hula_fwd_action_0(bit<32> index){
    meta.index = index;
  }

  action hula_fwd_action_1(){
    standard_metadata.egress_spec = hdr.srcRoute_0_.port[8:0];
    hdr.srcRoute_0_ = hdr.srcRoute_1_;
    hdr.srcRoute_1_ = hdr.srcRoute_2_;
    hdr.srcRoute_2_ = hdr.srcRoute_3_;
    hdr.srcRoute_3_ = hdr.srcRoute_4_;
    hdr.srcRoute_4_ = hdr.srcRoute_5_;
    hdr.srcRoute_5_ = hdr.srcRoute_6_;
    hdr.srcRoute_6_ = hdr.srcRoute_7_;
    hdr.srcRoute_7_.setInvalid();
  }

  action hula_nhop_action_0(bit<32> index){
    DEVNULL_dstindex_nhop_reg_hula_get_nhop = index;
    tmp = dstindex_nhop_reg_hula_get_nhop;
    standard_metadata.egress_spec = tmp[8:0];
  }

  action hula_nhop_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action hula_src_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action hula_src_action_1(){
    standard_metadata.egress_spec = hdr.srcRoute_0_.port[8:0];
    hdr.srcRoute_0_ = hdr.srcRoute_1_;
    hdr.srcRoute_1_ = hdr.srcRoute_2_;
    hdr.srcRoute_2_ = hdr.srcRoute_3_;
    hdr.srcRoute_3_ = hdr.srcRoute_4_;
    hdr.srcRoute_4_ = hdr.srcRoute_5_;
    hdr.srcRoute_5_ = hdr.srcRoute_6_;
    hdr.srcRoute_6_ = hdr.srcRoute_7_;
    hdr.srcRoute_7_.setInvalid();
  }

  // Table Definitions

  table dmac {
    key = {
      standard_metadata.egress_spec : exact;
    }
    actions = {
      dmac_action_0;
      dmac_action_1;
    }
  }
    
  table hula_bwd {
    key = {
      hdr.ipv4.dstAddr : ternary;
    }
    actions = {
      hula_bwd_action_0;
      hula_bwd_action_1;
    }
  }
    
  table hula_fwd {
    key = {
      hdr.ipv4.dstAddr : exact;
      hdr.ipv4.srcAddr : exact;
    }
    actions = {
      hula_fwd_action_0;
      hula_fwd_action_1;
    }
  }
    
  table hula_nhop {
    key = {
      hdr.ipv4.dstAddr : ternary;
    }
    actions = {
      hula_nhop_action_0;
      hula_nhop_action_1;
    }
  }
    
  table hula_src {
    key = {
      hdr.ipv4.srcAddr : exact;
    }
    actions = {
      hula_src_action_0;
      hula_src_action_1;
    }
  }
    

  apply {
    // Pipeline
    if (!(1w1 == (hdr.hula.isValid() ? 1w1 : 1w0))) {
      if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {
        standard_metadata.egress_spec = 9w511;
      } else {
        flow_hash_ingress_hash_crc16_flow_hash_0 = hdr.ipv4.srcAddr;
        flow_hash_ingress_hash_crc16_flow_hash_1 = hdr.ipv4.dstAddr;
        flow_hash_ingress_hash_crc16_flow_hash_2 = hdr.udp.srcPort;


        flow_hash = flow_hash_ingress_hash_crc16_flow_hash;
        if (!(port == 16w0)) {
          standard_metadata.egress_spec = port[8:0];
        } else {
          hula_nhop.apply();
          DEVNULL_flow_port_reg_ingress_index = flow_hash;
          DEVNULL_flow_port_reg_ingress_value = standard_metadata.egress_spec;
        }

        dmac.apply();
      }

    } else {
      if (!(1w0 == hdr.hula.dir)) {
        hula_bwd.apply();
        hula_src.apply();
      } else {
        hula_fwd.apply();
        if (!(1w0 == _symb$hula_fwd$action)) {} else {
          DEVNULL_srcindex_qdepth_reg_ingress = meta.index;
          old_qdepth = srcindex_qdepth_reg_ingress;
          if (!(old_qdepth > hdr.hula.qdepth)) {
            DEVNULL_srcindex_qdepth_reg_ingress1 = meta.index;
            old_digest = srcindex_qdepth_reg_ingress1;
            if (!(old_digest == hdr.hula.digest)) {} else {
              DEVNULL_srcindex_qdepth_reg_ingress_index = meta.index;
              DEVNULL_srcindex_qdepth_reg_ingress_value = hdr.hula.qdepth;
            }

            standard_metadata.egress_spec = 9w511;
          } else {
            DEVNULL_srcindex_qdepth_reg_change_best_path_at_dst = hdr.hula.qdepth;
            meta.index = srcindex_qdepth_reg_change_best_path_at_dst;
            DEVNULL_srcindex_digest_reg_change_best_path_at_dst = hdr.hula.digest;
            meta.index = srcindex_digest_reg_change_best_path_at_dst;
            hdr.hula.dir = 1w1;
            standard_metadata.egress_spec = standard_metadata.ingress_port;
          }

        }

      }

    }

    if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {} else {
      hdr.ipv4.ttl = (hdr.ipv4.ttl - 8w1);
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

  // Action Definitions

  // Table Definitions


  apply {
    // Pipeline
    if (!(1w1 == (hdr.hula.isValid() ? 1w1 : 1w0))) {} else {
      if (!(1w0 == hdr.hula.dir)) {} else {
        if (!(hdr.hula.qdepth < standard_metadata.deq_qdepth[14:0])) {} else {
          hdr.hula.qdepth = standard_metadata.deq_qdepth[14:0];
        }

      }

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
  
