
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
  bit<32> srcAddr;
  bit<8> protocol;
  bit<32> dstAddr;
}
header nc_hdr_t {
  bit<16> vgroup;
  bit<128> value;
  bit<16> seq;
  bit<8> sc;
  bit<8> op;
  bit<128> key;
}
header overlay_0__t {
  bit<32> swip;
}
header overlay_1__t {
  bit<32> swip;
}
header overlay_2__t {
  bit<32> swip;
}
header overlay_3__t {
  bit<32> swip;
}
header overlay_4__t {
  bit<32> swip;
}
header overlay_5__t {
  bit<32> swip;
}
header overlay_6__t {
  bit<32> swip;
}
header overlay_7__t {
  bit<32> swip;
}
header overlay_8__t {
  bit<32> swip;
}
header tcp_t {

}
header udp_t {
  bit<16> length;
  bit<16> dstPort;
}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  nc_hdr_t nc_hdr;
  overlay_0__t overlay_0_;
  overlay_1__t overlay_1_;
  overlay_2__t overlay_2_;
  overlay_3__t overlay_3_;
  overlay_4__t overlay_4_;
  overlay_5__t overlay_5_;
  overlay_6__t overlay_6_;
  overlay_7__t overlay_7_;
  overlay_8__t overlay_8_;
  tcp_t tcp;
  udp_t udp;
}

  
// METADATA



struct location_t {

  bit<16> index;

}

struct my_md_t {

  bit<16> role;
  bit<32> ipaddress;

}

struct reply_to_client_md_t {

  bit<32> ipv4_srcAddr;
  bit<32> ipv4_dstAddr;

}

struct sequence_md_t {

  bit<16> seq;

}
struct my_metadata_t {
  location_t location;
  my_md_t my_md;
  reply_to_client_md_t reply_to_client_md;
  sequence_md_t sequence_md;


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
      (8w17) : parse_udp;
      default : accept;
    }

  }
    

  state parse_nc_header {
    packet.extract(hdr.nc_hdr);
    transition accept;
  }
    

  state parse_overlay_0 {
    packet.extract(hdr.overlay_0_);
    transition select(hdr.overlay_0_.swip){
      (32w0) : parse_nc_header;
      default : parse_overlay_1;
    }

  }
    

  state parse_overlay_1 {
    packet.extract(hdr.overlay_1_);
    transition select(hdr.overlay_1_.swip){
      (32w0) : parse_nc_header;
      default : parse_overlay_2;
    }

  }
    

  state parse_overlay_2 {
    packet.extract(hdr.overlay_2_);
    transition select(hdr.overlay_2_.swip){
      (32w0) : parse_nc_header;
      default : parse_overlay_3;
    }

  }
    

  state parse_overlay_3 {
    packet.extract(hdr.overlay_3_);
    transition select(hdr.overlay_3_.swip){
      (32w0) : parse_nc_header;
      default : parse_overlay_4;
    }

  }
    

  state parse_overlay_4 {
    packet.extract(hdr.overlay_4_);
    transition select(hdr.overlay_4_.swip){
      (32w0) : parse_nc_header;
      default : parse_overlay_5;
    }

  }
    

  state parse_overlay_5 {
    packet.extract(hdr.overlay_5_);
    transition select(hdr.overlay_5_.swip){
      (32w0) : parse_nc_header;
      default : parse_overlay_6;
    }

  }
    

  state parse_overlay_6 {
    packet.extract(hdr.overlay_6_);
    transition select(hdr.overlay_6_.swip){
      (32w0) : parse_nc_header;
      default : parse_overlay_7;
    }

  }
    

  state parse_overlay_7 {
    packet.extract(hdr.overlay_7_);
    hdr.overlay_7_.swip = 32w0;
    transition accept;
  }
    

  state parse_tcp {
    packet.extract(hdr.tcp);
    transition accept;
  }
    

  state parse_udp {
    packet.extract(hdr.udp);
    transition select(hdr.udp.dstPort){
      (16w8888) : parse_overlay_0;
      (16w8889) : parse_overlay_0;
      default : accept;
    }

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
  bit<16> DEVNULL_sequence_reg_assign_value_act_index;
  bit<16> DEVNULL_sequence_reg_assign_value_act_value;
  bit<16> DEVNULL_sequence_reg_get_sequence_act;
  bit<16> DEVNULL_sequence_reg_maintain_sequence_act;
  bit<16> DEVNULL_sequence_reg_maintain_sequence_act_index;
  bit<16> DEVNULL_sequence_reg_maintain_sequence_act_value;
  bit<16> DEVNULL_value_reg_assign_value_act_index;
  bit<128> DEVNULL_value_reg_assign_value_act_value;
  bit<16> DEVNULL_value_reg_read_value_act;
  bit<1> did_pop_front;
  bit<9> egress_spec;
  bit<32> havoc_pop_chain_1;
  bit<32> havoc_pop_chain_2;
  bit<32> havoc_pop_chain_3;
  bit<32> havoc_pop_chain_4;
  bit<32> havoc_pop_chain_5;
  bit<32> havoc_pop_chain_6;
  bit<32> havoc_pop_chain_7;
  bit<32> havoc_pop_chain_8;
  bit<32> havoc_pop_chain_9;
  bit<16> index;
  bit<32> nexthop;
  bit<16> sequence_reg_get_sequence_act;
  bit<16> sequence_reg_maintain_sequence_act;
  bit<32> sw_ip;
  bit<16> sw_role;
  bit<128> value_reg_read_value_act;

  // Action Definitions
  action assign_value_action_0(){
    DEVNULL_sequence_reg_assign_value_act_index = meta.location.index;
    DEVNULL_sequence_reg_assign_value_act_value = hdr.nc_hdr.seq;
    DEVNULL_value_reg_assign_value_act_index = meta.location.index;
    DEVNULL_value_reg_assign_value_act_value = hdr.nc_hdr.value;
  }

  action assign_value_action_1(){

  }

  action drop_packet_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action drop_packet_action_1(){

  }

  action failure_recovery_action_0(){
    hdr.ipv4.dstAddr = hdr.overlay_1_.swip;
    hdr.nc_hdr.sc = (hdr.nc_hdr.sc + 8w255);
    did_pop_front = 1w1;
    hdr.udp.length = (hdr.udp.length + 16w65532);
    hdr.ipv4.totalLen = (hdr.ipv4.totalLen + 16w65532);
  }

  action failure_recovery_action_1(){
    meta.reply_to_client_md.ipv4_srcAddr = hdr.ipv4.dstAddr;
    meta.reply_to_client_md.ipv4_dstAddr = hdr.ipv4.srcAddr;
    hdr.ipv4.srcAddr = meta.reply_to_client_md.ipv4_srcAddr;
    hdr.ipv4.dstAddr = meta.reply_to_client_md.ipv4_dstAddr;
    hdr.nc_hdr.op = 8w13;
    hdr.udp.dstPort = 16w8889;
  }

  action failure_recovery_action_2(bit<32> nexthop){
    hdr.overlay_0_.swip = nexthop;
    hdr.ipv4.dstAddr = nexthop;
  }

  action failure_recovery_action_3(){

  }

  action failure_recovery_action_4(){
    standard_metadata.egress_spec = 9w511;
  }

  action find_index_action_0(bit<16> index){
    meta.location.index = index;
  }

  action find_index_action_1(){

  }

  action get_my_address_action_0(bit<32> sw_ip,bit<16> sw_role){
    meta.my_md.ipaddress = sw_ip;
    meta.my_md.role = sw_role;
  }

  action get_my_address_action_1(){

  }

  action get_sequence_action_0(){
    DEVNULL_sequence_reg_get_sequence_act = meta.location.index;
    meta.sequence_md.seq = sequence_reg_get_sequence_act;
  }

  action get_sequence_action_1(){

  }

  action ipv4_route_action_0(bit<9> egress_spec){
    standard_metadata.egress_spec = egress_spec;
    hdr.ipv4.ttl = (hdr.ipv4.ttl + 8w255);
  }

  action ipv4_route_action_1(){

  }

  action maintain_sequence_action_0(){
    meta.sequence_md.seq = (meta.sequence_md.seq + 16w1);
    DEVNULL_sequence_reg_maintain_sequence_act_index = meta.location.index;
    DEVNULL_sequence_reg_maintain_sequence_act_value = meta.sequence_md.seq;
    DEVNULL_sequence_reg_maintain_sequence_act = meta.location.index;
    hdr.nc_hdr.seq = sequence_reg_maintain_sequence_act;
  }

  action maintain_sequence_action_1(){

  }

  action pop_chain_action_0(){
    hdr.nc_hdr.sc = (hdr.nc_hdr.sc + 8w255);
    did_pop_front = 1w1;
    hdr.udp.length = (hdr.udp.length + 16w65532);
    hdr.ipv4.totalLen = (hdr.ipv4.totalLen + 16w65532);
  }

  action pop_chain_action_1(){

  }

  action read_value_action_0(){
    DEVNULL_value_reg_read_value_act = meta.location.index;
    hdr.nc_hdr.value = value_reg_read_value_act;
  }

  action read_value_action_1(){

  }

  // Table Definitions

  table assign_value {
    key = {
    }
    actions = {
      assign_value_action_0;
      assign_value_action_1;
    }
  }
    
  table drop_packet {
    key = {
    }
    actions = {
      drop_packet_action_0;
      drop_packet_action_1;
    }
  }
    
  table failure_recovery {
    key = {
      hdr.ipv4.dstAddr : ternary;
      hdr.overlay_1_.swip : ternary;
      hdr.nc_hdr.vgroup : ternary;
    }
    actions = {
      failure_recovery_action_0;
      failure_recovery_action_1;
      failure_recovery_action_2;
      failure_recovery_action_3;
      failure_recovery_action_4;
    }
  }
    
  table find_index {
    key = {
      hdr.nc_hdr.key : exact;
    }
    actions = {
      find_index_action_0;
      find_index_action_1;
    }
  }
    
  table get_my_address {
    key = {
      hdr.nc_hdr.op : exact;
    }
    actions = {
      get_my_address_action_0;
      get_my_address_action_1;
    }
  }
    
  table get_sequence {
    key = {
    }
    actions = {
      get_sequence_action_0;
      get_sequence_action_1;
    }
  }
    
  table ipv4_route {
    key = {
      hdr.ipv4.dstAddr : exact;
    }
    actions = {
      ipv4_route_action_0;
      ipv4_route_action_1;
    }
  }
    
  table maintain_sequence {
    key = {
    }
    actions = {
      maintain_sequence_action_0;
      maintain_sequence_action_1;
    }
  }
    
  table pop_chain {
    key = {
    }
    actions = {
      pop_chain_action_0;
      pop_chain_action_1;
    }
  }
    
  table read_value {
    key = {
    }
    actions = {
      read_value_action_0;
      read_value_action_1;
    }
  }
    

  apply {
    // Pipeline
    if (!((hdr.nc_hdr.isValid() ? 1w1 : 1w0) == 1w1)) {} else {
      get_my_address.apply();
      if (!(hdr.ipv4.dstAddr == meta.my_md.ipaddress)) {} else {
        find_index.apply();
        get_sequence.apply();
        if (!(hdr.nc_hdr.op == 8w10)) {
          if (!(hdr.nc_hdr.op == 8w12)) {} else {
            if (!(meta.my_md.role == 16w100)) {} else {
              maintain_sequence.apply();
            }

            if (!((meta.my_md.role == 16w10051) || (hdr.nc_hdr.seq > meta.sequence_md.seq))) {
              drop_packet.apply();
            } else {
              assign_value.apply();
              did_pop_front = 1w0;
              pop_chain.apply();
              if (!(1w1 == did_pop_front)) {} else {
                hdr.overlay_0_ = hdr.overlay_1_;
                if (!(1w1 == (hdr.overlay_1_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_0_.swip = havoc_pop_chain_1;
                } else {
                  hdr.overlay_0_.swip = hdr.overlay_1_.swip;
                }

                hdr.overlay_1_ = hdr.overlay_2_;
                if (!(1w1 == (hdr.overlay_2_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_1_.swip = havoc_pop_chain_2;
                } else {
                  hdr.overlay_1_.swip = hdr.overlay_2_.swip;
                }

                hdr.overlay_2_ = hdr.overlay_3_;
                if (!(1w1 == (hdr.overlay_3_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_2_.swip = havoc_pop_chain_3;
                } else {
                  hdr.overlay_2_.swip = hdr.overlay_3_.swip;
                }

                hdr.overlay_3_ = hdr.overlay_4_;
                if (!(1w1 == (hdr.overlay_4_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_3_.swip = havoc_pop_chain_4;
                } else {
                  hdr.overlay_3_.swip = hdr.overlay_4_.swip;
                }

                hdr.overlay_4_ = hdr.overlay_5_;
                if (!(1w1 == (hdr.overlay_5_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_4_.swip = havoc_pop_chain_5;
                } else {
                  hdr.overlay_4_.swip = hdr.overlay_5_.swip;
                }

                hdr.overlay_5_ = hdr.overlay_6_;
                if (!(1w1 == (hdr.overlay_6_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_5_.swip = havoc_pop_chain_6;
                } else {
                  hdr.overlay_5_.swip = hdr.overlay_6_.swip;
                }

                hdr.overlay_6_ = hdr.overlay_7_;
                if (!(1w1 == (hdr.overlay_7_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_6_.swip = havoc_pop_chain_7;
                } else {
                  hdr.overlay_6_.swip = hdr.overlay_7_.swip;
                }

                hdr.overlay_7_ = hdr.overlay_8_;
                if (!(1w1 == (hdr.overlay_8_.isValid() ? 1w1 : 1w0))) {
                  hdr.overlay_7_.swip = havoc_pop_chain_8;
                } else {
                  hdr.overlay_7_.swip = hdr.overlay_8_.swip;
                }

                hdr.overlay_8_.setInvalid();
                hdr.overlay_8_.swip = havoc_pop_chain_9;
              }

            }

          }

        } else {
          read_value.apply();
        }

      }

    }

    if (!((hdr.nc_hdr.isValid() ? 1w1 : 1w0) == 1w1)) {} else {
      failure_recovery.apply();
    }

    if (!(((hdr.tcp.isValid() ? 1w1 : 1w0) == 1w1) || ((hdr.udp.isValid() ? 1w1 : 1w0) == 1w1))) {} else {
      ipv4_route.apply();
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
  bit<48> dmac;
  bit<48> smac;

  // Action Definitions
  action ethernet_set_mac_action_0(bit<48> smac,bit<48> dmac){
    hdr.ethernet.srcAddr = smac;
    hdr.ethernet.dstAddr = dmac;
  }

  action ethernet_set_mac_action_1(){

  }

  // Table Definitions

  table ethernet_set_mac {
    key = {
      standard_metadata.egress_spec : exact;
    }
    actions = {
      ethernet_set_mac_action_0;
      ethernet_set_mac_action_1;
    }
  }
    

  apply {
    // Pipeline
    ethernet_set_mac.apply();
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
  
