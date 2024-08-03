
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header eth_type_t {
  bit<16> value;
}
header ethernet_t {
  bit<48> srcAddr;
  bit<48> dstAddr;
}
header gtpu_t {
  bit<1> seq_flag;
  bit<1> npdu_flag;
  bit<1> ex_flag;
}
header gtpu_ext_psc_t {
  bit<8> next_ext;
}
header gtpu_options_t {
  bit<8> next_ext;
}
header icmp_t {
  bit<8> type;
  bit<8> code;
}
header inner_icmp_t {
  bit<8> type;
  bit<8> code;
}
header inner_ipv4_t {
  bit<32> srcAddr;
  bit<8> protocol;
  bit<32> dstAddr;
  bit<6> dscp;
}
header inner_tcp_t {
  bit<16> srcPort;
  bit<16> dstPort;
}
header inner_udp_t {
  bit<16> srcPort;
  bit<16> dstPort;
}
header inner_vlan_tag_t {
  bit<16> eth_type;
}
header ipv4_t {
  bit<8> ttl;
  bit<32> srcAddr;
  bit<8> protocol;
  bit<32> dstAddr;
  bit<6> dscp;
}
header mpls_t {
  bit<8> ttl;
  bit<3> tc;
  bit<20> label;
  bit<1> bos;
}
header packet_in_t {
  bit<9> ingress_port;
}
header packet_out_t {
  bit<9> egress_port;
}
header tcp_t {
  bit<16> srcPort;
  bit<16> dstPort;
}
header udp_t {
  bit<16> srcPort;
  bit<16> dstPort;
}
header vlan_tag_t {
  bit<12> vlan_id;
  bit<3> pri;
  bit<16> eth_type;
  bit<1> cfi;
}
// Assemble headers in a single struct
struct my_headers_t {
  eth_type_t eth_type;
  ethernet_t ethernet;
  gtpu_t gtpu;
  gtpu_ext_psc_t gtpu_ext_psc;
  gtpu_options_t gtpu_options;
  icmp_t icmp;
  inner_icmp_t inner_icmp;
  inner_ipv4_t inner_ipv4;
  inner_tcp_t inner_tcp;
  inner_udp_t inner_udp;
  inner_vlan_tag_t inner_vlan_tag;
  ipv4_t ipv4;
  mpls_t mpls;
  packet_in_t packet_in;
  packet_out_t packet_out;
  tcp_t tcp;
  udp_t udp;
  vlan_tag_t vlan_tag;
}

  
// METADATA



struct lkp_t {

  bit<16> l4_sport;
  bit<16> l4_dport;
  bit<1> is_ipv4;
  bit<32> ipv4_src;
  bit<32> ipv4_dst;
  bit<8> ip_proto;
  bit<8> icmp_type;
  bit<8> icmp_code;

}
struct my_metadata_t {
  lkp_t lkp;

  bit<3> vlan_pri;
  bit<12> vlan_id;
  bit<1> vlan_cfi;
  bit<2> tc;
  bit<4> slice_id;
  bit<1> skip_next;
  bit<1> skip_forwarding;
  bit<2> port_type;
  bit<2> packet_color;
  bit<32> next_id;
  bit<8> mpls_ttl;
  bit<20> mpls_label;
  bit<16> l4_sport;
  bit<16> l4_dport;
  bit<1> is_multicast;
  bit<1> is_controller_packet_out;
  bit<32> ipv4_src_addr;
  bit<32> ipv4_dst_addr;
  bit<8> ip_proto;
  bit<16> ip_eth_type;
  bit<3> fwd_type;
  bit<6> dscp;

}
// PARSER

parser MyParser(
  packet_in packet,
  out my_headers_t hdr,
  inout my_metadata_t meta,
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
  bit<8> gtpu_ext_len;
  bit<8> gtpu_msgtype;
  bit<3> gtpu_version;
  bit<6> last_ipv4_dscp;
  bit<16> look_eth;
  bit<4> look_mpls;
  bit<1> look_packet_out;
  bit<16> look_vlan;

  // Parser state machine


  state check_packet_out {

    transition select(look_packet_out){
      (1w0) : parse_packet_out_and_accept;
      default : strip_packet_out;
    }

  }
    

  state parse_eth_type {
    packet.extract(hdr.eth_type);
    transition select(hdr.eth_type.value){
      (16w34887) : parse_mpls;
      (16w2048) : parse_ipv4;
      default : accept;
    }

  }
    

  state parse_eth_type_1 {
    packet.extract(hdr.eth_type);
    transition select(hdr.eth_type.value){
      (16w34887) : reject;
      (16w2048) : parse_ipv4;
      default : accept;
    }

  }
    

  state parse_ethernet {
    meta.vlan_id = 12w4094;
    packet.extract(hdr.ethernet);
    transition select(look_eth){
      (16w34984) : parse_vlan_tag;
      (16w37120) : parse_vlan_tag;
      (16w33024) : parse_vlan_tag;
      default : parse_eth_type;
    }

  }
    

  state parse_ethernet_1 {
    meta.vlan_id = 12w4094;
    packet.extract(hdr.ethernet);
    transition select(look_eth){
      (16w34984) : parse_vlan_tag_1;
      (16w37120) : parse_vlan_tag_1;
      (16w33024) : parse_vlan_tag_1;
      default : parse_eth_type_1;
    }

  }
    

  state parse_gtpu {
    packet.extract(hdr.gtpu);
    transition select(hdr.gtpu.ex_flag,hdr.gtpu.seq_flag,hdr.gtpu.npdu_flag){
      (1w0,1w0,1w0) : parse_inner_ipv4;
      default : parse_gtpu_options;
    }

  }
    

  state parse_gtpu_ext_psc {
    packet.extract(hdr.gtpu_ext_psc);
    transition select(hdr.gtpu_ext_psc.next_ext){
      (8w0) : parse_inner_ipv4;
      default : accept;
    }

  }
    

  state parse_gtpu_options {
    packet.extract(hdr.gtpu_options);
    transition select(hdr.gtpu_options.next_ext,gtpu_ext_len){
      (8w133,8w1) : parse_gtpu_ext_psc;
      default : accept;
    }

  }
    

  state parse_icmp {
    packet.extract(hdr.icmp);
    transition accept;
  }
    

  state parse_inner_icmp {
    packet.extract(hdr.inner_icmp);
    transition accept;
  }
    

  state parse_inner_ipv4 {
    packet.extract(hdr.inner_ipv4);
    last_ipv4_dscp = hdr.inner_ipv4.dscp;
    transition select(hdr.inner_ipv4.protocol){
      (8w6) : parse_inner_tcp;
      (8w17) : parse_inner_udp;
      (8w1) : parse_inner_icmp;
      default : accept;
    }

  }
    

  state parse_inner_tcp {
    packet.extract(hdr.inner_tcp);
    transition accept;
  }
    

  state parse_inner_udp {
    packet.extract(hdr.inner_udp);
    transition accept;
  }
    

  state parse_inner_vlan_tag {
    packet.extract(hdr.inner_vlan_tag);
    hdr.inner_vlan_tag.eth_type = look_vlan;
    transition parse_eth_type;
  }
    

  state parse_inner_vlan_tag_1 {
    packet.extract(hdr.inner_vlan_tag);
    hdr.inner_vlan_tag.eth_type = look_vlan;
    transition parse_eth_type_1;
  }
    

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    meta.ip_proto = hdr.ipv4.protocol;
    meta.ip_eth_type = 16w2048;
    meta.ipv4_src_addr = hdr.ipv4.srcAddr;
    meta.ipv4_dst_addr = hdr.ipv4.dstAddr;
    last_ipv4_dscp = hdr.ipv4.dscp;
    transition select(hdr.ipv4.protocol){
      (8w6) : parse_tcp;
      (8w17) : parse_udp;
      (8w1) : parse_icmp;
      default : accept;
    }

  }
    

  state parse_mpls {
    packet.extract(hdr.mpls);
    meta.mpls_label = hdr.mpls.label;
    meta.mpls_ttl = hdr.mpls.ttl;
    transition select(look_mpls){
      (4w4) : parse_ipv4;
      default : parse_ethernet_1;
    }

  }
    

  state parse_packet_out_and_accept {
    packet.extract(hdr.packet_out);
    transition accept;
  }
    

  state parse_tcp {
    packet.extract(hdr.tcp);
    meta.l4_sport = hdr.tcp.srcPort;
    meta.l4_dport = hdr.tcp.dstPort;
    transition accept;
  }
    

  state parse_udp {
    packet.extract(hdr.udp);
    meta.l4_sport = hdr.udp.srcPort;
    meta.l4_dport = hdr.udp.dstPort;
    transition select(hdr.udp.dstPort,gtpu_version,gtpu_msgtype){
      (16w2152,3w1,8w255) : parse_gtpu;
      default : accept;
    }

  }
    

  state parse_vlan_tag {
    packet.extract(hdr.vlan_tag);
    hdr.vlan_tag.eth_type = look_eth;
    transition select(look_vlan){
      (16w33024) : parse_inner_vlan_tag;
      default : parse_eth_type;
    }

  }
    

  state parse_vlan_tag_1 {
    packet.extract(hdr.vlan_tag);
    hdr.vlan_tag.eth_type = look_eth;
    transition select(look_vlan){
      (16w33024) : parse_inner_vlan_tag_1;
      default : parse_eth_type_1;
    }

  }
    

  state start {
    meta.is_controller_packet_out = 1w0;
    packet.extract(hdr.packet_out);
    last_ipv4_dscp = 6w0;
    transition select(standard_metadata.ingress_port){
      (9w510) : check_packet_out;
      default : parse_ethernet;
    }

  }
    

  state strip_packet_out {

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
  bit<32> clone_id;
  bit<48> dmac;
  bit<1> exitt;
  bit<3> fwd_type;
  bit<16> group_id;
  bit<20> label;
  bit<2> meter_havoc;
  bit<32> next_id;
  bit<9> port_num;
  bit<2> port_type;
  bit<5> qid;
  bit<4> slice_id;
  bit<6> slice_tc;
  bit<48> smac;
  bit<2> tc;
  bit<12> vlan_id;

  // Action Definitions
  action acl_action_0(bit<32> next_id){
    meta.next_id = next_id;
  }

  action acl_action_1(){
    standard_metadata.egress_spec = 9w510;
    meta.skip_next = 1w1;
  }

  action acl_action_2(bit<32> clone_id){

  }

  action acl_action_3(){
    standard_metadata.egress_spec = 9w511;
    meta.skip_next = 1w1;
  }

  action acl_action_4(){

  }

  action bridging_action_0(bit<32> next_id){
    meta.next_id = next_id;
  }

  action bridging_action_1(){

  }

  action classifier_action_0(bit<4> slice_id,bit<2> tc){
    meta.slice_id = slice_id;
    meta.tc = tc;
  }

  action classifier_action_1(){
    meta.slice_id = hdr.ipv4.dscp[5:2];
    meta.tc = hdr.ipv4.dscp[1:0];
  }

  action classifier_action_2(){
    meta.slice_id = 4w0;
    meta.tc = 2w0;
  }

  action fwd_classifier_action_0(bit<3> fwd_type){
    meta.fwd_type = fwd_type;
  }

  action fwd_classifier_action_1(){
    meta.fwd_type = 3w0;
  }

  action hashed_action_0(bit<9> port_num){
    standard_metadata.egress_spec = port_num;
  }

  action hashed_action_1(bit<9> port_num,bit<48> smac,bit<48> dmac){
    hdr.ethernet.srcAddr = smac;
    hdr.ethernet.dstAddr = dmac;
    standard_metadata.egress_spec = port_num;
  }

  action hashed_action_2(){

  }

  action ingress_port_vlan_action_0(){
    meta.skip_forwarding = 1w1;
    meta.skip_next = 1w1;
    meta.port_type = 2w0;
  }

  action ingress_port_vlan_action_1(bit<2> port_type){
    meta.port_type = port_type;
  }

  action ingress_port_vlan_action_2(bit<12> vlan_id,bit<2> port_type){
    meta.vlan_id = vlan_id;
    meta.port_type = port_type;
  }

  action mpls_action_0(bit<32> next_id){
    meta.mpls_label = 20w0;
    meta.next_id = next_id;
  }

  action mpls_action_1(){

  }

  action multicast_action_0(bit<16> group_id){
    standard_metadata.mcast_grp = group_id;
    meta.is_multicast = 1w1;
  }

  action multicast_action_1(){

  }

  action next_mpls_action_0(bit<20> label){
    meta.mpls_label = label;
  }

  action next_mpls_action_1(){

  }

  action next_vlan_action_0(bit<12> vlan_id){
    meta.vlan_id = vlan_id;
  }

  action next_vlan_action_1(){

  }

  action queues_action_0(bit<5> qid){

  }

  action queues_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action queues_action_2(){

  }

  action routing_v4_action_0(bit<32> next_id){
    meta.next_id = next_id;
  }

  action routing_v4_action_1(){

  }

  action routing_v4_action_2(){

  }

  action xconnect_action_0(bit<9> port_num){
    standard_metadata.egress_spec = port_num;
  }

  action xconnect_action_1(bit<32> next_id){
    meta.next_id = next_id;
  }

  action xconnect_action_2(){

  }

  // Table Definitions

  table acl {
    key = {
      standard_metadata.ingress_port : exact;
      hdr.ethernet.dstAddr : exact;
      hdr.ethernet.srcAddr : exact;
      hdr.vlan_tag.vlan_id : ternary;
      hdr.eth_type.value : exact;
      meta.lkp.ipv4_src : exact;
      meta.lkp.ipv4_dst : exact;
      meta.lkp.ip_proto : exact;
      hdr.icmp.type : ternary;
      hdr.icmp.code : ternary;
      meta.lkp.l4_sport : exact;
      meta.lkp.l4_dport : exact;
      meta.port_type : exact;
    }
    actions = {
      acl_action_0;
      acl_action_1;
      acl_action_2;
      acl_action_3;
      acl_action_4;
    }
  }
    
  table bridging {
    key = {
      meta.vlan_id : exact;
      hdr.ethernet.dstAddr : exact;
    }
    actions = {
      bridging_action_0;
      bridging_action_1;
    }
  }
    
  table classifier {
    key = {
      standard_metadata.ingress_port : exact;
      meta.lkp.ipv4_src : exact;
      meta.lkp.ipv4_dst : exact;
      meta.lkp.ip_proto : exact;
      meta.lkp.l4_sport : exact;
      meta.lkp.l4_dport : exact;
    }
    actions = {
      classifier_action_0;
      classifier_action_1;
      classifier_action_2;
    }
  }
    
  table fwd_classifier {
    key = {
      standard_metadata.ingress_port : exact;
      hdr.ethernet.dstAddr : exact;
      hdr.eth_type.value : exact;
      meta.ip_eth_type : exact;
    }
    actions = {
      fwd_classifier_action_0;
      fwd_classifier_action_1;
    }
  }
    
  table hashed {
    key = {
      meta.next_id : exact;
    }
    actions = {
      hashed_action_0;
      hashed_action_1;
      hashed_action_2;
    }
  }
    
  table ingress_port_vlan {
    key = {
      standard_metadata.ingress_port : exact;
      hdr.vlan_tag.isValid() : exact;
      hdr.vlan_tag.vlan_id : ternary;
    }
    actions = {
      ingress_port_vlan_action_0;
      ingress_port_vlan_action_1;
      ingress_port_vlan_action_2;
    }
  }
    
  table mpls {
    key = {
      meta.mpls_label : exact;
    }
    actions = {
      mpls_action_0;
      mpls_action_1;
    }
  }
    
  table multicast {
    key = {
      meta.next_id : exact;
    }
    actions = {
      multicast_action_0;
      multicast_action_1;
    }
  }
    
  table next_mpls {
    key = {
      meta.next_id : exact;
    }
    actions = {
      next_mpls_action_0;
      next_mpls_action_1;
    }
  }
    
  table next_vlan {
    key = {
      meta.next_id : exact;
    }
    actions = {
      next_vlan_action_0;
      next_vlan_action_1;
    }
  }
    
  table queues {
    key = {
      meta.slice_id : exact;
      meta.tc : exact;
      meta.packet_color : exact;
    }
    actions = {
      queues_action_0;
      queues_action_1;
      queues_action_2;
    }
  }
    
  table routing_v4 {
    key = {
      meta.ipv4_dst_addr : exact;
    }
    actions = {
      routing_v4_action_0;
      routing_v4_action_1;
      routing_v4_action_2;
    }
  }
    
  table xconnect {
    key = {
      standard_metadata.ingress_port : exact;
      meta.next_id : exact;
    }
    actions = {
      xconnect_action_0;
      xconnect_action_1;
      xconnect_action_2;
    }
  }
    

  apply {
    // Pipeline
    meta.lkp.is_ipv4 = 1w0;
    meta.lkp.ipv4_src = 32w0;
    meta.lkp.ipv4_dst = 32w0;
    meta.lkp.ip_proto = 8w0;
    meta.lkp.l4_sport = 16w0;
    meta.lkp.l4_dport = 16w0;
    meta.lkp.icmp_type = 8w0;
    meta.lkp.icmp_code = 8w0;
    if (!(1w1 == (hdr.inner_ipv4.isValid() ? 1w1 : 1w0))) {
      if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {} else {
        meta.lkp.is_ipv4 = 1w1;
        meta.lkp.ipv4_src = hdr.ipv4.srcAddr;
        meta.lkp.ipv4_dst = hdr.ipv4.dstAddr;
        meta.lkp.ip_proto = hdr.ipv4.protocol;
        if (!(1w1 == (hdr.tcp.isValid() ? 1w1 : 1w0))) {
          if (!(1w1 == (hdr.udp.isValid() ? 1w1 : 1w0))) {
            if (!(1w1 == (hdr.icmp.isValid() ? 1w1 : 1w0))) {} else {
              meta.lkp.icmp_type = hdr.icmp.type;
              meta.lkp.icmp_code = hdr.icmp.code;
            }

          } else {
            meta.lkp.l4_sport = hdr.udp.srcPort;
            meta.lkp.l4_dport = hdr.udp.dstPort;
          }

        } else {
          meta.lkp.l4_sport = hdr.tcp.srcPort;
          meta.lkp.l4_dport = hdr.tcp.dstPort;
        }

      }

    } else {
      meta.lkp.is_ipv4 = 1w1;
      meta.lkp.ipv4_src = hdr.inner_ipv4.srcAddr;
      meta.lkp.ipv4_dst = hdr.inner_ipv4.dstAddr;
      meta.lkp.ip_proto = hdr.inner_ipv4.protocol;
      if (!(1w1 == (hdr.inner_tcp.isValid() ? 1w1 : 1w0))) {
        if (!(1w1 == (hdr.inner_udp.isValid() ? 1w1 : 1w0))) {
          if (!(1w1 == (hdr.inner_icmp.isValid() ? 1w1 : 1w0))) {} else {
            meta.lkp.icmp_type = hdr.inner_icmp.type;
            meta.lkp.icmp_code = hdr.inner_icmp.code;
          }

        } else {
          meta.lkp.l4_sport = hdr.inner_udp.srcPort;
          meta.lkp.l4_dport = hdr.inner_udp.dstPort;
        }

      } else {
        meta.lkp.l4_sport = hdr.inner_tcp.srcPort;
        meta.lkp.l4_dport = hdr.inner_tcp.dstPort;
      }

    }

    if (!(1w1 == (hdr.packet_out.isValid() ? 1w1 : 1w0))) {} else {
      standard_metadata.egress_spec = hdr.packet_out.egress_port;
      hdr.packet_out.setInvalid();
      meta.is_controller_packet_out = 1w1;
      exitt = 1w1;
    }

    if ((1w1 == exitt)) {} else {
      classifier.apply();
      if (!(1w0 == meta.is_controller_packet_out)) {} else {
        if (!(1w1 == (hdr.vlan_tag.isValid() ? 1w1 : 1w0))) {} else {
          meta.vlan_id = hdr.vlan_tag.vlan_id;
          meta.vlan_pri = hdr.vlan_tag.pri;
          meta.vlan_cfi = hdr.vlan_tag.cfi;
        }

        if (!(1w1 == (hdr.mpls.isValid() ? 1w1 : 1w0))) {} else {
          meta.mpls_ttl = 8w65;
        }

        ingress_port_vlan.apply();
        fwd_classifier.apply();
        if (!(1w0 == meta.skip_forwarding)) {} else {
          if (!(3w0 == meta.fwd_type)) {
            if (!(3w1 == meta.fwd_type)) {
              if (!(3w2 == meta.fwd_type)) {} else {
                routing_v4.apply();
              }

            } else {
              mpls.apply();
            }

          } else {
            bridging.apply();
          }

        }

        if (!(1w0 == meta.skip_next)) {} else {
          next_mpls.apply();
          next_vlan.apply();
        }

        acl.apply();
        if (!(1w0 == meta.skip_next)) {} else {
          xconnect.apply();
          hashed.apply();
          multicast.apply();
        }

        slice_tc = (meta.slice_id ++ meta.tc);
        meta.packet_color = meter_havoc;
        meta.dscp = slice_tc;
        queues.apply();
      }

    }

    exitt = 1w0;
  }
}
  
// EGRESS

control MyEgress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
  bit<1> egress_havoc_bos;
  bit<20> egress_havoc_label;
  bit<3> egress_havoc_tc;
  bit<8> egress_havoc_ttl;
  bit<1> exitt;
  bit<1> push_vlan_havoc_cfi;
  bit<16> push_vlan_havoc_eth_type;
  bit<3> push_vlan_havoc_pri;
  bit<12> push_vlan_havoc_vlan_id;
  bit<2> rewriter_action_run;
  bit<6> tmp_dscp;

  // Action Definitions
  action egress_vlan_action_0(){
    hdr.vlan_tag.setValid();
    hdr.vlan_tag.cfi = push_vlan_havoc_cfi;
    hdr.vlan_tag.pri = push_vlan_havoc_pri;
    hdr.vlan_tag.eth_type = push_vlan_havoc_eth_type;
    hdr.vlan_tag.vlan_id = push_vlan_havoc_vlan_id;
    hdr.vlan_tag.cfi = meta.vlan_cfi;
    hdr.vlan_tag.pri = meta.vlan_pri;
    hdr.vlan_tag.eth_type = 16w33024;
    hdr.vlan_tag.vlan_id = meta.vlan_id;
  }

  action egress_vlan_action_1(){
    hdr.vlan_tag.setInvalid();
  }

  action egress_vlan_action_2(){
    standard_metadata.egress_spec = 9w511;
  }

  action rewriter_action_0(){
    rewriter_action_run = 2w0;
  }

  action rewriter_action_1(){
    rewriter_action_run = 2w1;
    tmp_dscp = 6w0;
  }

  action rewriter_action_2(){
    rewriter_action_run = 2w2;
  }

  // Table Definitions

  table egress_vlan {
    key = {
      meta.vlan_id : exact;
      standard_metadata.egress_port : exact;
    }
    actions = {
      egress_vlan_action_0;
      egress_vlan_action_1;
      egress_vlan_action_2;
    }
  }
    
  table rewriter {
    key = {
      standard_metadata.egress_port : exact;
    }
    actions = {
      rewriter_action_0;
      rewriter_action_1;
      rewriter_action_2;
    }
  }
    

  apply {
    // Pipeline
    if (!(1w1 == meta.is_controller_packet_out)) {} else {
      exitt = 1w1;
    }

    if ((1w1 == exitt)) {} else {
      if (!(9w510 == standard_metadata.egress_port)) {} else {
        hdr.packet_in.setValid();
        hdr.packet_in.ingress_port = standard_metadata.ingress_port;
        exitt = 1w1;
      }

    }

    exitt = 1w0;
    if ((1w1 == exitt)) {} else {
      if (!(1w0 == meta.is_controller_packet_out)) {} else {
        if (!((1w1 == meta.is_multicast) && (standard_metadata.egress_port == standard_metadata.ingress_port))) {} else {
          standard_metadata.egress_spec = 9w511;
        }

        if (!(20w0 == meta.mpls_label)) {
          hdr.mpls.setValid();
          hdr.mpls.label = egress_havoc_label;
          hdr.mpls.tc = egress_havoc_tc;
          hdr.mpls.bos = egress_havoc_bos;
          hdr.mpls.ttl = egress_havoc_ttl;
          hdr.mpls.label = meta.mpls_label;
          hdr.mpls.tc = 3w0;
          hdr.mpls.bos = 1w1;
          hdr.mpls.ttl = meta.mpls_ttl;
          hdr.eth_type.value = 16w34887;
        } else {
          if (!(1w1 == (hdr.mpls.isValid() ? 1w1 : 1w0))) {} else {
            hdr.mpls.setInvalid();
            hdr.eth_type.value = meta.ip_eth_type;
          }

        }

        egress_vlan.apply();
        if (!(1w1 == (hdr.mpls.isValid() ? 1w1 : 1w0))) {
          if (!((1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0)) && !(3w0 == meta.fwd_type))) {} else {
            hdr.ipv4.ttl = (hdr.ipv4.ttl - 8w1);
            if (!(8w0 == hdr.ipv4.ttl)) {} else {
              standard_metadata.egress_spec = 9w511;
            }

          }

        } else {
          hdr.mpls.ttl = (hdr.mpls.ttl - 8w1);
          if (!(8w0 == hdr.mpls.ttl)) {} else {
            standard_metadata.egress_spec = 9w511;
          }

        }

        tmp_dscp = meta.dscp;
        rewriter_action_run = 2w3;
        rewriter.apply();
        if (!(2w0 == rewriter_action_run)) {
          if (!(2w1 == rewriter_action_run)) {} else {
            if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {} else {
              hdr.inner_ipv4.dscp = tmp_dscp;
            }

          }

        } else {
          if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {} else {
            hdr.inner_ipv4.dscp = tmp_dscp;
          }

        }

      }

    }

    exitt = 1w0;
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
  
