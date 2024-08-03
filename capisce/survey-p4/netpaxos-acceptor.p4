
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header ethernet_t {
  bit<16> etherType;
}
header ipv4_t {
  bit<8> protocol;
}
header paxos_t {
  bit<16> vproposal;
  bit<32> val;
  bit<16> proposal;
  bit<16> msgtype;
  bit<32> inst;
  bit<16> acpt;
}
header udp_t {
  bit<16> dstPort;
  bit<16> checksum;
}
// Assemble headers in a single struct
struct my_headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  paxos_t paxos;
  udp_t udp;
}

  
// METADATA



struct local_metadata_t {

  bit<16> proposal;

}
struct my_metadata_t {
  local_metadata_t local_metadata;


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
    

  state parse_paxos {
    packet.extract(hdr.paxos);
    transition accept;
  }
    

  state parse_udp {
    packet.extract(hdr.udp);
    transition select(hdr.udp.dstPort){
      (16w34952) : parse_paxos;
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
  bit<32> DEVNULL_acceptor_id;
  bit<32> DEVNULL_acceptor_id_1a;
  bit<32> DEVNULL_proposal_register_1a_index;
  bit<16> DEVNULL_proposal_register_1a_value;
  bit<32> DEVNULL_proposal_register_2a_index;
  bit<16> DEVNULL_proposal_register_2a_value;
  bit<32> DEVNULL_proposal_register_read_round;
  bit<32> DEVNULL_val_register_1a;
  bit<32> DEVNULL_val_register_index;
  bit<32> DEVNULL_val_register_value;
  bit<32> DEVNULL_vproposal_register_1a;
  bit<32> DEVNULL_vproposal_register_2a_index;
  bit<16> DEVNULL_vproposal_register_2a_value;
  bit<16> acceptor_id;
  bit<16> acceptor_id_1a;
  bit<9> port;
  bit<16> proposal_register_read_round;
  bit<32> val_register_1a;
  bit<16> vproposal_register_1a;

  // Action Definitions
  action drop_tbl_action_0(){
    standard_metadata.egress_spec = 9w511;
  }

  action drop_tbl_action_1(){

  }

  action fwd_tbl_action_0(bit<9> port){
    standard_metadata.egress_spec = port;
  }

  action fwd_tbl_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action fwd_tbl_action_2(){

  }

  action paxos_tbl_action_0(){
    DEVNULL_proposal_register_1a_index = hdr.paxos.inst;
    DEVNULL_proposal_register_1a_value = hdr.paxos.proposal;
    DEVNULL_vproposal_register_1a = hdr.paxos.inst;
    hdr.paxos.vproposal = vproposal_register_1a;
    DEVNULL_val_register_1a = hdr.paxos.inst;
    hdr.paxos.val = val_register_1a;
    DEVNULL_acceptor_id_1a = 32w0;
    hdr.paxos.acpt = acceptor_id_1a;
    hdr.udp.checksum = 16w0;
  }

  action paxos_tbl_action_1(){
    DEVNULL_proposal_register_2a_index = hdr.paxos.inst;
    DEVNULL_proposal_register_2a_value = hdr.paxos.proposal;
    DEVNULL_vproposal_register_2a_index = hdr.paxos.inst;
    DEVNULL_vproposal_register_2a_value = hdr.paxos.proposal;
    DEVNULL_val_register_index = hdr.paxos.inst;
    DEVNULL_val_register_value = hdr.paxos.val;
    hdr.paxos.msgtype = 16w4;
    hdr.paxos.vproposal = hdr.paxos.proposal;
    DEVNULL_acceptor_id = 32w0;
    hdr.paxos.acpt = acceptor_id;
    hdr.udp.checksum = 16w0;
  }

  action paxos_tbl_action_2(){

  }

  action round_tbl_action_0(){
    DEVNULL_proposal_register_read_round = hdr.paxos.inst;
    meta.local_metadata.proposal = proposal_register_read_round;
  }

  action round_tbl_action_1(){

  }

  // Table Definitions

  table drop_tbl {
    key = {
    }
    actions = {
      drop_tbl_action_0;
      drop_tbl_action_1;
    }
  }
    
  table fwd_tbl {
    key = {
      standard_metadata.ingress_port : exact;
    }
    actions = {
      fwd_tbl_action_0;
      fwd_tbl_action_1;
      fwd_tbl_action_2;
    }
  }
    
  table paxos_tbl {
    key = {
      hdr.paxos.msgtype : exact;
    }
    actions = {
      paxos_tbl_action_0;
      paxos_tbl_action_1;
      paxos_tbl_action_2;
    }
  }
    
  table round_tbl {
    key = {
    }
    actions = {
      round_tbl_action_0;
      round_tbl_action_1;
    }
  }
    

  apply {
    // Pipeline
    if (!((hdr.ipv4.isValid() ? 1w1 : 1w0) == 1w1)) {
      if (!((hdr.paxos.isValid() ? 1w1 : 1w0) == 1w1)) {
        standard_metadata.egress_spec = 9w511;
      } else {
        round_tbl.apply();
        if (!(meta.local_metadata.proposal <= hdr.paxos.proposal)) {
          drop_tbl.apply();
        } else {
          paxos_tbl.apply();
        }

      }

    } else {
      fwd_tbl.apply();
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
  
