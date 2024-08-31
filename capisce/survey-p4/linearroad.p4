
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header accident_alert_t {
  bit<32> vid;
  bit<16> time;
  bit<8> seg;
}
header accnt_bal_t {
  bit<32> vid;
  bit<16> time;
  bit<32> qid;
  bit<32> bal;
}
header accnt_bal_req_t {
  bit<32> vid;
  bit<16> time;
  bit<32> qid;
}
header ethernet_t {
  bit<48> srcAddr;
  bit<16> etherType;
  bit<48> dstAddr;
}
header expenditure_report_t {
  bit<16> time;
  bit<32> qid;
  bit<16> emit;
  bit<16> bal;
}
header expenditure_req_t {
  bit<8> xway;
  bit<32> vid;
  bit<16> time;
  bit<32> qid;
  bit<8> day;
}
header ipv4_t {
  bit<16> totalLen;
  bit<8> protocol;
  bit<32> dstAddr;
}
header lr_msg_type_t {
  bit<8> msg_type;
}
header pos_report_t {
  bit<8> xway;
  bit<32> vid;
  bit<16> time;
  bit<8> spd;
  bit<8> seg;
  bit<8> lane;
  bit<8> dir;
}
header toll_notification_t {
  bit<32> vid;
  bit<16> toll;
  bit<16> time;
  bit<8> spd;
}
header travel_estimate_t {
  bit<16> travel_time;
  bit<16> toll;
  bit<32> qid;
}
header travel_estimate_req_t {
  bit<8> xway;
  bit<8> tod;
  bit<8> seg_init;
  bit<8> seg_end;
  bit<32> qid;
  bit<8> dow;
}
header udp_t {
  bit<16> length;
  bit<16> dstPort;
  bit<16> checksum;
}
// Assemble headers in a single struct
struct my_headers_t {
  accident_alert_t accident_alert;
  accnt_bal_t accnt_bal;
  accnt_bal_req_t accnt_bal_req;
  ethernet_t ethernet;
  expenditure_report_t expenditure_report;
  expenditure_req_t expenditure_req;
  ipv4_t ipv4;
  lr_msg_type_t lr_msg_type;
  pos_report_t pos_report;
  toll_notification_t toll_notification;
  travel_estimate_t travel_estimate;
  travel_estimate_req_t travel_estimate_req;
  udp_t udp;
}

  
// METADATA



struct accident_egress_meta_t {

  bit<1> recirculate;

}

struct accident_meta_t {

  bit<1> has_accident_ahead;
  bit<8> accident_seg;

}

struct accnt_bal_egress_meta_t {

  bit<1> recirculate;

}

struct seg_meta_t {

  bit<8> vol;
  bit<8> prev_vol;
  bit<16> ewma_spd;

}

struct stopped_ahead_t {

  bit<8> seg4l3;
  bit<8> seg4l2;
  bit<8> seg4l1;
  bit<8> seg4_ord;
  bit<8> seg3l3;
  bit<8> seg3l2;
  bit<8> seg3l1;
  bit<8> seg3_ord;
  bit<8> seg2l3;
  bit<8> seg2l2;
  bit<8> seg2l1;
  bit<8> seg2_ord;
  bit<8> seg1l3;
  bit<8> seg1l2;
  bit<8> seg1l1;
  bit<8> seg1_ord;
  bit<8> seg0l3;
  bit<8> seg0l2;
  bit<8> seg0l1;
  bit<8> seg0_ord;

}

struct te_md_t {

  bit<16> toll_sum;
  bit<16> time_sum;
  bit<8> seg_end;
  bit<8> seg_cur;
  bit<1> recirculated;
  bit<1> dir;

}

struct toll_egress_meta_t {

  bit<1> recirculate;

}

struct toll_meta_t {

  bit<16> toll;
  bit<1> has_toll;
  bit<32> bal;

}

struct v_state_t {

  bit<8> prev_xway;
  bit<8> prev_spd;
  bit<8> prev_seg;
  bit<3> prev_nomove_cnt;
  bit<3> prev_lane;
  bit<1> prev_dir;
  bit<3> nomove_cnt;
  bit<1> new_seg;
  bit<1> new;

}
struct my_metadata_t {
  accident_egress_meta_t accident_egress_meta;
  accident_meta_t accident_meta;
  accnt_bal_egress_meta_t accnt_bal_egress_meta;
  seg_meta_t seg_meta;
  stopped_ahead_t stopped_ahead;
  te_md_t te_md;
  toll_egress_meta_t toll_egress_meta;
  toll_meta_t toll_meta;
  v_state_t v_state;


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


  state parse_accident_alert {
    packet.extract(hdr.accident_alert);
    transition accept;
  }
    

  state parse_accnt_bal {
    packet.extract(hdr.accnt_bal);
    transition accept;
  }
    

  state parse_accnt_bal_req {
    packet.extract(hdr.accnt_bal_req);
    transition accept;
  }
    

  state parse_ethernet {
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType){
      (16w2048) : parse_ipv4;
      default : accept;
    }

  }
    

  state parse_expenditure_report {
    packet.extract(hdr.expenditure_report);
    transition accept;
  }
    

  state parse_expenditure_req {
    packet.extract(hdr.expenditure_req);
    transition accept;
  }
    

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    transition select(hdr.ipv4.protocol){
      (8w17) : parse_udp;
      default : accept;
    }

  }
    

  state parse_lr {
    packet.extract(hdr.lr_msg_type);
    transition select(hdr.lr_msg_type.msg_type){
      (8w0) : parse_pos_report;
      (8w2) : parse_accnt_bal_req;
      (8w10) : parse_toll_notification;
      (8w11) : parse_accident_alert;
      (8w12) : parse_accnt_bal;
      (8w3) : parse_expenditure_req;
      (8w13) : parse_expenditure_report;
      (8w4) : parse_travel_estimate_req;
      (8w14) : parse_travel_estimate;
      default : accept;
    }

  }
    

  state parse_pos_report {
    packet.extract(hdr.pos_report);
    transition accept;
  }
    

  state parse_toll_notification {
    packet.extract(hdr.toll_notification);
    transition accept;
  }
    

  state parse_travel_estimate {
    packet.extract(hdr.travel_estimate);
    transition accept;
  }
    

  state parse_travel_estimate_req {
    packet.extract(hdr.travel_estimate_req);
    transition accept;
  }
    

  state parse_udp {
    packet.extract(hdr.udp);
    transition select(hdr.udp.dstPort){
      (16w4660) : parse_lr;
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
  bit<1> DEVNULL_v_dir_reg_do_update_pos_state;
  bit<32> DEVNULL_v_dir_reg_do_update_pos_state_index;
  bit<8> DEVNULL_v_dir_reg_do_update_pos_state_value;
  bit<32> DEVNULL_v_lane_reg_do_update_pos_state;
  bit<32> DEVNULL_v_lane_reg_do_update_pos_state_index;
  bit<8> DEVNULL_v_lane_reg_do_update_pos_state_value;
  bit<32> DEVNULL_v_seg_reg_do_update_pos_state;
  bit<32> DEVNULL_v_seg_reg_do_update_pos_state_index;
  bit<8> DEVNULL_v_seg_reg_do_update_pos_state_value;
  bit<32> DEVNULL_v_spd_reg_do_update_pos_state;
  bit<32> DEVNULL_v_spd_reg_do_update_pos_state_index;
  bit<8> DEVNULL_v_spd_reg_do_update_pos_state_value;
  bit<32> DEVNULL_v_valid_reg_do_update_pos_state;
  bit<32> DEVNULL_v_valid_reg_do_update_pos_state_index;
  bit<1> DEVNULL_v_valid_reg_do_update_pos_state_value;
  bit<32> DEVNULL_v_xway_reg_do_update_pos_state;
  bit<32> DEVNULL_v_xway_reg_do_update_pos_state_index;
  bit<8> DEVNULL_v_xway_reg_do_update_pos_state_value;
  bit<16> base_toll;
  bit<48> dmac;
  bit<32> nhop_ipv4;
  bit<9> port;
  bit<1> v_dir_reg_do_update_pos_state;
  bit<3> v_lane_reg_do_update_pos_state;
  bit<8> v_seg_reg_do_update_pos_state;
  bit<8> v_spd_reg_do_update_pos_state;
  bit<1> v_valid_reg_do_update_pos_state;
  bit<8> v_xway_reg_do_update_pos_state;

  // Action Definitions
  action check_toll_action_0(bit<16> base_toll){
    meta.toll_meta.has_toll = 1w1;
    meta.toll_meta.toll = (base_toll * (((8w0 ++ meta.seg_meta.vol) - 16w50) * ((8w0 ++ meta.seg_meta.vol) - 16w50)));

    meta.toll_meta.bal = (meta.toll_meta.bal + (16w0 ++ meta.toll_meta.toll));

  }

  action check_toll_action_1(){

  }

  action dec_prev_stopped_action_0(){

  }

  action dec_prev_stopped_action_1(){

  }

  action forward_action_0(bit<48> dmac){
    hdr.ethernet.dstAddr = dmac;
  }

  action forward_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action forward_action_2(){

  }

  action inc_stopped_action_0(){

  }

  action ipv4_lpm_action_0(bit<32> nhop_ipv4,bit<9> port){
    hdr.ipv4.dstAddr = nhop_ipv4;
    standard_metadata.egress_spec = port;
  }

  action ipv4_lpm_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action ipv4_lpm_action_2(){

  }

  action load_accnt_bal_action_0(){

  }

  action load_stopped_ahead_action_0(){

    meta.stopped_ahead.seg0_ord = (meta.stopped_ahead.seg0l1 | (meta.stopped_ahead.seg0l2 | meta.stopped_ahead.seg0l3));
    meta.stopped_ahead.seg1_ord = (meta.stopped_ahead.seg1l1 | (meta.stopped_ahead.seg1l2 | meta.stopped_ahead.seg1l3));
    meta.stopped_ahead.seg2_ord = (meta.stopped_ahead.seg2l1 | (meta.stopped_ahead.seg2l2 | meta.stopped_ahead.seg2l3));
    meta.stopped_ahead.seg3_ord = (meta.stopped_ahead.seg3l1 | (meta.stopped_ahead.seg3l2 | meta.stopped_ahead.seg3l3));
    meta.stopped_ahead.seg4_ord = (meta.stopped_ahead.seg4l1 | (meta.stopped_ahead.seg4l2 | meta.stopped_ahead.seg4l3));
  }

  action load_stopped_ahead_action_1(){

  }

  action loc_changed_action_0(){

  }

  action loc_changed_action_1(){

  }

  action loc_not_changed_action_0(){

    meta.v_state.nomove_cnt = ((meta.v_state.prev_nomove_cnt + 3w1) - (((meta.v_state.prev_nomove_cnt + 3w1) & 3w4) >> 3w2));

  }

  action loc_not_changed_action_1(){

  }

  action update_ewma_spd_action_0(){
    meta.seg_meta.ewma_spd = (8w0 ++ hdr.pos_report.spd);

  }

  action update_ewma_spd_action_1(){

    meta.seg_meta.ewma_spd = (((16w0 ++ meta.seg_meta.ewma_spd) * 32w96) + (16w0 ++ (((8w0 ++ hdr.pos_report.spd) * 16w32) >> 16w7)))[15:0];

  }

  action update_new_seg_action_0(){
    meta.v_state.new_seg = 1w1;
  }

  action update_new_seg_action_1(){

  }

  action update_pos_state_action_0(){
    DEVNULL_v_valid_reg_do_update_pos_state = hdr.pos_report.vid;
    meta.v_state.new = v_valid_reg_do_update_pos_state;
    meta.v_state.new = ~meta.v_state.new;
    DEVNULL_v_spd_reg_do_update_pos_state = hdr.pos_report.vid;
    meta.v_state.prev_spd = v_spd_reg_do_update_pos_state;
    DEVNULL_v_xway_reg_do_update_pos_state = hdr.pos_report.vid;
    meta.v_state.prev_xway = v_xway_reg_do_update_pos_state;
    DEVNULL_v_lane_reg_do_update_pos_state = hdr.pos_report.vid;
    meta.v_state.prev_lane = v_lane_reg_do_update_pos_state;
    DEVNULL_v_seg_reg_do_update_pos_state = hdr.pos_report.vid;
    meta.v_state.prev_seg = v_seg_reg_do_update_pos_state;
    DEVNULL_v_dir_reg_do_update_pos_state = meta.v_state.prev_dir;
    meta.v_state.prev_dir = v_dir_reg_do_update_pos_state;
    DEVNULL_v_valid_reg_do_update_pos_state_index = hdr.pos_report.vid;
    DEVNULL_v_valid_reg_do_update_pos_state_value = 1w1;
    DEVNULL_v_spd_reg_do_update_pos_state_index = hdr.pos_report.vid;
    DEVNULL_v_spd_reg_do_update_pos_state_value = hdr.pos_report.spd;
    DEVNULL_v_xway_reg_do_update_pos_state_index = hdr.pos_report.vid;
    DEVNULL_v_xway_reg_do_update_pos_state_value = hdr.pos_report.xway;
    DEVNULL_v_lane_reg_do_update_pos_state_index = hdr.pos_report.vid;
    DEVNULL_v_lane_reg_do_update_pos_state_value = hdr.pos_report.lane;
    DEVNULL_v_seg_reg_do_update_pos_state_index = hdr.pos_report.vid;
    DEVNULL_v_seg_reg_do_update_pos_state_value = hdr.pos_report.seg;
    DEVNULL_v_dir_reg_do_update_pos_state_index = hdr.pos_report.vid;
    DEVNULL_v_dir_reg_do_update_pos_state_value = hdr.pos_report.dir;
  }

  action update_pos_state_action_1(){

  }

  action update_vol_state_action_0(){

  }

  action update_vol_state_action_1(){

    meta.seg_meta.vol = (meta.seg_meta.vol + 8w1);

  }

  action update_vol_state_action_2(){

    meta.seg_meta.vol = (meta.seg_meta.vol + 8w1);

    meta.seg_meta.prev_vol = (meta.seg_meta.prev_vol - 8w1);
  }

  action update_vol_state_action_3(){

  }

  // Table Definitions

  table check_toll {
    key = {
      meta.v_state.new_seg : exact;
      meta.seg_meta.ewma_spd : exact;
      meta.seg_meta.vol : exact;
      meta.accident_meta.has_accident_ahead : exact;
    }
    actions = {
      check_toll_action_0;
      check_toll_action_1;
    }
  }
    
  table dec_prev_stopped {
    key = {
    }
    actions = {
      dec_prev_stopped_action_0;
      dec_prev_stopped_action_1;
    }
  }
    
  table forward {
    key = {
      hdr.ipv4.dstAddr : exact;
    }
    actions = {
      forward_action_0;
      forward_action_1;
      forward_action_2;
    }
  }
    
  table inc_stopped {
    key = {
    }
    actions = {
      inc_stopped_action_0;
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
    
  table load_accnt_bal {
    key = {
    }
    actions = {
      load_accnt_bal_action_0;
    }
  }
    
  table load_stopped_ahead {
    key = {
    }
    actions = {
      load_stopped_ahead_action_0;
      load_stopped_ahead_action_1;
    }
  }
    
  table loc_changed {
    key = {
    }
    actions = {
      loc_changed_action_0;
      loc_changed_action_1;
    }
  }
    
  table loc_not_changed {
    key = {
    }
    actions = {
      loc_not_changed_action_0;
      loc_not_changed_action_1;
    }
  }
    
  table update_ewma_spd {
    key = {
      meta.seg_meta.vol : exact;
    }
    actions = {
      update_ewma_spd_action_0;
      update_ewma_spd_action_1;
    }
  }
    
  table update_new_seg {
    key = {
    }
    actions = {
      update_new_seg_action_0;
      update_new_seg_action_1;
    }
  }
    
  table update_pos_state {
    key = {
    }
    actions = {
      update_pos_state_action_0;
      update_pos_state_action_1;
    }
  }
    
  table update_vol_state {
    key = {
      meta.v_state.new : exact;
      meta.v_state.new_seg : exact;
    }
    actions = {
      update_vol_state_action_0;
      update_vol_state_action_1;
      update_vol_state_action_2;
      update_vol_state_action_3;
    }
  }
    

  apply {
    // Pipeline
    if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {
      standard_metadata.egress_spec = 9w511;
    } else {
      if (!(1w1 == (hdr.pos_report.isValid() ? 1w1 : 1w0))) {
        if (!(1w1 == (hdr.accnt_bal_req.isValid() ? 1w1 : 1w0))) {} else {
          load_accnt_bal.apply();
        }

      } else {
        update_pos_state.apply();
        if (!(!(meta.v_state.prev_seg == hdr.pos_report.seg) || (1w1 == meta.v_state.new))) {} else {
          update_new_seg.apply();
        }

        update_vol_state.apply();
        update_ewma_spd.apply();
        if (!((((hdr.pos_report.xway == meta.v_state.prev_xway) && (hdr.pos_report.seg == meta.v_state.prev_seg)) && (hdr.pos_report.dir == (7w0 ++ meta.v_state.prev_dir))) && (hdr.pos_report.lane == (5w0 ++ meta.v_state.prev_lane)))) {
          loc_changed.apply();
        } else {
          loc_not_changed.apply();
        }

        if (!((meta.v_state.prev_nomove_cnt == 3w3) && (meta.v_state.nomove_cnt < 3w3))) {} else {
          dec_prev_stopped.apply();
        }

        if (!((meta.v_state.prev_nomove_cnt < 3w3) && (meta.v_state.nomove_cnt == 3w3))) {} else {
          inc_stopped.apply();
        }

        load_stopped_ahead.apply();
        check_toll.apply();
      }

      ipv4_lpm.apply();
      forward.apply();
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
  bit<16> bal;
  bit<32> mir_ses;
  bit<48> smac;
  bit<16> time;
  bit<16> toll;

  // Action Definitions
  action daily_expenditure_action_0(bit<16> bal){
    hdr.lr_msg_type.msg_type = 8w13;
    hdr.expenditure_report.setValid();
    hdr.expenditure_report.time = hdr.expenditure_req.time;
    hdr.expenditure_report.emit = hdr.expenditure_req.time;
    hdr.expenditure_report.qid = hdr.expenditure_req.qid;
    hdr.expenditure_report.bal = bal;
    hdr.expenditure_req.setInvalid();
    hdr.ipv4.totalLen = 16w39;
    hdr.udp.length = 16w19;
    hdr.udp.checksum = 16w0;
  }

  action daily_expenditure_action_1(){

  }

  action send_accident_alert_action_0(){
    meta.accident_egress_meta.recirculate = 1w1;
  }

  action send_accident_alert_action_1(){
    hdr.lr_msg_type.msg_type = 8w11;
    hdr.accident_alert.setValid();
    hdr.accident_alert.time = hdr.pos_report.time;
    hdr.accident_alert.vid = hdr.pos_report.vid;
    hdr.accident_alert.seg = meta.accident_meta.accident_seg;
    hdr.pos_report.setInvalid();
    hdr.ipv4.totalLen = 16w38;
    hdr.udp.length = 16w18;
    hdr.udp.checksum = 16w0;
  }

  action send_accident_alert_action_2(){

  }

  action send_accnt_bal_action_0(){
    meta.accnt_bal_egress_meta.recirculate = 1w1;
  }

  action send_accnt_bal_action_1(){
    hdr.lr_msg_type.msg_type = 8w12;
    hdr.accnt_bal.setValid();
    hdr.accnt_bal.time = hdr.accnt_bal_req.time;
    hdr.accnt_bal.vid = hdr.accnt_bal_req.vid;
    hdr.accnt_bal.qid = hdr.accnt_bal_req.qid;
    hdr.accnt_bal.bal = meta.toll_meta.bal;
    hdr.accnt_bal_req.setInvalid();
    hdr.ipv4.totalLen = 16w45;
    hdr.udp.length = 16w25;
    hdr.udp.checksum = 16w0;
  }

  action send_accnt_bal_action_2(){

  }

  action send_frame_action_0(bit<48> smac){
    hdr.ethernet.srcAddr = smac;
  }

  action send_frame_action_1(){
    standard_metadata.egress_spec = 9w511;
  }

  action send_frame_action_2(){

  }

  action send_toll_notification_action_0(){
    meta.toll_egress_meta.recirculate = 1w1;
  }

  action send_toll_notification_action_1(){
    hdr.lr_msg_type.msg_type = 8w10;
    hdr.toll_notification.setValid();
    hdr.toll_notification.time = hdr.pos_report.time;
    hdr.toll_notification.vid = hdr.pos_report.vid;
    hdr.toll_notification.spd = meta.seg_meta.ewma_spd[7:0];
    hdr.toll_notification.toll = meta.toll_meta.toll;
    hdr.pos_report.setInvalid();
    hdr.ipv4.totalLen = 16w50;
    hdr.udp.length = 16w20;
    hdr.udp.checksum = 16w0;
  }

  action send_toll_notification_action_2(){

  }

  action travel_estimate_history_action_0(bit<16> time,bit<16> toll){
    meta.te_md.time_sum = (meta.te_md.time_sum + time);
    meta.te_md.toll_sum = (meta.te_md.toll_sum + toll);
  }

  action travel_estimate_history_action_1(){

  }

  action travel_estimate_init_action_0(){
    meta.te_md.dir = 1w0;
    meta.te_md.seg_cur = hdr.travel_estimate_req.seg_init;
    meta.te_md.seg_end = hdr.travel_estimate_req.seg_end;
  }

  action travel_estimate_init_rev_action_0(){
    meta.te_md.dir = 1w1;
    meta.te_md.seg_cur = hdr.travel_estimate_req.seg_end;
    meta.te_md.seg_end = hdr.travel_estimate_req.seg_init;
  }

  action travel_estimate_recirc_action_0(bit<32> mir_ses){
    meta.te_md.seg_cur = (meta.te_md.seg_cur + 8w1);
    meta.te_md.recirculated = 1w1;
    standard_metadata.egress_spec = 9w511;
  }

  action travel_estimate_recirc_action_1(){

  }

  action travel_estimate_send_action_0(){
    hdr.lr_msg_type.msg_type = 8w14;
    hdr.travel_estimate.setValid();
    hdr.travel_estimate.qid = hdr.travel_estimate_req.qid;
    hdr.travel_estimate.travel_time = meta.te_md.time_sum;
    hdr.travel_estimate.toll = meta.te_md.toll_sum;
    hdr.travel_estimate_req.setInvalid();
    hdr.ipv4.totalLen = 16w37;
    hdr.udp.length = 16w16;
    hdr.udp.checksum = 16w0;
  }

  // Table Definitions

  table daily_expenditure {
    key = {
      hdr.expenditure_req.vid : exact;
      hdr.expenditure_req.day : exact;
      hdr.expenditure_req.xway : exact;
    }
    actions = {
      daily_expenditure_action_0;
      daily_expenditure_action_1;
    }
  }
    
  table send_accident_alert {
    key = {
      meta.accident_meta.has_accident_ahead : exact;
      meta.accident_egress_meta.recirculate : exact;
    }
    actions = {
      send_accident_alert_action_0;
      send_accident_alert_action_1;
      send_accident_alert_action_2;
    }
  }
    
  table send_accnt_bal {
    key = {
      meta.accnt_bal_egress_meta.recirculate : exact;
    }
    actions = {
      send_accnt_bal_action_0;
      send_accnt_bal_action_1;
      send_accnt_bal_action_2;
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
    
  table send_toll_notification {
    key = {
      meta.toll_meta.has_toll : exact;
      meta.toll_egress_meta.recirculate : exact;
    }
    actions = {
      send_toll_notification_action_0;
      send_toll_notification_action_1;
      send_toll_notification_action_2;
    }
  }
    
  table travel_estimate_history {
    key = {
      hdr.travel_estimate_req.dow : exact;
      hdr.travel_estimate_req.tod : exact;
      hdr.travel_estimate_req.xway : exact;
      meta.te_md.dir : exact;
      meta.te_md.seg_cur : exact;
    }
    actions = {
      travel_estimate_history_action_0;
      travel_estimate_history_action_1;
    }
  }
    
  table travel_estimate_init {
    key = {
    }
    actions = {
      travel_estimate_init_action_0;
    }
  }
    
  table travel_estimate_init_rev {
    key = {
    }
    actions = {
      travel_estimate_init_rev_action_0;
    }
  }
    
  table travel_estimate_recirc {
    key = {
    }
    actions = {
      travel_estimate_recirc_action_0;
      travel_estimate_recirc_action_1;
    }
  }
    
  table travel_estimate_send {
    key = {
    }
    actions = {
      travel_estimate_send_action_0;
    }
  }
    

  apply {
    // Pipeline
    if (!(1w1 == (hdr.ipv4.isValid() ? 1w1 : 1w0))) {} else {
      if (!(1w1 == (hdr.pos_report.isValid() ? 1w1 : 1w0))) {
        if (!(1w1 == (hdr.accnt_bal_req.isValid() ? 1w1 : 1w0))) {
          if (!(1w1 == (hdr.expenditure_req.isValid() ? 1w1 : 1w0))) {
            if (!(1w1 == (hdr.travel_estimate_req.isValid() ? 1w1 : 1w0))) {} else {
              if (!(1w0 == meta.te_md.recirculated)) {} else {
                if (!(hdr.travel_estimate_req.seg_init < hdr.travel_estimate_req.seg_end)) {
                  travel_estimate_init_rev.apply();
                } else {
                  travel_estimate_init.apply();
                }

              }

              travel_estimate_history.apply();
              if (!(meta.te_md.seg_cur == meta.te_md.seg_end)) {
                travel_estimate_recirc.apply();
              } else {
                travel_estimate_send.apply();
              }

            }

          } else {
            daily_expenditure.apply();
          }

        } else {
          send_accnt_bal.apply();
        }

      } else {
        send_accident_alert.apply();
        send_toll_notification.apply();
      }

      send_frame.apply();
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
  
