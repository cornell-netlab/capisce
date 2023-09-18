open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type egress_metadata_t = {
  recirculate : Var.t
}

let accident_egress_meta : egress_metadata_t =
  {
    recirculate = Var.make "meta.accident_egress_meta.recirculate" 1;
  }

let accnt_bal_egress_meta : egress_metadata_t =
  {
    recirculate = Var.make "meta.accnt_bal_egress_meta.recirculate" 1;
  }

let toll_egress_meta : egress_metadata_t =
  {
    recirculate = Var.make "meta.toll_egress_meta.recirculate" 1;
  }

type accident_meta_t = {
    cur_stp_cnt : Var.t;
    prev_stp_cnt : Var.t;
    accident_seg : Var.t;
    has_accident_ahead : Var.t;
}

let accident_meta : accident_meta_t =
  let field f sz = Var.make (Printf.sprintf "meta.accident_meta.%s" f) sz in
  {
    cur_stp_cnt = field "cur_stp_cnt" 8;
    prev_stp_cnt = field "prev_stp_cnt" 8;
    accident_seg = field "accident_seg" 8;
    has_accident_ahead = field "has_accident_ahead" 1;
}

type seg_metadata_t = {
  vol : Var.t;
  prev_vol : Var.t;
  ewma_spd : Var.t;
}

let seg_meta : seg_metadata_t =
  let field f sz = Var.make (Printf.sprintf "meta.seg_meta.%s" f) sz in
  {
    vol = field "vol" 8;
    prev_vol = field "prev_vol" 8;
    ewma_spd = field "ewma_spd" 16;
}

type stopped_metadata_t = {
    seg0l1 : Var.t;
    seg0l2 : Var.t;
    seg0l3 : Var.t;
    seg1l1 : Var.t;
    seg1l2 : Var.t;
    seg1l3 : Var.t;
    seg2l1 : Var.t;
    seg2l2 : Var.t;
    seg2l3 : Var.t;
    seg3l1 : Var.t;
    seg3l2 : Var.t;
    seg3l3 : Var.t;
    seg4l1 : Var.t;
    seg4l2 : Var.t;
    seg4l3 : Var.t;
    seg0_ord : Var.t;
    seg1_ord : Var.t;
    seg2_ord : Var.t;
    seg3_ord : Var.t;
    seg4_ord : Var.t;
}
let stopped_ahead : stopped_metadata_t =
  let field f = Var.make (Printf.sprintf "meta.stopped_ahead.%s" f) 8 in
  {
    seg0l1 = field "seg0l1";
    seg0l2 = field "seg0l2";
    seg0l3 = field "seg0l3";
    seg1l1 = field "seg1l1";
    seg1l2 = field "seg1l2";
    seg1l3 = field "seg1l3";
    seg2l1 = field "seg2l1";
    seg2l2 = field "seg2l2";
    seg2l3 = field "seg2l3";
    seg3l1 = field "seg3l1";
    seg3l2 = field "seg3l2";
    seg3l3 = field "seg3l3";
    seg4l1 = field "seg4l1";
    seg4l2 = field "seg4l2";
    seg4l3 = field "seg4l3";
    seg0_ord = field "seg0_ord";
    seg1_ord = field "seg1_ord";
    seg2_ord = field "seg2_ord";
    seg3_ord = field "seg3_ord";
    seg4_ord = field "seg4_ord";
}

type travel_estimate_metadata_t = {
    recirculated : Var.t;
    dir : Var.t;
    seg_cur : Var.t;
    seg_end : Var.t;
    toll_sum : Var.t;
    time_sum : Var.t;
}

let te_md : travel_estimate_metadata_t =
  let field f sz = Var.make (Printf.sprintf "meta.te_md.%s" f) sz in
  {
    recirculated = field "recirculated" 1;
    dir = field "dir" 1;
    seg_cur = field "seg_cur" 8;
    seg_end = field "seg_end" 8;
    toll_sum = field "toll_sum" 16;
    time_sum = field "time_sum" 16;
  }

type toll_metadata_t = {
    toll : Var.t;
    has_toll : Var.t;
    bal : Var.t;
}
let toll_meta : toll_metadata_t =
  let field f sz = Var.make (Printf.sprintf "meta.toll_meta.%s" f) sz in
  {
    toll = field "toll" 16;
    has_toll = field "has_toll" 1;
    bal = field "bal" 32;
  }

type v_state_metadata_t = {
    new_ : Var.t;
    new_seg : Var.t;
    prev_spd : Var.t;
    prev_xway : Var.t;
    prev_lane : Var.t;
    prev_seg : Var.t;
    prev_dir : Var.t;
    prev_nomove_cnt : Var.t;
    nomove_cnt : Var.t;
  }
let v_state : v_state_metadata_t =
  let field f sz = Var.make (Printf.sprintf "meta.v_state.%s" f) sz in
  {
    new_ = field "new" 1;
    new_seg = field "new_seg" 1;
    prev_spd = field "prev_spd" 8;
    prev_xway = field "prev_xway" 8;
    prev_lane = field "prev_lane" 3;
    prev_seg = field "prev_seg" 8;
    prev_dir = field "prev_dir" 1;
    prev_nomove_cnt = field "prev_nomove_cnt" 3;
    nomove_cnt = field "nomove_cnt" 3;
}


type accident_alert_t = {
  isValid : Var.t;
  time : Var.t;
  vid : Var.t;
  emit : Var.t;
  seg : Var.t;
}
let accident_alert : accident_alert_t =
  let field f sz = Var.make (Printf.sprintf "hdr.accident_alert.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    vid = field "vid" 32;
    emit = field "emit" 16;
    seg = field "seg" 8;
}


type accnt_bal_t = {
  isValid : Var.t;
  time : Var.t;
  vid : Var.t;
  emit : Var.t;
  qid : Var.t;
  bal : Var.t;
}

let accnt_bal : accnt_bal_t =
  let field f sz = Var.make (Printf.sprintf "hdr.accnt_bal.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    vid = field "vid" 32;
    emit = field "emit" 16;
    qid = field "qid" 32;
    bal = field "bal" 32
}

type accnt_bal_req_t = {
  isValid : Var.t;
  time : Var.t;
  vid : Var.t;
  qid : Var.t;
}

let accnt_bal_req : accnt_bal_req_t =
  let field f sz = Var.make (Printf.sprintf "hdr.accnt_bal_req.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    vid = field "vid" 32;
    qid = field "qid" 32;
  }

type ethernet_t = {
  isValid : Var.t;
  dstAddr : Var.t;
  srcAddr : Var.t;
  etherType : Var.t;
}

let ethernet : ethernet_t =
  let field f sz = Var.make (Printf.sprintf "hdr.ethernet.%s" f) sz in
  {
    isValid = field "isValid" 1;
    dstAddr = field "dstAddr" 48;
    srcAddr = field "srcAddr" 48;
    etherType = field "etherType" 16;
}

type expenditure_report_t = {
  isValid : Var.t;
  time : Var.t;
  emit : Var.t;
  qid : Var.t ;
  bal : Var.t;
}

let expenditure_report : expenditure_report_t =
  let field f sz = Var.make (Printf.sprintf "hdr.expenditure_report.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    emit = field "emit" 16;
    qid = field "qid" 32;
    bal = field "bal" 16
  }

type expenditure_req_t = {
  isValid : Var.t;
  time : Var.t;
  vid : Var.t;
  qid : Var.t;
  xway : Var.t;
  day : Var.t;
}
let expenditure_req : expenditure_req_t =
  let field f sz = Var.make (Printf.sprintf "hdr.expenditure_req.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    vid = field "vid" 32;
    qid = field "qid" 32;
    xway = field "xway" 8;
    day = field "day" 8;
}

type ipv4_t = {
  isValid : Var.t;
  version : Var.t;
  ihl : Var.t;
  diffserv : Var.t;
  totalLen : Var.t;
  identification : Var.t;
  flags : Var.t;
  fragOffset : Var.t;
  ttl : Var.t;
  protocol : Var.t;
  hdrChecksum : Var.t;
  srcAddr : Var.t;
  dstAddr : Var.t;
}

let ipv4 : ipv4_t =
  let field f sz = Var.make (Printf.sprintf "hdr.ipv4.%s" f) sz in
  {
    isValid = field "isValid" 1;
    version = field "version" 4;
    ihl = field "ihl" 4;
    diffserv = field "diffserve" 8;
    totalLen = field "totalLen" 16;
    identification = field "identification" 16;
    flags = field "flags" 3;
    fragOffset = field "fragOffset" 13;
    ttl = field "ttl" 8;
    protocol = field "protocol" 8;
    hdrChecksum = field "hdrChecksum" 16;
    srcAddr = field "srcAddr" 32;
    dstAddr = field "dstAddr" 32;
}

type lr_msg_type_t = {
  isValid : Var.t;
  msg_type : Var.t
}

let lr_msg_type : lr_msg_type_t = {
  isValid = Var.make "hdr.lr_msg_type.isValid" 1;
  msg_type = Var.make "hdr.lr_msg_type.msg_type" 8;
}

type pos_report_t = {
  isValid : Var.t;
  time : Var.t;
  vid : Var.t;
  spd : Var.t;
  xway : Var.t;
  lane : Var.t;
  dir : Var.t;
  seg : Var.t;
}

let pos_report : pos_report_t =
  let field f sz = Var.make (Printf.sprintf "hdr.pos_report.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    vid = field "vid" 32;
    spd = field "spd" 8;
    xway = field "xway" 8;
    lane = field "lane" 8;
    dir = field "dir" 8;
    seg = field "seg" 8;
  }

type toll_notification_t =
  {
    isValid : Var.t;
    time : Var.t;
    vid : Var.t;
    emit : Var.t;
    spd : Var.t;
    toll : Var.t;
}

let toll_notification : toll_notification_t =
  let field f sz = Var.make (Printf.sprintf "hdr.toll_notification.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    vid  = field "vid" 32;
    emit = field "emit" 16;
    spd = field "spd" 8;
    toll = field "toll" 16;
  }

type travel_estimate_t = {
  isValid : Var.t;
  qid : Var.t;
  travel_time : Var.t;
  toll : Var.t;
}

let travel_estimate : travel_estimate_t =
  let field f sz = Var.make (Printf.sprintf "hdr.travel_estimate.%s" f) sz in
  {
    isValid = field "isValid" 1;
    qid = field "qid" 32;
    travel_time = field "travel_time" 16;
    toll = field "toll" 16;
  }

type travel_estimate_req_t = {
  isValid : Var.t;
  time : Var.t;
  qid : Var.t;
  xway : Var.t;
  seg_init : Var.t;
  seg_end : Var.t;
  dow : Var.t;
  tod : Var.t;
}

let travel_estimate_req : travel_estimate_req_t =
  let field f sz = Var.make (Printf.sprintf "hdr.travel_estimate_req.%s" f) sz in
  {
    isValid = field "isValid" 1;
    time = field "time" 16;
    qid = field "qid" 32;
    xway = field "xway" 8;
    seg_init = field "seg_init" 8;
    seg_end = field "seg_end" 8;
    dow = field "dow" 8;
    tod = field "tod" 8;
}


type metadata_t =  {
    accident_egress_meta : egress_metadata_t;
    accident_meta : accident_meta_t;
    accnt_bal_egress_meta : egress_metadata_t;
    seg_meta : seg_metadata_t;
    stopped_ahead : stopped_metadata_t;
    te_md : travel_estimate_metadata_t;
    toll_egress_meta : egress_metadata_t;
    toll_meta : toll_metadata_t;
    v_state : v_state_metadata_t;
}

let meta : metadata_t = {
    accident_egress_meta;
    accident_meta;
    accnt_bal_egress_meta;
    seg_meta;
    stopped_ahead;
    te_md;
    toll_egress_meta;
    toll_meta;
    v_state;
}

type header_t = {
    accident_alert : accident_alert_t;
    accnt_bal : accnt_bal_t;
    accnt_bal_req : accnt_bal_req_t;
    ethernet : ethernet_t;
    expenditure_report : expenditure_report_t;
    expenditure_req : expenditure_req_t;
    ipv4 : ipv4_t;
    lr_msg_type : lr_msg_type_t;
    pos_report : pos_report_t;
    toll_notification : toll_notification_t;
    travel_estimate : travel_estimate_t;
    travel_estimate_req : travel_estimate_req_t;
    udp : udp_t;
}

let hdr : header_t = {
    accident_alert;
    accnt_bal;
    accnt_bal_req;
    ethernet;
    expenditure_report;
    expenditure_req;
    ipv4;
    lr_msg_type;
    pos_report;
    toll_notification;
    travel_estimate;
    travel_estimate_req;
    udp;
}


let linearroad_parser =
  let open HoareNet in
  let open Expr in
  let parse_pos_report =
    sequence [
      assign hdr.pos_report.isValid btrue;
      transition_accept
    ]
  in
  let parse_accnt_bal_req =
    sequence [
      assign hdr.accnt_bal_req.isValid btrue;
      transition_accept;
    ]
  in
  let parse_toll_notification =
    sequence [
      assign hdr.toll_notification.isValid btrue;
      transition_accept;
    ]
  in
  let parse_accident_alert =
    sequence [
      assign hdr.accident_alert.isValid btrue;
      transition_accept
    ]
  in
  let parse_accnt_bal =
    sequence [
      assign hdr.accnt_bal.isValid btrue;
      transition_accept
    ]
  in
  let parse_expenditure_req =
    sequence [
      assign hdr.expenditure_req.isValid btrue;
      transition_accept
    ]
  in
  let parse_expenditure_report =
    sequence [
      assign hdr.expenditure_report.isValid btrue;
      transition_accept
    ]
  in
  let parse_travel_estimate_req =
    sequence [
      assign hdr.travel_estimate_req.isValid btrue;
      transition_accept
    ]
  in
  let parse_travel_estimate =
    sequence [
      assign hdr.travel_estimate.isValid btrue;
      transition_accept
    ]
  in
  let parse_lr =
    sequence [
      assign hdr.lr_msg_type.isValid btrue;
      select (var hdr.lr_msg_type.msg_type) [
        bvi  0 8, parse_pos_report;
        bvi  2 8, parse_accnt_bal_req;
        bvi 10 8, parse_toll_notification;
        bvi 11 8, parse_accident_alert;
        bvi 12 8, parse_accnt_bal;
        bvi  3 8, parse_expenditure_req;
        bvi 13 8, parse_expenditure_report;
        bvi  4 8, parse_travel_estimate_req;
        bvi 14 8, parse_travel_estimate;
      ] transition_accept
    ]
  in
  let parse_udp =
    sequence [
      assign hdr.udp.isValid btrue;
      select (var hdr.udp.dstPort) [
        bvi 4660 16, parse_lr
      ] transition_accept
    ]
  in
  let parse_ipv4 =
    sequence [
      assign hdr.ipv4.isValid btrue;
      select (var hdr.ipv4.protocol) [
        bvi 17 8, parse_udp
      ] transition_accept
    ]

  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      select (var hdr.ethernet.etherType) [
        bvi 2048 16, parse_ipv4
      ] transition_accept
    ]
  in
  let start =
    sequence [
      assign hdr.accident_alert.isValid bfalse;
      assign hdr.accnt_bal.isValid bfalse;
      assign hdr.accnt_bal_req.isValid bfalse;
      assign hdr.ethernet.isValid bfalse;
      assign hdr.expenditure_report.isValid bfalse;
      assign hdr.expenditure_req.isValid bfalse;
      assign hdr.ipv4.isValid bfalse;
      assign hdr.lr_msg_type.isValid bfalse;
      assign hdr.pos_report.isValid bfalse;
      assign hdr.toll_notification.isValid bfalse;
      assign hdr.travel_estimate.isValid bfalse;
      assign hdr.travel_estimate_req.isValid bfalse;
      assign hdr.udp.isValid bfalse;
      parse_ethernet
    ]
  in
  start

let linearroad_ingress _ (*annotated*) =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let open Primitives in
  let do_update_pos_state =
    [], Action.[
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_valid_reg.read(meta.v_state.new, (bit<32>)hdr.pos_report.vid); *)
        assign meta.v_state.new_ @@ bnot @@ var meta.v_state.new_;
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_spd_reg.read(meta.v_state.prev_spd, (bit<32>)hdr.pos_report.vid); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_xway_reg.read(meta.v_state.prev_xway, (bit<32>)hdr.pos_report.vid); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_lane_reg.read(meta.v_state.prev_lane, (bit<32>)hdr.pos_report.vid); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_seg_reg.read(meta.v_state.prev_seg, (bit<32>)hdr.pos_report.vid); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_dir_reg.read(meta.v_state.prev_dir, (bit<32>)hdr.pos_report.vid); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_valid_reg.write((bit<32>)hdr.pos_report.vid, (bit<1>)1w1); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_spd_reg.write((bit<32>)hdr.pos_report.vid, (bit<8>)hdr.pos_report.spd); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_xway_reg.write((bit<32>)hdr.pos_report.vid, (bit<8>)hdr.pos_report.xway); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_lane_reg.write((bit<32>)hdr.pos_report.vid, (bit<3>)hdr.pos_report.lane); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_seg_reg.write((bit<32>)hdr.pos_report.vid, (bit<8>)hdr.pos_report.seg); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_dir_reg.write((bit<32>)hdr.pos_report.vid, (bit<1>)hdr.pos_report.dir); *)
      ]
  in
  let update_pos_state = instr_table ("update_pos_state", [], [do_update_pos_state]) in
  let set_new_seg =
    [], Action.[
        assign meta.v_state.new_seg @@ bvi 1 1
      ]
  in
  let update_new_seg =
    instr_table ("update_new_seg", [], [set_new_seg])
  in
  let load_vol =
    [], Action.[
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* seg_vol_reg.read(meta.seg_meta.vol, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir)); *)
      ]
  in
  let load_and_inc_vol =
    [],
    snd load_vol @ Action.[
        assign meta.seg_meta.vol @@ badd (var meta.seg_meta.vol) (bvi 1 8);
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* seg_vol_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir), (bit<8>)meta.seg_meta.vol); *)
      ]
  in
  let load_and_inc_and_dec_vol =
    [],
    snd load_and_inc_vol @ Action.[
        (* seg_vol_reg.read(meta.seg_meta.prev_vol, (bit<32>)((bit<16>)meta.v_state.prev_xway * 16w200 + (bit<16>)(meta.v_state.prev_seg * 8w2) + (bit<16>)meta.v_state.prev_dir)); *)
        assign meta.seg_meta.prev_vol @@ bsub (var meta.seg_meta.prev_vol) (bvi 1 8);
        (* seg_vol_reg.write((bit<32>)((bit<16>)meta.v_state.prev_xway * 16w200 + (bit<16>)(meta.v_state.prev_seg * 8w2) + (bit<16>)meta.v_state.prev_dir), (bit<8>)meta.seg_meta.prev_vol); *)
      ]
  in
  let update_vol_state =
    instr_table ("update_vol_state",
                 [`Exact meta.v_state.new_;
                  `Exact meta.v_state.new_seg
                 ], [
                   load_vol;
                   load_and_inc_vol;
                   load_and_inc_and_dec_vol;
                 ])
  in
  let set_spd =
    [], Action.[
        assign meta.seg_meta.ewma_spd @@ bcast 16 @@ var hdr.pos_report.spd;
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* seg_ewma_spd_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir), (bit<16>)meta.seg_meta.ewma_spd); *)

      ]
  in
  let calc_ewma_spd =
    [], Action.[
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* seg_ewma_spd_reg.read(meta.seg_meta.ewma_spd, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir)); *)
        (* meta.seg_meta.ewma_spd = (bit<16>)( (bit<32>)meta.seg_meta.ewma_spd * 32w96 + (bit<32>) (((bit<16>)hdr.pos_report.spd * 16w32) >> 16w7)); *)
        lshr_ (bmul (bcast 16 @@ var hdr.pos_report.spd) (bvi 32 16)) (bvi 7 16)
        |> bcast 32
        |> badd (bmul (bcast 32 @@ var meta.seg_meta.ewma_spd) (bvi 96 32))
        |> bcast 16
        |> assign meta.seg_meta.ewma_spd;
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid
        (* seg_ewma_spd_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir), (bit<16>)meta.seg_meta.ewma_spd); *)
      ]
  in
  let do_loc_not_changed =
    [], Action.[
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_nomove_cnt_reg.read(meta.v_state.prev_nomove_cnt, (bit<32>)hdr.pos_report.vid); *)
        (* meta.v_state.nomove_cnt = meta.v_state.prev_nomove_cnt + 3w1 - ((meta.v_state.prev_nomove_cnt + 3w1 & 3w4) >> 3w2); *)
        lshr_ (band (badd (var meta.v_state.prev_nomove_cnt) (bvi 1 3)) (bvi 4 3)) (bvi 2 3)
        |> bsub (badd (var meta.v_state.prev_nomove_cnt) (bvi 1 3))
        |> assign meta.v_state.nomove_cnt;
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_nomove_cnt_reg.write((bit<32>)hdr.pos_report.vid, (bit<3>)meta.v_state.nomove_cnt); *)
      ]
  in
  let loc_not_changed =
    instr_table ("loc_not_changed", [], [do_loc_not_changed])
  in
  let do_loc_changed =
    [], Action.[
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_nomove_cnt_reg.read(meta.v_state.prev_nomove_cnt, (bit<32>)hdr.pos_report.vid); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_nomove_cnt_reg.write((bit<32>)hdr.pos_report.vid, (bit<3>)3w0); *)
      ]
  in
  let loc_changed =
    instr_table ("loc_changed", [], [do_loc_changed])
  in
  let update_ewma_spd =
    instr_table ("update_ewma_spd",
                [`Exact meta.seg_meta.vol],
                [set_spd; calc_ewma_spd])
  in
  let do_dec_prev_stopped =
    [], [
        (* stopped_cnt_reg.read(meta.accident_meta.prev_stp_cnt, (bit<32>)((bit<16>)meta.v_state.prev_xway * 16w600 + (bit<16>)(meta.v_state.prev_seg * 8w2) * 16w3 + (bit<16>)meta.v_state.prev_dir * 16w3 + (bit<16>)meta.v_state.prev_lane)); *)
        (* stopped_cnt_reg.write((bit<32>)((bit<16>)meta.v_state.prev_xway * 16w600 + (bit<16>)(meta.v_state.prev_seg * 8w2) * 16w3 + (bit<16>)meta.v_state.prev_dir * 16w3 + (bit<16>)meta.v_state.prev_lane), (bit<8>)(meta.accident_meta.prev_stp_cnt - 8w1)); *)
      ]
  in
  let dec_prev_stopped =
    instr_table ("dec_prev_stopped", [], [do_dec_prev_stopped])
  in
  let do_inc_stopped =
    [], Action.[
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* stopped_cnt_reg.read(meta.accident_meta.cur_stp_cnt, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + (bit<16>)hdr.pos_report.lane)); *)
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* stopped_cnt_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + (bit<16>)hdr.pos_report.lane), (bit<8>)(meta.accident_meta.cur_stp_cnt + 8w1)); *)
    ]
  in
  let inc_stopped =
    instr_table ("inc_stopped", [], [do_inc_stopped])
  in
  let do_load_stopped_ahead =
    [], Action.[
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg0l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg0l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg0l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg1l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w1) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg1l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w1) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg1l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w1) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg2l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w2) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg2l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w2) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg2l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w2) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg3l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w3) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg3l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w3) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg3l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w3) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg4l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w4) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg4l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w4) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2)); *)
      assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
      (* stopped_cnt_reg.read(meta.stopped_ahead.seg4l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w4) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3)); *)
      assign meta.stopped_ahead.seg0_ord @@ bor (var meta.stopped_ahead.seg0l1) @@ bor (var meta.stopped_ahead.seg0l2) (var meta.stopped_ahead.seg0l3);
      assign meta.stopped_ahead.seg1_ord @@ bor (var meta.stopped_ahead.seg1l1) @@ bor (var meta.stopped_ahead.seg1l2) (var meta.stopped_ahead.seg1l3);
      assign meta.stopped_ahead.seg2_ord @@ bor (var meta.stopped_ahead.seg2l1) @@ bor (var meta.stopped_ahead.seg2l2) (var meta.stopped_ahead.seg2l3);
      assign meta.stopped_ahead.seg3_ord @@ bor (var meta.stopped_ahead.seg3l1) @@ bor (var meta.stopped_ahead.seg3l2) (var meta.stopped_ahead.seg3l3);
      assign meta.stopped_ahead.seg4_ord @@ bor (var meta.stopped_ahead.seg4l1) @@ bor (var meta.stopped_ahead.seg4l2) (var meta.stopped_ahead.seg4l3);
    ]
  in
  let load_stopped_ahead =
    instr_table ("load_stopped_ahead", [], [do_load_stopped_ahead])
  in
  let issue_toll =
    let base_toll = Var.make "base_toll" 16 in
    [base_toll], Action.[
        assign meta.toll_meta.has_toll @@ bvi 1 1;
        (bsub (bcast 16 @@ var meta.seg_meta.vol) (bvi 50 16))
        |> bmul (bsub (bcast 16 @@ var meta.seg_meta.vol) (bvi 50 16))
        |> bmul (var base_toll)
        |> assign toll_meta.toll;
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_accnt_bal_reg.read(meta.toll_meta.bal, (bit<32>)hdr.pos_report.vid); *)
        assign meta.toll_meta.bal @@ badd (var meta.toll_meta.bal) @@ bcast 32 @@ var meta.toll_meta.toll;
        assert_ @@ eq_ btrue @@ var hdr.pos_report.isValid;
        (* v_accnt_bal_reg.write((bit<32>)hdr.pos_report.vid, (bit<32>)meta.toll_meta.bal); *)
    ]
  in
  let check_toll =
    instr_table ("check_toll",
                [`Exact meta.v_state.new_seg;
                 `MaskableDegen meta.seg_meta.ewma_spd;
                 `MaskableDegen meta.seg_meta.vol;
                 `MaskableDegen meta.accident_meta.has_accident_ahead
                ],
                [issue_toll])
  in
  let do_load_accnt_bal = [], Action.[
      assert_ @@ eq_ btrue @@ var hdr.accnt_bal_req.isValid;
      (* v_accnt_bal_reg.read(meta.toll_meta.bal, (bit<32>)hdr.accnt_bal_req.vid); *)
    ]
  in
  let load_accnt_bal =
    instr_table ("load_accnt_bal",
                 [],
                 [do_load_accnt_bal]
                )
  in
  let set_nhop =
    let nhop_ipv4 = Var.make "nhop_ipv4" 32 in
    let port = Var.make "port" 9 in
    [nhop_ipv4; port], Action.[
        assign hdr.ipv4.dstAddr @@ var nhop_ipv4;
        assign standard_metadata.egress_spec @@ var port
    ]
  in
  let _drop =
    [], Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9;
      ]
  in
  let ipv4_lpm =
    instr_table ("ipv4_lpm",
                [`Maskable hdr.ipv4.dstAddr],
                [set_nhop; _drop])
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [dmac], Action.[
      assign hdr.ethernet.dstAddr @@ var dmac
    ]
  in
  let forward =
    instr_table ("forward",
                 [`Exact hdr.ipv4.dstAddr],
                 [set_dmac; _drop]
                )
  in
  ifte_seq (eq_ btrue @@ var hdr.ipv4.isValid) [
    ifte_seq (eq_ btrue @@ var hdr.pos_report.isValid) [
      update_pos_state;
      ifte_seq (ors_ [eq_ btrue @@ var meta.v_state.new_;
                      not_ @@ eq_ (var meta.v_state.prev_seg) (var pos_report.seg)
                     ])[
        update_new_seg
      ] [];
      update_vol_state;
      update_ewma_spd;
      ifte (ands_[
          eq_ (var hdr.pos_report.xway) (var meta.v_state.prev_xway);
          eq_ (var hdr.pos_report.seg) (var meta.v_state.prev_seg);
          eq_ (var hdr.pos_report.dir) (bcast 8 @@ var meta.v_state.prev_dir);
          eq_ (var hdr.pos_report.lane) (bcast 8 @@ var meta.v_state.prev_lane);
        ])
        loc_not_changed
        loc_changed;
      ifte (ands_ [
          eq_ (var meta.v_state.prev_nomove_cnt) (bvi 3 3);
          ult_ (var meta.v_state.nomove_cnt) (bvi 3 3)])
        dec_prev_stopped
        skip;
      ifte (ands_ [
          ult_ (var meta.v_state.prev_nomove_cnt) (bvi 3 3);
          eq_ (var meta.v_state.nomove_cnt) (bvi 3 3)])
        inc_stopped
        skip;
      load_stopped_ahead;
      (* check_accidents??? *)
      check_toll;
    ] [
      ifte_seq (eq_ btrue @@ var hdr.accnt_bal_req.isValid) [
        load_accnt_bal
      ] []
    ];
    ipv4_lpm;
    forward
  ] []

let linearroad_egress =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let open Primitives in
  let accident_alert_e2e =
    [], Action.[
        assign meta.accident_egress_meta.recirculate @@ bvi 1 1;
        (* clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.accident_meta, meta.accident_egress_meta }); *)
      ]
  in
  let make_accident_alert =
    [], Action.[
        assign hdr.lr_msg_type.msg_type @@ bvi 11 8;
        assign hdr.accident_alert.isValid btrue;
        assign hdr.accident_alert.time @@ var hdr.pos_report.time;
        assign hdr.accident_alert.vid @@ var hdr.pos_report.vid;
        assign hdr.accident_alert.seg @@ var meta.accident_meta.accident_seg;
        assign hdr.pos_report.isValid @@ bfalse;
        assign hdr.ipv4.totalLen @@ bvi 38 16;
        assign hdr.udp.length @@ bvi 18 16;
        assign hdr.udp.checksum @@ bvi 0 16;
      ]
  in
  let send_accident_alert =
    instr_table ("send_accident_alert",
                [`Exact meta.accident_meta.has_accident_ahead;
                 `Exact meta.accident_egress_meta.recirculate ],
                [ accident_alert_e2e; make_accident_alert ])
  in
  let toll_notification_e2e =
    [], Action.[
        assign meta.toll_egress_meta.recirculate @@ bvi 1 1;
        (* clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.toll_meta, meta.toll_egress_meta, meta.seg_meta }); *)
      ]
  in
  let make_toll_notification =
    [], Action.[
        assign hdr.lr_msg_type.msg_type @@ bvi 10 8;
        assign hdr.toll_notification.isValid btrue;
        assign hdr.toll_notification.time @@ var hdr.pos_report.time;
        assign hdr.toll_notification.vid @@ var hdr.pos_report.vid;
        assign hdr.toll_notification.spd @@ bcast 8 @@ var meta.seg_meta.ewma_spd;
        assign hdr.toll_notification.toll @@ var meta.toll_meta.toll;
        assign hdr.pos_report.isValid bfalse;
        assign hdr.ipv4.totalLen @@ bvi 50 16;
        assign hdr.udp.length @@ bvi 20 16;
        assign hdr.udp.checksum @@ bvi 0 16;
      ]
  in
  let send_toll_notification =
    instr_table ("send_toll_notification",
                [`Exact meta.toll_meta.has_toll;
                 `Exact meta.toll_egress_meta.recirculate],
                [toll_notification_e2e; make_toll_notification])
  in
  let accnt_bal_e2e =
    [], Action.[
        assign meta.accnt_bal_egress_meta.recirculate @@ bvi 1 1;
        (* clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.toll_meta, meta.accnt_bal_egress_meta }); *)
      ]
  in
  let make_accnt_bal =
    [], Action.[
        assign hdr.lr_msg_type.msg_type @@ bvi 12 8;
        assign hdr.accnt_bal.isValid btrue;
        assign hdr.accnt_bal.time @@ var hdr.accnt_bal_req.time;
        assign hdr.accnt_bal.vid @@ var hdr.accnt_bal_req.vid;
        assign hdr.accnt_bal.qid @@ var hdr.accnt_bal_req.qid;
        assign hdr.accnt_bal.bal @@ var meta.toll_meta.bal;
        assign hdr.accnt_bal_req.isValid bfalse;
        assign hdr.ipv4.totalLen @@ bvi 45 16;
        assign hdr.udp.length @@ bvi 25 16;
        assign hdr.udp.checksum @@ bvi 0 16;
      ]
  in
  let send_accnt_bal =
    instr_table ("send_accnt_bal",
                [`Exact meta.accnt_bal_egress_meta.recirculate],
                [accnt_bal_e2e; make_accnt_bal])
  in
  let make_expenditure_report =
    let bal = Var.make "bal" 16 in
    [bal], Action.[
        assign hdr.lr_msg_type.msg_type @@ bvi 13 8;
        assign hdr.expenditure_report.isValid btrue;
        assign hdr.expenditure_report.time @@ var hdr.expenditure_req.time;
        assign hdr.expenditure_report.emit @@ var hdr.expenditure_req.time;
        assign hdr.expenditure_report.qid @@ var hdr.expenditure_req.qid;
        assign hdr.expenditure_report.bal @@ var bal;
        assign hdr.expenditure_req.isValid bfalse;
        assign hdr.ipv4.totalLen @@ bvi 39 16;
        assign hdr.udp.length @@ bvi 19 16;
        assign hdr.udp.checksum @@ bvi 0 16;
    ]
  in
  let daily_expenditure =
    instr_table ("daily_expenditure",
                [`Exact hdr.expenditure_req.vid;
                 `Exact hdr.expenditure_req.day;
                 `Exact hdr.expenditure_req.xway
                ],
                [make_expenditure_report])
  in
  let do_travel_estimate_init =
    [],
    Action.[
      assign meta.te_md.dir @@ bvi 0 1;
      assign meta.te_md.seg_cur @@ var hdr.travel_estimate_req.seg_init;
      assign meta.te_md.seg_end @@ var hdr.travel_estimate_req.seg_end;
    ]
  in
  let travel_estimate_init =
    instr_table ("travel_estimate_init",
                [],
                [do_travel_estimate_init])
  in
  let do_travel_estimate_init_rev =
    [], Action.[
      assign meta.te_md.dir @@ bvi 1 1;
      assign meta.te_md.seg_cur @@ var hdr.travel_estimate_req.seg_end;
      assign meta.te_md.seg_end @@ var hdr.travel_estimate_req.seg_init;
    ]
  in
  let travel_estimate_init_rev =
    instr_table ("travel_estimate_init_rev",
                 [],
                 [do_travel_estimate_init_rev]
                )
  in
  let update_travel_estimate =
    let time = Var.make "time" 16 in
    let toll = Var.make "toll" 16 in
    [time; toll], Action.[
        assign meta.te_md.time_sum @@ badd (var meta.te_md.time_sum) (var time);
        assign meta.te_md.toll_sum @@ badd (var meta.te_md.toll_sum) (var toll);
      ]
  in
  let travel_estimate_history =
    instr_table ("travel_estimate_history",
                [`Exact hdr.travel_estimate_req.dow;
                 `Exact hdr.travel_estimate_req.tod;
                 `Exact hdr.travel_estimate_req.xway;
                 `Exact meta.te_md.dir;
                 `Exact meta.te_md.seg_cur
                ],
                [update_travel_estimate])
  in
  let do_travel_estimate_send = [], Action.[
      assign hdr.lr_msg_type.msg_type @@ bvi 14 8;
      assign hdr.travel_estimate.isValid btrue;
      assign hdr.travel_estimate.qid @@ var hdr.travel_estimate_req.qid;
      assign hdr.travel_estimate.travel_time @@ var meta.te_md.time_sum;
      assign hdr.travel_estimate.toll @@ var meta.te_md.toll_sum;
      assign hdr.travel_estimate_req.isValid bfalse;
      assign hdr.ipv4.totalLen @@ bvi 37 16;
      assign hdr.udp.length @@ bvi 16 16;
      assign hdr.udp.checksum @@ bvi 0 16
    ]
  in
  let travel_estimate_send =
    instr_table("travel_estimate_send",
               [],
               [do_travel_estimate_send])
  in
  let travel_estimate_e2e =
    let mir_ses = Var.make "mir_ses" 32 in
    [mir_ses], Action.[
        assign meta.te_md.seg_cur @@ badd (var meta.te_md.seg_cur) (bvi 1 8);
        assign meta.te_md.recirculated btrue;
        (* clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.te_md }); *)
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let travel_estimate_recirc =
    instr_table("travel_estimate_recirc",
                [],
                [travel_estimate_e2e])
  in
  let rewrite_mac =
    let smac = Var.make "smac" 48 in
    [smac], Action.[
      assign hdr.ethernet.srcAddr @@ var smac
    ]
  in
  let _drop =
    [], Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let send_frame =
    instr_table("send_frame",
                [`Exact standard_metadata.egress_port],
                [rewrite_mac; _drop]
               )
  in
  ifte_seq (eq_ btrue @@ var hdr.ipv4.isValid) [
    ifte_seq (eq_ btrue @@ var hdr.pos_report.isValid) [
      send_accident_alert;
      send_toll_notification
    ] [
      ifte_seq (eq_ btrue @@ var hdr.accnt_bal_req.isValid) [
        send_accnt_bal
      ] [
        ifte_seq (eq_ btrue @@ var hdr.expenditure_req.isValid) [
          daily_expenditure
        ] [
          ifte_seq (eq_ btrue @@ var hdr.travel_estimate_req.isValid) [
            ifte_seq (eq_ (bvi 0 1) @@ var meta.te_md.recirculated) [
              ifte (ult_ (var hdr.travel_estimate_req.seg_init) (var hdr.travel_estimate_req.seg_end))
                travel_estimate_init
                travel_estimate_init_rev
            ] [];
            travel_estimate_history;
            ifte (eq_ (var meta.te_md.seg_cur) (var meta.te_md.seg_end))
              travel_estimate_send
              travel_estimate_recirc
          ][]
        ]
      ]
    ];
    send_frame
  ][]

let linearroad fixed =
  pipeline linearroad_parser (linearroad_ingress fixed) linearroad_egress
  |> HoareNet.assert_valids

let test_assert_valids_travel_estimate_send () =
  let open BExpr in
  let open Expr in
  let do_travel_estimate_send = ([], Primitives.Action.[
      assign hdr.lr_msg_type.msg_type @@ bvi 14 8;
      assign hdr.travel_estimate.isValid btrue;
      assign hdr.travel_estimate.qid @@ var hdr.travel_estimate_req.qid;
      assign hdr.travel_estimate.travel_time @@ var meta.te_md.time_sum;
      assign hdr.travel_estimate.toll @@ var meta.te_md.toll_sum;
      assign hdr.travel_estimate_req.isValid bfalse;
      assign hdr.ipv4.totalLen @@ bvi 37 16;
      assign hdr.udp.length @@ bvi 16 16;
      assign hdr.udp.checksum @@ bvi 0 16
    ])
  in
  let travel_estimate_send =
    HoareNet.instr_table("travel_estimate_send",
               [],
               [do_travel_estimate_send])
  in
  let travel_estimate_send_annotated =
  let do_travel_estimate_send = [], Primitives.Action.[
      assert_ @@ eq_ btrue @@ var hdr.lr_msg_type.isValid;
      assign hdr.lr_msg_type.msg_type @@ bvi 14 8;
      assign hdr.travel_estimate.isValid btrue;
      assert_ @@ eq_ btrue @@ var hdr.travel_estimate.isValid;
      assert_ @@ eq_ btrue @@ var hdr.travel_estimate_req.isValid;
      assign hdr.travel_estimate.qid @@ var hdr.travel_estimate_req.qid;
      assert_ @@ eq_ btrue @@ var hdr.travel_estimate.isValid;
      assign hdr.travel_estimate.travel_time @@ var meta.te_md.time_sum;
      assert_ @@ eq_ btrue @@ var hdr.travel_estimate.isValid;
      assign hdr.travel_estimate.toll @@ var meta.te_md.toll_sum;
      assign hdr.travel_estimate_req.isValid bfalse;
      assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid;
      assign hdr.ipv4.totalLen @@ bvi 37 16;
      assert_ @@ eq_ btrue @@ var hdr.udp.isValid;
      assign hdr.udp.length @@ bvi 16 16;
      assert_ @@ eq_ btrue @@ var hdr.udp.isValid;
      assign hdr.udp.checksum @@ bvi 0 16
    ]
  in
  HoareNet.instr_table
      ("travel_estimate_send",
       [], [do_travel_estimate_send])
  in
  travel_estimate_send
  |> HoareNet.assert_valids
  |> HoareNet.safe_to_gpl_exn
  |> Alcotest.(check Equivalences.gpl)
    "equivalent programs"
    (HoareNet.safe_to_gpl_exn travel_estimate_send_annotated)


let tricky_path_solves () =
  let open ASTs in
  let open GCL in
  let open BExpr in
  let open Expr in
  let tricky_path =
    sequence [
     assign zombie.parse_result @@ bvi 0 1;
     assign hdr.accident_alert.isValid @@ bvi 0 1;
     assign hdr.accnt_bal.isValid @@ bvi 0 1;
     assign hdr.accnt_bal_req.isValid @@ bvi 0 1;
     assign hdr.ethernet.isValid @@ bvi 0 1;
     assign hdr.expenditure_report.isValid @@ bvi 0 1;
     assign hdr.expenditure_req.isValid @@ bvi 0 1;
     assign hdr.ipv4.isValid @@ bvi 0 1;
     assign hdr.lr_msg_type.isValid @@ bvi 0 1;
     assign hdr.pos_report.isValid @@ bvi 0 1;
     assign hdr.toll_notification.isValid @@ bvi 0 1;
     assign hdr.travel_estimate.isValid @@ bvi 0 1;
     assign hdr.travel_estimate_req.isValid @@ bvi 0 1;
     assign hdr.udp.isValid @@ bvi 0 1;
     assign hdr.ethernet.isValid @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ethernet.isValid;
     assume  @@ eq_ (bvi 2048 16) @@ var hdr.ethernet.etherType;
     assign hdr.ipv4.isValid @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assume @@ eq_ (bvi 17 8) @@ var hdr.ipv4.protocol;
     assign hdr.udp.isValid @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.udp.isValid;
     assume @@ eq_ (bvi 4660 16) @@ var hdr.udp.dstPort;
     assign hdr.lr_msg_type.isValid @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.lr_msg_type.isValid;
     assume @@ eq_ (bvi 0 8) @@ var hdr.lr_msg_type.msg_type;
     assign hdr.pos_report.isValid @@ bvi 1 1;
     assign zombie.parse_result @@ bvi 1 1;
     assume @@ eq_ (var zombie.parse_result) @@ bvi 1 1;
     assume @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assume @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assume (uge_ (var @@ Var.make "_symb$update_pos_state$action" 1) @@ bvi 0 1);
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign meta.v_state.new_ @@ bnot @@ var meta.v_state.new_;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assume @@ not_ @@ ors_ [
                  (not_ (eq_ (var meta.v_state.prev_seg) (var hdr.pos_report.seg)));
                  (eq_ (bvi 1 1) (var meta.v_state.new_))];
     assume @@ eq_ (var @@ Var.make "_symb$update_vol_state$match_0" 1) (var meta.v_state.new_);
     assume @@ eq_ (var @@ Var.make "_symb$update_vol_state$match_1" 1) (var meta.v_state.new_seg);
     assume @@ eq_ (var @@ Var.make "_symb$update_vol_state$action" 2) (bvi 0 2);
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign meta.seg_meta.vol @@ badd (var meta.seg_meta.vol) (bvi 1 8);
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign meta.seg_meta.prev_vol @@ bsub (var meta.seg_meta.prev_vol) (bvi 1 8);
     assume @@ eq_ (var @@ Var.make "_symb$update_ewma_spd$match_0" 8) (var meta.seg_meta.vol);
     assume @@ eq_ (var @@ Var.make "_symb$update_ewma_spd$action" 1) (bvi 0 1);
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign meta.seg_meta.ewma_spd @@ (* var @@ Var.make "ABSTRACT" 16; *)
     bslice 0 15 @@ badd (bmul (bconcat (bvi 0 16) @@ var meta.seg_meta.ewma_spd) (bvi 96 32)) (bconcat (bvi 0 16) (lshr_ (bmul (bconcat (bvi 0 8) (var hdr.pos_report.spd)) (bvi 32 16)) (bvi 7 16)));
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assume @@ not_ @@ ands_ [
       eq_ (var hdr.pos_report.xway) @@ var meta.v_state.prev_xway;
       eq_ (var hdr.pos_report.seg) @@ var meta.v_state.prev_seg;
       eq_ (var hdr.pos_report.dir) @@ bconcat (bvi 0 7) @@ var meta.v_state.prev_dir;
       eq_ (var hdr.pos_report.lane) @@ bconcat (bvi 0 5) @@ var meta.v_state.prev_lane];
     assume @@ uge_ (var @@ Var.make "_symb$loc_changed$action" 1) @@ bvi 0 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assume @@ not_ @@ ands_ [
       eq_ (var meta.v_state.prev_nomove_cnt) (bvi 3 3);
       ult_ (var meta.v_state.nomove_cnt) (bvi 3 3)];
     assume @@ not_ @@ ands_ [
       ult_ (var meta.v_state.prev_nomove_cnt) (bvi 3 3);
       eq_ (var meta.v_state.nomove_cnt) @@ bvi 3 3];
     assume @@ uge_ (var @@ Var.make "_symb$load_stopped_ahead$action" 1) @@ bvi 0 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign meta.stopped_ahead.seg0_ord @@ bor (var meta.stopped_ahead.seg0l1) @@ bor (var meta.stopped_ahead.seg0l2) @@ var meta.stopped_ahead.seg0l3;
     assign meta.stopped_ahead.seg1_ord @@ bor (var meta.stopped_ahead.seg1l1) @@ bor (var meta.stopped_ahead.seg1l2) @@ var meta.stopped_ahead.seg1l3;
     assign meta.stopped_ahead.seg2_ord @@ bor (var meta.stopped_ahead.seg2l1) @@ bor (var meta.stopped_ahead.seg2l2) @@ var meta.stopped_ahead.seg2l3;
     assign meta.stopped_ahead.seg3_ord @@ bor (var meta.stopped_ahead.seg3l1) @@ bor (var meta.stopped_ahead.seg3l2) @@ var meta.stopped_ahead.seg3l3;
     assign meta.stopped_ahead.seg4_ord @@ bor (var meta.stopped_ahead.seg4l1) @@ bor (var meta.stopped_ahead.seg4l2) @@ var meta.stopped_ahead.seg4l3;
     assume @@ eq_ (var @@ Var.make "_symb$check_toll$match_0" 1) @@ var meta.v_state.new_seg;
     assume @@ eq_ (var @@ Var.make "_symb$check_toll$match_1" 16) @@ var meta.seg_meta.ewma_spd;
     assume @@ eq_ (var @@ Var.make "_symb$check_toll$match_2" 8) @@ var meta.seg_meta.vol;
     assume @@ eq_ (var @@ Var.make "_symb$check_toll$match_3" 1) @@ var meta.accident_meta.has_accident_ahead;
     assume @@ uge_ (var @@ Var.make "_symb$check_toll$action" 1) @@ bvi 0 1;
     assign meta.toll_meta.has_toll @@ bvi 1 1;
     assign meta.toll_meta.toll @@ bmul (var @@ Var.make "_symb$check_toll$0$base_toll" 16)
       (bmul (bsub (bconcat (bvi 0 8) (var meta.seg_meta.vol)) (bvi 50 16)) (bsub (bconcat (bvi 0 8) (var meta.seg_meta.vol)) @@ bvi 50 16));
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign meta.toll_meta.bal @@ badd (var meta.toll_meta.bal) @@ bconcat (bvi 0 16) @@ var meta.toll_meta.toll;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assume @@ not_ @@ eq_ (bvi 1 1) @@ var @@ Var.make "_symb$ipv4_lpm$match_0$DONT_CARE" 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assume @@ eq_ (var @@ Var.make "_symb$ipv4_lpm$match_0" 32) @@ (var hdr.ipv4.dstAddr);
     assume @@ uge_ (var @@ Var.make "_symb$ipv4_lpm$action" 1) @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assign hdr.ipv4.dstAddr @@ var @@ Var.make "_symb$ipv4_lpm$1$nhop_ipv4" 32;
     assign standard_metadata.egress_spec @@ var @@ Var.make "_symb$ipv4_lpm$1$port" 9;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assume @@ eq_ (var @@ Var.make "_symb$forward$match_0" 32) @@ var hdr.ipv4.dstAddr;
     assume @@ uge_ (var @@ Var.make "_symb$forward$action" 1) @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ethernet.isValid;
     assign hdr.ethernet.dstAddr @@ var @@ Var.make "_symb$forward$1$dmac" 48;
     assume @@ not_  @@ eq_ (var standard_metadata.egress_spec) (bvi 511 9);
     assign standard_metadata.egress_port @@ var standard_metadata.egress_spec;
     assume @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assume @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assume @@ eq_ (var @@ Var.make "_symb$send_accident_alert$match_0" 1) @@ var meta.accident_meta.has_accident_ahead;
     assume @@ eq_ (var @@ Var.make "_symb$send_accident_alert$match_1" 1) @@ var meta.accident_egress_meta.recirculate;
     assume @@ eq_ (var @@ Var.make "_symb$send_accident_alert$action" 1) @@ bvi 0 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.lr_msg_type.isValid;
     assign hdr.lr_msg_type.msg_type @@ bvi 11 8;
     assign hdr.accident_alert.isValid @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.accident_alert.isValid;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign hdr.accident_alert.time @@ var hdr.pos_report.time;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.accident_alert.isValid;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign hdr.accident_alert.vid @@ var hdr.pos_report.vid;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.accident_alert.isValid;
     assign hdr.accident_alert.seg @@ var meta.accident_meta.accident_seg;
     assign hdr.pos_report.isValid @@ bvi 0 1;  (*The offending assignment*)
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assign hdr.ipv4.totalLen @@ bvi 38 16;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.udp.isValid;
     assign hdr.udp.length @@ bvi 18 16;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.udp.isValid;
     assign hdr.udp.checksum @@ bvi 0 16;
     assume @@ eq_ (var @@ Var.make "_symb$send_toll_notification$match_0" 1) @@ var meta.toll_meta.has_toll;
     assume @@ eq_ (var @@ Var.make "_symb$send_toll_notification$match_1" 1) @@ var meta.toll_egress_meta.recirculate;
     assume @@ eq_ (var @@ Var.make "_symb$send_toll_notification$action" 1) @@ bvi 0 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.lr_msg_type.isValid;
     assign hdr.lr_msg_type.msg_type @@ bvi 10 8;
     assign hdr.toll_notification.isValid @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.toll_notification.isValid;
     (* THE NEXT LINE IS THE OFFENDING ASSERTION *)
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign hdr.toll_notification.time @@ var hdr.pos_report.time;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.toll_notification.isValid;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.pos_report.isValid;
     assign hdr.toll_notification.vid @@ var hdr.pos_report.vid;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.toll_notification.isValid;
     assign hdr.toll_notification.spd @@ bslice 0 7 @@ var meta.seg_meta.ewma_spd;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.toll_notification.isValid;
     assign hdr.toll_notification.toll @@ var meta.toll_meta.toll;
     assign hdr.pos_report.isValid @@ bvi 0 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ipv4.isValid;
     assign hdr.ipv4.totalLen @@ bvi 50 16;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.udp.isValid;
     assign hdr.udp.length @@ bvi 20 16;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.udp.isValid;
     assign hdr.udp.checksum @@ bvi 0 16;
     assume @@ eq_ (var @@ Var.make "_symb$send_frame$match_0" 9) @@ var standard_metadata.egress_port;
     assume @@ uge_ (var @@ Var.make "_symb$send_fr ame$action" 1) @@ bvi 1 1;
     assert_ @@ eq_ (bvi 1 1) @@ var hdr.ethernet.isValid;
     assign hdr.ethernet.srcAddr @@ var @@ Var.make "_symb$send_frame$1$smac" 48
   ]
  in
  let assert_normalized = GCL.single_assert_nf tricky_path in
  let solve path =
    let path = GCL.simplify_path path in
    let pi_vc = Psv.(vc @@ snd @@ passify path) in
    match
      Qe.orelse ~input:pi_vc
        [Qe.solve_one ~qe:Qe.nikolaj_please;
         Qe.solve_one ~qe:Qe.abstract_expressionism;
         (* Qe.solve_one ~qe:BottomUpQe.cnf_qe *)
        ]
    with
    | None -> Alcotest.fail "QE failed"
    | Some (cvs, cpf_str) ->
      Solver.of_smtlib ~dvs:[] ~cvs cpf_str
  in
  let solutions = List.map ~f:solve assert_normalized in
  BExpr.ands_ solutions
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is satisfiable"
    BExpr.false_



let test_annotations () =
  HoareNet.check_annotations (linearroad true)
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer_timeout () =
  HoareNet.infer ~qe:`Enum (linearroad true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc (linearroad true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Conc CPI is trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "tricky path is eliminated" `Quick tricky_path_solves;
  Alcotest.test_case "Validity Assert_s are Correct" `Quick test_assert_valids_travel_estimate_send;
  Alcotest.test_case "Linearroad annotations" `Quick test_annotations;
  Alcotest.test_case "Linearroad infer enum unannotated" `Slow test_infer_timeout;
  Alcotest.test_case "Linearroad infer concolic" `Quick test_concolic;
]
