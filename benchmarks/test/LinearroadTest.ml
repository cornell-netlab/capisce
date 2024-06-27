open Core
open Pbench
open DependentTypeChecker
open Programs.V1ModelUtils
open Programs.Linearroad

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
     (* assign meta.seg_meta.ewma_spd @@ (\* var @@ Var.make "ABSTRACT" 16; *\) *)
     (* bslice 0 15 @@ badd (bmul (bconcat (bvi 0 16) @@ var meta.seg_meta.ewma_spd) (bvi 96 32)) (bconcat (bvi 0 16) (lshr_ (bmul (bconcat (bvi 0 8) (var hdr.pos_report.spd)) (bvi 32 16)) (bvi 7 16))); *)
     (* the eliminated form using ICs *)
     assume @@ eq_ (var meta.seg_meta.ewma_spd) @@ band (bvi 65504 16) @@ var meta.seg_meta.ewma_spd;
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
     assume @@ uge_ (var @@ Var.make "_symb$send_frame$action" 1) @@ bvi 1 1;
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
        [Qe.solve_one_option ~qe:(Qe.nikolaj_please);
         (* Qe.solve_one ~qe:BottomUpQe.cnf_qe *)
        ]
    with
    | None -> Alcotest.fail "QE failed"
    | Some cpf -> cpf
  in
  let solutions = List.map ~f:solve assert_normalized in
  BExpr.ands_ solutions
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is satisfiable"
    BExpr.false_

let true_path_resolves () =
  let open ASTs in
  let open GCL in
  let open BExpr in
  let open Expr in
  let path =
    sequence [
      assume (eq_ (bvi 2048 16) @@ var hdr.ethernet.etherType);
      assume (eq_ (bvi 17 8) @@ var hdr.ipv4.protocol);
      assume (eq_ (bvi 4660 16) @@ var hdr.udp.dstPort);
      assume (eq_ (bvi 0 8) @@ var hdr.lr_msg_type.msg_type);
      assume (uge_ (var @@ Var.make "_symb$update_pos_state$action" 1) (bvi 0 1));
      assign meta.v_state.new_ (bnot (var meta.v_state.new_));
      assume (or_
                (not_    (eq_ (var meta.v_state.prev_seg) @@ var hdr.pos_report.seg))
                (eq_ (bvi 1 1) @@ var meta.v_state.new_));
      assume (uge_ (var @@ Var.make "_symb$update_new_seg$action" 1) (bvi 0 1));
      assume (eq_ (var @@ Var.make "_symb$update_vol_state$match_0" 1) @@ var meta.v_state.new_);
      assume (eq_ (var @@ Var.make "_symb$update_vol_state$match_1" 1) (bvi 1 1));
      assume (uge_ (var @@ Var.make "_symb$update_vol_state$action" 2) (bvi 2 2));
      assume (eq_ (var @@ Var.make "_symb$update_ewma_spd$match_0" 8) @@ var meta.seg_meta.vol);
      assume (uge_ (var @@ Var.make "_symb$update_ewma_spd$action" 1) (bvi 1 1));
      assign meta.seg_meta.ewma_spd (bconcat (bvi 0 8) @@ var hdr.pos_report.spd);
      assume (not_  (ands_ [
          (eq_ (var hdr.pos_report.xway) (var meta.v_state.prev_xway));
          (eq_ (var hdr.pos_report.seg) (var meta.v_state.prev_seg));
          (eq_ (var hdr.pos_report.dir) (bconcat (bvi 0 7) @@ var meta.v_state.prev_dir));
          (eq_ (var hdr.pos_report.lane) (bconcat (bvi 0 5) @@ var meta.v_state.prev_lane))]));
      assume (uge_ (var @@ Var.make "_symb$loc_changed$action" 1) (bvi 0 1));
      assume (not_  (and_
                       (eq_ (var meta.v_state.prev_nomove_cnt) (bvi 3 3))
                       (ult_ (var meta.v_state.nomove_cnt) (bvi 3 3))));
      assume (not_  (and_
                       (ult_ (var meta.v_state.prev_nomove_cnt) (bvi 3 3))
                       (eq_ (var meta.v_state.nomove_cnt) (bvi 3 3))));
      assume (uge_ (var @@ Var.make "_symb$load_stopped_ahead$action" 1) (bvi 0 1));
      assume (eq_ (var @@ Var.make "_symb$check_toll$match_0" 1) (bvi 1 1));
      assume (eq_ (var @@ Var.make "_symb$check_toll$match_1" 16) @@ var meta.seg_meta.ewma_spd);
      assume (eq_ (var @@ Var.make "_symb$check_toll$match_2" 8) @@ var meta.seg_meta.vol);
      assume (eq_ (var @@ Var.make "_symb$check_toll$match_3" 1) @@ var meta.accident_meta.has_accident_ahead);
      assume (uge_ (var @@ Var.make "_symb$check_toll$action" 1) (bvi 0 1));
      assume (eq_ (bvi 1 1) @@ var @@ Var.make "_symb$ipv4_lpm$match_0$DONT_CARE" 1);
      assume (uge_ (var @@ Var.make "_symb$ipv4_lpm$action" 1) (bvi 1 1));
      assign hdr.ipv4.dstAddr @@ var @@ Var.make "_symb$ipv4_lpm$1$nhop_ipv4" 32;
      assign standard_metadata.egress_spec @@ var @@ Var.make "_symb$ipv4_lpm$1$port" 9;
      assume (eq_ (var @@ Var.make "_symb$forward$match_0" 32) @@ var hdr.ipv4.dstAddr);
      assume (uge_ (var @@ Var.make "_symb$forward$action" 1) (bvi 1 1));
      assume (not_  (eq_ (var @@ Var.make "standard_metadata.egress_spec" 9) (bvi 511 9)));
      assign standard_metadata.egress_port (var standard_metadata.egress_spec);
      assume (eq_ (var @@ Var.make "_symb$send_accident_alert$match_0" 1) @@ var meta.accident_meta.has_accident_ahead);
      assume (eq_ (var @@ Var.make "_symb$send_accident_alert$match_1" 1) @@ var meta.accident_egress_meta.recirculate);
      assume (eq_ (var @@ Var.make "_symb$send_accident_alert$action" 1) (bvi 0 1));
      assume (eq_ (var @@ Var.make "_symb$send_toll_notification$match_0" 1) (bvi 1 1));
      assume (eq_ (var @@ Var.make "_symb$send_toll_notification$match_1" 1) @@ var meta.toll_egress_meta.recirculate);
      assume (eq_ (var @@ Var.make "_symb$send_toll_notification$action" 1) (bvi 0 1));
      assert_ false_;
      (* assume (eq_ _symb$send_frame$match_0 standard_metadata.egress_port); *)
      (* assume (uge_ _symb$send_frame$action (bvi 1 1)) *)
    ]
  in
  let assert_normalized = GCL.single_assert_nf path in
  let solve path =
    let path = GCL.simplify_path path in
    let pi_vc = Psv.(vc @@ snd @@ passify path) in
    match
      Qe.orelse ~input:pi_vc
        [Qe.solve_one_option ~qe:(Qe.nikolaj_please);
         (* Qe.solve_one ~qe:Qe.abstract_expressionism; *)
         Qe.solve_one_option ~qe:BottomUpQe.cnf_qe_result
        ]
    with
    | None -> Alcotest.fail "QE failed"
    | Some cpf -> cpf     
  in
  let solutions = List.map ~f:solve assert_normalized in
  BExpr.ands_ solutions
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is not trivial"
    BExpr.true_

let paths () = 
  HoareNet.annotated_to_gpl (linearroad true)
  |> ASTs.GPL.count_paths
  |> Bigint.to_string
  |> Alcotest.(check string) "equal" ""

let test_annotations () =
  HoareNet.check_annotations (linearroad true)
  |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer_timeout () =
  HoareNet.infer ~qe:`Enum (linearroad true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is not trivial"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc (linearroad true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is not trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "has some paths" `Quick paths;
  Alcotest.test_case "tricky path is eliminated" `Quick tricky_path_solves;
  Alcotest.test_case "true path is not true" `Quick true_path_resolves;
  Alcotest.test_case "Linearroad infer enum unannotated" `Slow test_infer_timeout;
  Alcotest.test_case "Linearroad infer concolic with annotation" `Quick test_concolic;
]
