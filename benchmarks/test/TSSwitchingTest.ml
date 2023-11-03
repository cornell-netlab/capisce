open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

let ts_switching_parser =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let parse_rtp =
    sequence [
      assign hdr.rtp.isValid btrue;
      transition_accept
    ]
  in
  let parse_udp =
    sequence [
      assign hdr.udp.isValid btrue;
      parse_rtp;
    ]
  in
  let parse_ipv4 =
    sequence [
        assign hdr.ipv4.isValid btrue;
        ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 17 8))
          [ parse_udp ]
          [ transition_accept ];
        transition_accept
      ]
  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      ifte_seq (eq_ (var hdr.ethernet.etherType) (bvi 2048 16))
        [parse_ipv4]
        [transition_accept]
    ]

  in
  let start =
    sequence [
      assign hdr.ethernet.isValid bfalse;
      assign hdr.ipv4.isValid bfalse;
      assign hdr.udp.isValid bfalse;
      assign hdr.rtp.isValid bfalse;
      parse_ethernet
    ]
  in
  start

let ts_switching_ingress fixed =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let _drop_0 = [], Primitives.Action.[
      (* my_direct_counter.count() *)
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let take_video_0 =
    let dst_ip = Var.make "dst_ip" 32 in
    [], Primitives.Action.[
        (* my_direct_counter.count() *)
        assign standard_metadata.egress_spec @@ bvi 1 9;
        assign hdr.ipv4.dstAddr @@ var dst_ip
      ]
  in
  let schedule_table =
    instr_table ("schedule_table",
          [ 
            `Exact hdr.ipv4.dstAddr;
            `Maskable hdr.rtp.timestamp
          ], [
            take_video_0; _drop_0;
            nop (*Unspecified default action, assuming nop*)
          ])
  in
  sequence [
    if fixed then assume @@ ands_ [
        eq_ btrue @@ var hdr.ipv4.isValid;
        eq_ btrue @@ var hdr.rtp.isValid;
      ]
    else skip;
    schedule_table
  ]


let ts_switching_egress =
  (* HoareNet.skip *)
  let open HoareNet in
  (* let open BExpr in *)
  skip

let ts_switching fixed =
  pipeline ts_switching_parser (ts_switching_ingress fixed) ts_switching_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations (ts_switching false)
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer_buggy () =
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (ts_switching false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (ts_switching true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (ts_switching false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (ts_switching true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Conc CPI is trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "ts_switching annotations" `Quick test_annotations;
  Alcotest.test_case "ts_switching infer enum buggy" `Quick test_infer_buggy;
  Alcotest.test_case "ts_switching infer enum fixed" `Quick test_infer_fixed;
  Alcotest.test_case "ts_switching infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "ts_switching infer conc fixed" `Quick test_concolic_fixed;
]
