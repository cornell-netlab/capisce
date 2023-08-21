open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type intrinsic_metadata_t = {
  mcast_grp : Var.t;
  egress_rid : Var.t
}

let intrinsic_metadata : intrinsic_metadata_t = {
  mcast_grp = Var.make "meta.intrinsic_metadata.mcast_grp" 16;
  egress_rid = Var.make "meta.intrinsic_metadata.egress_rid" 16;
}

type meta_t =  {
  intrinsic_metadata : intrinsic_metadata_t
}

let meta : meta_t = {intrinsic_metadata}

let mc_nat_parser =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let parse_udp =
    sequence [
      assign hdr.udp.isValid btrue;
      transition_accept
    ]
  in
  let parse_ipv4 =
    sequence [
        assign hdr.ipv4.isValid btrue;
        (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
        ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 17 8))
          [ parse_udp ]
          [ transition_accept ];
        transition_accept
      ]
  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
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
      parse_ethernet
    ]
  in
  start

let mc_nat_ingress fixed =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let _drop = [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let set_output_mcg =
    let mcast_group = Var.make "mcast_group" 16 in
    [mcast_group], Primitives.Action.[
        assign meta.intrinsic_metadata.mcast_grp @@ var mcast_group
      ]
  in
  let set_mcg =
    instr_table("set_mcg",
         [`Exact hdr.ipv4.dstAddr ],
         [set_output_mcg; _drop])
  in
  sequence [
    if fixed then assume @@ eq_ btrue @@ var hdr.ipv4.isValid else skip;
    set_mcg
  ]


let mc_nat_egress =
  (* HoareNet.skip *)
  let open HoareNet in
  (* let open BExpr in *)
  let open Expr in
  let _drop = [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let do_nat =
    let dst_ip = Var.make "dst_ip" 32 in
    [dst_ip], Primitives.Action.[
        assign hdr.ipv4.dstAddr @@ var dst_ip;
        assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8)
      ]
  in
  let nat_table =
    instr_table ( "nat_table",
                  [`Exact meta.intrinsic_metadata.egress_rid;
                   `Exact hdr.ipv4.dstAddr],
                  [do_nat; _drop]
    )
  in
  sequence [
    nat_table
  ]


let mc_nat fixed =
  pipeline mc_nat_parser (mc_nat_ingress fixed) mc_nat_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations (mc_nat false)
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer_buggy () =
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (mc_nat false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (mc_nat true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (mc_nat false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (mc_nat true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Conc CPI is trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "mc_nat annotations" `Quick test_annotations;
  Alcotest.test_case "mc_nat infer enum buggy" `Quick test_infer_buggy;
  Alcotest.test_case "mc_nat infer enum fixed" `Quick test_infer_fixed;
  Alcotest.test_case "mc_nat infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "mc_nat infer conc fixed" `Quick test_concolic_fixed;
]
