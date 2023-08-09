open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type mymeta_t = {
  f1 : Var.t;
  f2 : Var.t
}
let mymeta : mymeta_t = {
  f1 = Var.make "meta.mymeta.f1" 8;
  f2 = Var.make "meta.mymeta.f2" 8
}

type metadata_t = {
  mymeta : mymeta_t
}

let meta : metadata_t = {mymeta}

let resubmit_parser =
  let open HoareNet in
  (* start *)
  sequence [
    assign hdr.ethernet.isValid bfalse;
    (* parse_ethernet  *)
    assign hdr.ethernet.isValid btrue;
    transition_accept;
  ]

let resubmit_ingress =
  let open HoareNet in
  let open Expr in
  let _nop = [],[] in
  let set_port =
    let port = Var.make "port" 9 in
    [], Primitives.Action.[assign standard_metadata.egress_spec @@ var port]
  in
  let _resubmit =
    [], Primitives.Action.[
        assign meta.mymeta.f1 @@ bvi 1 8;
        (*resubmit({standard_metadata, meta.mymeta})*)
      ]
  in
  let t_ingress_1 =
    table ("t_ingress_1", [meta.mymeta.f1], [_nop; set_port])
  in
  let t_ingress_2 =
    table ("t_ingress_2", [meta.mymeta.f2], [_nop; _resubmit])
  in
  sequence [
    t_ingress_1;
    t_ingress_2
  ]

let resubmit_egress = HoareNet.skip

let resubmit = pipeline resubmit_parser resubmit_ingress resubmit_egress

let test_annotations () =
  HoareNet.check_annotations resubmit
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer () =
  HoareNet.infer resubmit None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc resubmit None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "resubmit annotations" `Quick test_annotations;
  Alcotest.test_case "resubmit all_paths inference" `Quick test_infer;
  Alcotest.test_case "resubmit concolic inference" `Quick test_concolic;
]
