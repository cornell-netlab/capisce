open Core
open Capiscelib
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
    (* No default action specified, but we already have a _nop action *)
    instr_table ("t_ingress_1", [`Exact meta.mymeta.f1], [_nop; set_port])
  in
  let t_ingress_2 =
    (* No default action specified, but we already have a _nop action *)
    instr_table ("t_ingress_2", [`Exact meta.mymeta.f2], [_nop; _resubmit])
  in
  sequence [
    t_ingress_1;
    t_ingress_2
  ]

let resubmit_egress = HoareNet.skip

let resubmit =
  pipeline resubmit_parser resubmit_ingress resubmit_egress
  |> HoareNet.assert_valids