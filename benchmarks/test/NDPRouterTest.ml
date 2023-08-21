open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils


type routing_metadata_t = {
  nhop_ipv4 : Var.t
}

let routing_metadata : routing_metadata_t = {
  nhop_ipv4 = Var.make "meta.routing_metadata.nhop_ipv4" 32
}

type meta_t = {
  register_tmp : Var.t;
  ndpflags : Var.t
}

let meta : meta_t = {
  register_tmp = Var.make "meta.meta.register_tmp" 16;
  ndpflags = Var.make "meta.meta.ndpflags" 16
}

type metadata_t = {
  meta : meta_t;
  routing_metadata: routing_metadata_t
}
let meta : metadata_t = {meta; routing_metadata}

let ndp_parser =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  sequence [
    (* start state *)
    assign hdr.ethernet.isValid bfalse;
    assign hdr.ipv4.isValid bfalse;
    assign hdr.ndp.isValid bfalse;
    (* parse_ethernet *)
    assign hdr.ethernet.isValid btrue;
    (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
    ifte_seq (eq_ (var hdr.ethernet.etherType) (bvi 2048 16)) [
      (*parse_ipv4*)
      assign hdr.ipv4.isValid btrue;
      (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
      ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 409 8)) [
        assign hdr.ndp.isValid btrue;
        transition_accept
      ] [transition_accept]

    ] [transition_accept]
  ]

let ndp_ingress =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let set_nhop =
    let nhop_ipv4 = Var.make "nhop_ipv4" 32 in
    let port = Var.make "port" 9 in
    [nhop_ipv4; port], Primitives.Action.[
        assign meta.routing_metadata.nhop_ipv4 @@ var nhop_ipv4;
        assign standard_metadata.egress_port @@ var port;
        (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
        assign hdr.ipv4.ttl @@ (badd (var hdr.ipv4.ttl) (bvi 255 8))
      ]
  in
  let _drop =
    [], Primitives.Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let ipv4_lpm =
    sequence [
      (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
      instr_table ("ipv4_lpm", [`Maskable hdr.ipv4.dstAddr], [set_nhop; _drop])
    ]
  in
  let directpriohigh =
    [], Primitives.Action.[
        assign standard_metadata.egress_spec @@ bvi 1 9;
        (* assert_ @@ eq_ btrue @@ var hdr.ndp.isValid; *)
        assign meta.meta.ndpflags @@ var hdr.ndp.flags
      ]
  in
  let directtoprio =
    instr_table ("directtoprio", [`MaskableDegen meta.meta.register_tmp], [directpriohigh])
  in
  let readbuffer =
    [], [
      (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
    ]
  in
  let readbuffersense =
    instr_table ("readbuffersense", [`MaskableDegen meta.meta.register_tmp], [readbuffer])
  in
  let setpriolow =
    [], Primitives.Action.[
        (* standard_metadata.egress_spec = 9w0; *)
        assign standard_metadata.egress_spec @@ bvi 0 9;
        (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
        (* buffersense.write((bit<32>)standard_metadata.egress_port, (bit<16>)(meta.meta.register_tmp + 16w1)); *)
      ]
  in
  let setpriohigh =
    [], Primitives.Action.[
        (* truncate((bit<32>)32w54); *)
        (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
        assign hdr.ipv4.totalLen @@ bvi 20 16;
        assign standard_metadata.egress_spec @@ bvi 1 9;
      ]
  in
  let setprio =
    instr_table ("setprio", [`MaskableDegen meta.meta.register_tmp], [setpriolow; setpriohigh])
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [dmac], Primitives.Action.[
        (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
        assign hdr.ethernet.dstAddr @@ var dmac;
        (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
      ]
  in
  let forward =
    instr_table ("forward", [`Exact meta.routing_metadata.nhop_ipv4], [set_dmac; _drop])
  in
  ifte_seq (eq_ btrue @@ var hdr.ipv4.isValid) [
    (* assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid; *)
    ifte_seq (ugt_ (var hdr.ipv4.ttl) (bvi 0 8)) [
      ipv4_lpm;
      ifte_seq (eq_ btrue @@ var hdr.ndp.isValid) [
        (* assert_ @@ eq_ btrue @@ var hdr.ndp.isValid; *)
        ifte_seq (ugt_ (var hdr.ndp.flags) (bvi 1 16)) [
          directtoprio
        ] [
          readbuffersense;
          setprio
        ]
      ] [
        readbuffersense;
        setprio
      ];
      forward
    ] [
    ]
  ] []

let ndp_egress =
  let open HoareNet in
  (* let open BExpr in *)
  let open Expr in
  let decreasereg =
    [], [
        (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
        (* buffersense.write((bit<32>)standard_metadata.egress_port, (bit<16>)(meta.meta.register_tmp - 16w1 + (bit<16>)standard_metadata.egress_spec)); *)
      ]
  in
  let cont = [], [] in
  let dec_counter =
    instr_table ("dec_counter",
                 [`MaskableDegen meta.meta.ndpflags],
                 [decreasereg; cont])
  in
  let rewrite_mac =
    let smac = Var.make "smac" 48 in
    [smac], Primitives.Action.[
        (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
        assign hdr.ethernet.srcAddr @@ var smac
    ]
  in
  let _drop =
    [], Primitives.Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let send_frame =
    instr_table ("send_frame",
                 [`Exact standard_metadata.egress_port],
                 [rewrite_mac; _drop])
  in
  sequence [
    dec_counter;
    send_frame
  ]

let ndp =
  pipeline ndp_parser ndp_ingress ndp_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations ndp
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer () =
  HoareNet.infer ndp None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc ndp None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "ndp_router annotations" `Quick test_annotations;
  Alcotest.test_case "ndp_router all_paths inference" `Quick test_infer;
  Alcotest.test_case "ndp_router concolic inference" `Quick test_concolic;
]