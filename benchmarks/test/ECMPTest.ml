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


type metadata_t = {
  routing_metadata : routing_metadata_t
}

let meta = {routing_metadata}


let ecmp_parser : HoareNet.t =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  sequence [
    assign zombie.parse_result @@ Expr.bvi 0 1;
    assign hdr.ethernet.isValid @@ Expr.bvi 1 1;
    (* assert_ @@ eq_ (var hdr.ethernet.isValid) (bvi 1 1); *)
    choice_seqs [
      [ assume @@
        eq_ (var hdr.ethernet.etherType) (bvi 2048 16);
        assign hdr.ipv4.isValid @@ bvi 1 1;
        choice_seqs [
          [ (* assert_ @@ eq_ (var hdr.ipv4.isValid) (bvi 1 1); *)
            assume @@
            eq_ (var hdr.ipv4.protocol) (bvi 6 8);
            assign hdr.tcp.isValid @@ bvi 1 1;
            assign zombie.parse_result @@ bvi 1 1;
          ];
          [assume @@
           not_ (eq_ (var hdr.ipv4.protocol) (bvi 6 8));
           assign zombie.parse_result (bvi 1 1)
          ]
        ]
      ];
      [ assume @@
        not_ (eq_ (var hdr.ethernet.etherType) (Expr.bvi 2048 16));
        assign zombie.parse_result (bvi 1 1)
      ]
    ];
  ]

let ecmp_ingress =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let nhop_ipv4 = Var.make "nhop_ipv4" 32 in
  let port = Var.make "port" 9 in
  let dmac = Var.make "dmac" 48 in
  let ecmp_group =
    instr_table
      ("ecmp_group",
       [ `Maskable hdr.ipv4.dstAddr],
       [ (*_drop*)
         [],
         Primitives.Action.[
           assign
             standard_metadata.egress_spec
             (bvi 511 9)]
         ;
         (* set_nhop *)
         [nhop_ipv4; port],
         Primitives.Action.[
           assign meta.routing_metadata.nhop_ipv4 (var nhop_ipv4);
           assign standard_metadata.egress_spec (var port);
           (* assert_ @@ eq_ (var hdr.ipv4.isValid) (bvi 1 1); *)
           assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8);
         ]
         ;
         nop (* No default action specified, assuming noop *)
       ]
      )
  in
  let forward =
    instr_table (
      "forward",
      [ `MaskableDegen meta.routing_metadata.nhop_ipv4],
      [ (* set_dmac  *)
        [dmac],
        Primitives.Action.[
          assign hdr.ethernet.dstAddr (var dmac)
        ];
        (* _drop  *)
        [],
        Primitives.Action.[
          assign
            standard_metadata.egress_spec
            (Expr.bvi 511 9)
        ];
        nop (*  no default action specified assuming noop *)
      ]
    )

  in
  choice_seqs [
    [assume @@ eq_ (var hdr.ipv4.isValid) (bvi 1 1);
     choice_seqs [
       [ (* assert_ @@ eq_ (var hdr.ipv4.isValid) (bvi 1 1); *)
         assume @@ ugt_ (var hdr.ipv4.ttl) (bvi 0 8);
         ecmp_group;
         forward;
       ];
       [assume @@ not_ @@ ugt_ (var hdr.ipv4.ttl) (Expr.bvi 0 8)]

     ]
    ];
    [assume @@ not_ (eq_ (var hdr.ipv4.isValid) (Expr.bvi 1 1))]
  ]


let ecmp_egress =
  let open HoareNet in
  (* let open BExpr in *)
  let open Expr in
  let smac = Var.make "smac" 48 in
  let send_frame =
    instr_table (
      "send_frame",
      [ `Exact standard_metadata.egress_port ],
      [ [smac],
        Primitives.Action.[
          (* assert_ @@ eq_ (var hdr.ethernet.isValid) (bvi 1 1); *)
          assign hdr.ethernet.srcAddr (var smac);
        ];
        [],
        Primitives.Action.[
          assign standard_metadata.egress_spec (bvi 511 9)
        ]
      ]
    )
  in
  sequence [
    send_frame
  ]

let ecmp =
  pipeline ecmp_parser ecmp_ingress ecmp_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations ecmp
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer () =
  HoareNet.infer ecmp None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc ecmp None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "ecmp2 annotations" `Quick test_annotations;
  Alcotest.test_case "ecmp2 all_paths inference" `Quick test_infer;
  Alcotest.test_case "ecmp2 concolic inference" `Quick test_concolic;
]
