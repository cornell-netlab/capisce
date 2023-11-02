open Core
open Pbench
open DependentTypeChecker
open V1ModelUtils

type meta_t = {
  index : Var.t
}
let meta : meta_t = {
  index = Var.make "meta.index" 32;
}

type hula_t = {
  isValid : Var.t;
  dir : Var.t;
  qdepth : Var.t;
  digest : Var.t;
}

let hula : hula_t =
  let field f sz  = Var.make (Printf.sprintf "hdr.hula.%s" f) sz in
  { isValid = field "isValid" 1;
    dir = field "dir" 1;
    qdepth = field "qdepth" 15;
    digest = field "digest" 32;
  }

type srcRoute_t = {
  isValid : Var.t;
  bos : Var.t;
  port : Var.t;
}

let srcRoute i : srcRoute_t =
  let field f sz = Var.make (Printf.sprintf "hdr.srcRoute_%d_.%s" i f) sz in
  { isValid = field "isValid" 1;
    bos = field "bos" 1;
    port = field "port" 15;
  }

let pop_front_1 f n =
  let open Primitives.Action in
  let open Expr in
  List.init (n-1) ~f:(fun i ->
    [assign (f i).isValid @@ var (f Int.(i + 1)).isValid;
     assign (f i).bos @@ var (f Int.(i + 1)).bos;
     assign (f i).port @@ var (f Int.(i + 1)).port
    ]
  )
  |> List.concat
  |> Fun.flip List.append [assign (f (n - 1)).isValid @@ bfalse]

let hula_parser =
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
  let rec parse_srcRouting i =
    if Int.(i >= 7) then
      sequence [
        assign (srcRoute 7).isValid btrue;
        assume @@ eq_ btrue @@ var (srcRoute 7).bos;
        parse_ipv4
      ]
    else
      sequence [
        assign (srcRoute i).isValid btrue;
        ifte (eq_ btrue @@ var (srcRoute i).bos)
          parse_ipv4
          (parse_srcRouting Int.(i + 1))
      ]

  in
  let parse_hula =
    sequence [
      assign hula.isValid btrue;
      parse_srcRouting 0
    ]
  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      (* assert_ @@ eq_ btrue @@ var hdr.ethernet.isValid; *)
      select (var hdr.ethernet.etherType)[
        bvi 2048 16, parse_ipv4;
        bvi 9029 16, parse_hula;
      ] transition_accept
    ]

  in
  let start =
    sequence [
      assign hdr.ethernet.isValid bfalse;
      assign hdr.ipv4.isValid bfalse;
      assign hdr.udp.isValid bfalse;
      assign hula.isValid bfalse;
      assign (srcRoute 0).isValid bfalse;
      assign (srcRoute 1).isValid bfalse;
      assign (srcRoute 2).isValid bfalse;
      assign (srcRoute 3).isValid bfalse;
      assign (srcRoute 4).isValid bfalse;
      assign (srcRoute 5).isValid bfalse;
      assign (srcRoute 6).isValid bfalse;
      assign (srcRoute 7).isValid bfalse;
      parse_ethernet
    ]
  in
  start

let hula_ingress fixed =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let open Primitives in
  let hula_dst =
    let index = Var.make "index" 32 in
    [index], Action.[
        assign meta.index @@ var index
    ]
  in
  let srcRoute_nhop =
    [],
    Action.[
      assign standard_metadata.egress_spec @@ bcast 9 @@ var (srcRoute 0).port;
    ] @ pop_front_1 srcRoute 8
  in
  let hula_fwd =
    instr_table(
      "hula_fwd",
      [`Exact hdr.ipv4.dstAddr;
       `Exact hdr.ipv4.srcAddr],
      [hula_dst; srcRoute_nhop]
    )
  in
  let change_best_path_at_dst = sequence [
      assert_ @@ eq_ btrue @@ var hula.isValid;
      (* srcindex_qdepth_reg.write(meta.index, hdr.hula.qdepth); *)
      (* srcindex_digest_reg.write(meta.index, hdr.hula.digest); *)
    ]
  in
  let return_hula_to_src = sequence [
      assign hula.dir btrue;
      assign standard_metadata.egress_spec @@ var standard_metadata.ingress_port
    ]
  in
  let drop =
    assign standard_metadata.egress_spec @@ bvi 511 9
  in
  let update_ttl =
    assign hdr.ipv4.ttl @@ bsub (var hdr.ipv4.ttl) (bvi 1 8)
  in
  let hula_set_nhop =
    let index = Var.make "index" 32 in
    [index], []
    (* dstindex_nhop_reg.write(index, (bit<16>)standard_metadata.ingress_port);  *)
  in
  let hula_bwd =
    instr_table ("hula_bwd",
                [`Maskable hdr.ipv4.dstAddr],
                [hula_set_nhop])
  in
  let _drop = [], Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let hula_src =
    instr_table ("hula_src",
                 [`Exact hdr.ipv4.srcAddr],
                 [_drop; srcRoute_nhop]
                )
  in
  let hula_get_nhop =
    let tmp = Var.make "tmp" 16 in
    [], Action.[
       (* dstindex_nhop_reg.read(tmp, index); *)
       assign standard_metadata.egress_spec @@ bcast 9 @@ var tmp;
    ]
  in
  let hula_nhop =
    instr_table ("hula_nhop",
                [`Maskable hdr.ipv4.dstAddr],
                [hula_get_nhop; _drop])
  in
  let set_dmac =
    let dstAddr = Var.make "dstAddr" 48 in
    [dstAddr], Action.[
        assign hdr.ethernet.srcAddr @@ var hdr.ethernet.dstAddr;
        assign hdr.ethernet.dstAddr @@ var dstAddr;
    ]
  in
  let nop = [],[] in
  let dmac =
    instr_table ("dmac",
                 [`Exact standard_metadata.egress_spec],
                 [set_dmac; nop]
                )
  in
  let old_qdepth = Var.make "old_qdepth" 15 in
  let old_digest = Var.make "old_digest" 32 in
  let port = Var.make "port" 16 in
  sequence [
    ifte_seq (eq_ btrue @@ var hula.isValid) [
      ifte_seq (eq_ bfalse @@ var hula.dir) [
        hula_fwd;
        select (var @@ Var.make "_symb$hula_fwd$action" 1) [
          bfalse,
          (* qdepth_t old_qdepth; *)
          (* srcindex_qdepth_reg.read(old_qdepth, meta.index); *)
          ifte_seq (ugt_ (var old_qdepth) (var hula.qdepth)) [
              change_best_path_at_dst;
              return_hula_to_src;
          ] [ (* srcindex_digest_reg.read(old_digest, meta.index); *)
          ifte (eq_ (var old_digest) (var hula.digest))
            (assert_ @@ eq_ btrue @@ var hula.isValid (* srcindex_qdepth_reg.write(meta.index, hdr.hula.qdepth); *))
            (skip);
          drop;
        ]
      ] skip
    ] [
      hula_bwd;
      hula_src
    ]
  ] [
    ifte_seq (eq_ btrue @@ var hdr.ipv4.isValid) [
      if fixed then assume @@ eq_ btrue @@ var hdr.udp.isValid else skip;
      assert_ @@ eq_ btrue @@ var hdr.ipv4.isValid;
      assert_ @@ eq_ btrue @@ var hdr.udp.isValid;
         (* bit<16> flow_hash; *)
         (* hash(flow_hash, hashAlgorithm.crc16, 16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.udp.srcPort}, 32w65536);       *)
      ifte_seq (eq_ (var port) (bvi 0 16)) [
        hula_nhop;
        (* flow_port_reg.write((bit<32>)flow_hash, (bit<16>)standard_metadata.egress_spec); *)
      ] [
        assign standard_metadata.egress_spec @@ bcast 9 @@ var port;
      ];
      dmac
    ] [
      drop
    ]
  ];
    ifte (eq_ btrue @@ var hdr.ipv4.isValid)
      update_ttl
      skip
  ]


let hula_egress =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  sequence [
    ifte (eq_ btrue @@ var hula.isValid) (
      ifte (eq_ bfalse @@ var hula.dir) (
        ifte (ult_ (var hula.qdepth) @@ bcast 15 @@ var standard_metadata.deq_qdepth) (
          assign hula.qdepth @@ bcast 15 @@ var standard_metadata.deq_qdepth
        ) skip
      ) skip
    ) skip
  ]

let hula fixed =
  pipeline hula_parser (hula_ingress fixed) hula_egress
  |> HoareNet.assert_valids

let test_annotations () =
  HoareNet.check_annotations (hula true)
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer_buggy () =
  Printf.printf "GPL Program: %s ------\n" @@ HoareNet.to_string (hula false);
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (hula false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (hula true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.false_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (hula false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (hula true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is sat"
    BExpr.false_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "Hula annotations" `Quick test_annotations;
  Alcotest.test_case "Hula enum buggy" `Slow test_infer_buggy;
  Alcotest.test_case "Hula infer enum fixed" `Slow test_infer_fixed;
  Alcotest.test_case "Hula infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "Hula infer conc fixed" `Quick test_concolic_fixed;
]