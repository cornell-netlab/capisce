open Core
open Capisce
open ASTs.GPL
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
     (* assign (f i).bos @@ var (f Int.(i + 1)).bos;
     assign (f i).port @@ var (f Int.(i + 1)).port *)
    ]
  )
  |> List.concat
  |> Fun.flip List.append [assign (f (n - 1)).isValid @@ bfalse]

let hula_parser =
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

let hula_psm =
  let open EmitP4.Parser in 
  let open ASTs.GCL in 
  let open Expr in
  let parse_srcRouting = Printf.sprintf "parse_srcRouting__%d" in 
  let srcRouting i : state =
    let transition = 
      if Int.(i >= 7) then
        direct "parse_ipv4"
      else
        select (srcRoute i).bos [
          btrue, "parse_ipv4"
        ] (parse_srcRouting Int.(i + 1))
    in 
    let post = 
      assign (srcRoute 7).bos btrue;
    in
    state (parse_srcRouting i) (srcRoute i).isValid ~post transition
  in
  of_state_list @@ [
    noop_state "start" "parse_ethernet";
    state "parse_ethernet" hdr.ethernet.isValid @@
    select hdr.ethernet.etherType [
      bvi 2048 16, "parse_ipv4";
      bvi 9029 16, "parse_hula";
    ] "accept"
    ;
    state "parse_ipv4" hdr.ipv4.isValid @@ 
    select hdr.ipv4.protocol [
      bvi 17 8, "parse_udp"
    ] "accept" 
    ;
    state "parse_udp" hdr.udp.isValid @@
    direct "accept"
    ;
    state "parse_hula" hula.isValid @@
    direct (parse_srcRouting 0)
  ] @ List.init 7 ~f:srcRouting

let hula_ingress _ =
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
    table
      "hula_fwd"
      [hdr.ipv4.dstAddr, Exact;
       hdr.ipv4.srcAddr, Exact]
      [hula_dst; srcRoute_nhop (* default *) ]
  in
  let change_best_path_at_dst =
      (* srcindex_qdepth_reg.write(meta.index, hdr.hula.qdepth); *)
      register_read "srcindex_qdepth_reg_change_best_path_at_dst" meta.index (var hula.qdepth) @
      (* srcindex_digest_reg.write(meta.index, hdr.hula.digest); *)
      register_read "srcindex_digest_reg_change_best_path_at_dst" meta.index (var hula.digest)
      |> sequence_map ~f:active
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
    [index],
    (* dstindex_nhop_reg.write(index, (bit<16>)standard_metadata.ingress_port);  *)
    register_write "dstindec_nhop_reg_hula_set_nhop" (var index) (var standard_metadata.ingress_port);
  in
  let hula_bwd =
    table "hula_bwd"
      [hdr.ipv4.dstAddr, Maskable]
      [
        hula_set_nhop;
        nop; (* Unspecified default action, assuming nop *)
      ]
  in
  let _drop = [], Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let hula_src =
    table "hula_src"
      [hdr.ipv4.srcAddr, Exact]
      [_drop; srcRoute_nhop; (*default*)]
  in
  let hula_get_nhop =
    let tmp = Var.make "tmp" 16 in
    let index = Var.make "index" 32 in
    [index], Action.[
       (* dstindex_nhop_reg.read(tmp, index); *)
       register_read "dstindex_nhop_reg_hula_get_nhop" tmp (var index);
       [assign standard_metadata.egress_spec @@ bcast 9 @@ var tmp];
    ] |> List.concat
  in
  let hula_nhop =
    table "hula_nhop"
      [hdr.ipv4.dstAddr, Maskable]
      [hula_get_nhop; _drop (* default *)]
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
    table "dmac"
      [standard_metadata.egress_spec, Exact]
      [set_dmac; nop (* default *)]
  in
  let old_qdepth = Var.make "old_qdepth" 15 in
  let old_digest = Var.make "old_digest" 32 in
  let flow_hash = Var.make "flow_hash" 16 in
  let port = Var.make "port" 16 in
  sequence [
    ifte_seq (eq_ btrue @@ var hula.isValid) [
      ifte_seq (eq_ bfalse @@ var hula.dir) [
        hula_fwd;
        select (var @@ Var.make "_symb$hula_fwd$action" 1) [
          bvi 0 1, sequence [
            (* qdepth_t old_qdepth; *)
            (* srcindex_qdepth_reg.read(old_qdepth, meta.index); *)
            register_read "srcindex_qdepth_reg_ingress" old_qdepth (var meta.index) |> sequence_map ~f:active;
            ifte_seq (ugt_ (var old_qdepth) (var hula.qdepth)) [
                change_best_path_at_dst;
                return_hula_to_src;
            ] [ 
            (* srcindex_digest_reg.read(old_digest, meta.index); *)
            register_read "srcindex_qdepth_reg_ingress1" old_digest (var meta.index) |> sequence_map ~f:active;
            ifte (eq_ (var old_digest) (var hula.digest))
              ((* srcindex_qdepth_reg.write(meta.index, hdr.hula.qdepth); *)
                register_write "srcindex_qdepth_reg_ingress" (var meta.index) (var hula.qdepth)
                |> sequence_map ~f:active
              )
              skip;
            drop;
        ]
        ]
      ] skip
    ] [
      hula_bwd;
      hula_src
    ]
    ] [
      ifte_seq (eq_ btrue @@ var hdr.ipv4.isValid) [
        (* assert_ (eq_ btrue @@ var hdr.udp.isValid); *)
        (* bit<16> flow_hash; *)
        (* hash(flow_hash, hashAlgorithm.crc16, 16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.udp.srcPort}, 32w65536);       *)
        hash_ flow_hash "crc16" (bvi 0 16) [ var hdr.ipv4.srcAddr; var hdr.ipv4.dstAddr; var hdr.udp.srcPort ] (bvi 65536 32) "flow_hash_ingress"
        |> sequence_map ~f:active;
        ifte_seq (eq_ (var port) (bvi 0 16)) [
          hula_nhop;
          (* flow_port_reg.write((bit<32>)flow_hash, (bit<16>)standard_metadata.egress_spec); *)
          register_write "flow_port_reg_ingress" (var flow_hash) (var standard_metadata.egress_spec)
          |> sequence_map ~f:active
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
  hula_psm, hula_ingress fixed, hula_egress
