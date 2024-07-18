open Core
open Capisce
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
      instr_table ("ipv4_lpm", [
        hdr.ipv4.dstAddr, Maskable
        ], [
          set_nhop; _drop; 
          nop (*Unspecified default action, assuming noop*)
          ])
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
    instr_table ("directtoprio", 
    [
      meta.meta.register_tmp, MaskableDegen
    ], [
      directpriohigh;
      nop (*Unspecified default action, assuming noop*)
    ])
  in
  let readbuffer =
    [],
    (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
    register_read "buffersense_readbuffer" meta.meta.register_tmp (var standard_metadata.egress_port)
  in
  let readbuffersense =
    instr_table ("readbuffersense", [
      meta.meta.register_tmp, MaskableDegen
      ], [
        readbuffer;
        nop (*Unspecified default action, assuming noop*)
      ])
  in
  let setpriolow =
    [], Primitives.Action.[
        (* standard_metadata.egress_spec = 9w0; *)
        assign standard_metadata.egress_spec @@ bvi 0 9;
      ]
        (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
      @ register_read "buffersense_setpriolow" meta.meta.register_tmp (var standard_metadata.egress_port  )
        (* buffersense.write((bit<32>)standard_metadata.egress_port, (bit<16>)(meta.meta.register_tmp + 16w1)); *)
      @ register_write "buffersense_setpriolow" (var standard_metadata.egress_port) @@
        badd (var meta.meta.register_tmp) (bvi 1 16)
  in
  let setpriohigh =
    [], Primitives.Action.[
        (* truncate((bit<32>)32w54); *)
        assign hdr.ipv4.totalLen @@ bvi 20 16;
        assign standard_metadata.egress_spec @@ bvi 1 9;
      ]
  in
  let setprio =
    instr_table ("setprio", [
      meta.meta.register_tmp, MaskableDegen
      ], [
        setpriolow; setpriohigh;
        nop (* unspecified default action, adding noop  *)
        ])
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [dmac], Primitives.Action.[
      assign hdr.ethernet.dstAddr @@ var dmac;
    ] @
      (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
      register_read "buffersense_set_dmac" meta.meta.register_tmp (var standard_metadata.egress_port)
  in
  let forward =
    instr_table ("forward", [
      meta.routing_metadata.nhop_ipv4, Exact
      ], [
        set_dmac; _drop;
        nop (* unspecified default action, adding noop  *)
        ])
  in
  ifte_seq (eq_ btrue @@ var hdr.ipv4.isValid) [
    ifte_seq (ugt_ (var hdr.ipv4.ttl) (bvi 0 8)) [
      ipv4_lpm;
      ifte_seq (eq_ btrue @@ var hdr.ndp.isValid) [
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
      (* FIX-- set egress spec*)
      assign standard_metadata.egress_spec @@ bvi 511 9;
    ]
  ] [
    (* FIX-- set egress spec*)
    assign standard_metadata.egress_spec @@ bvi 511 9;
  ]

let ndp_egress =
  let open HoareNet in
  (* let open BExpr in *)
  let open Expr in
  let decreasereg =
    [],
    (* buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port); *)
    register_read "buffersense_decreasereg" meta.meta.register_tmp (var standard_metadata.egress_port) @
    (* buffersense.write((bit<32>)standard_metadata.egress_port, (bit<16>)(meta.meta.register_tmp - 16w1 + (bit<16>)standard_metadata.egress_spec)); *)
    register_write "buffersense_decreasereg" (var standard_metadata.egress_port) @@
    badd (bsub (var meta.meta.register_tmp) (bvi 1 16)) @@
    bcast 16 (var standard_metadata.egress_spec)
  in
  let cont = [], [] in
  let dec_counter =
    instr_table ("dec_counter",
                 [meta.meta.ndpflags, MaskableDegen],
                 [decreasereg; cont;
                  nop (* unspecified default action assuming noop *) 
                 ])
  in
  let rewrite_mac =
    let smac = Var.make "smac" 48 in
    [smac], Primitives.Action.[
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
                 [standard_metadata.egress_port, Exact],
                 [rewrite_mac; _drop;
                 nop (* unspecified default action assuming noop *)
                 ])
  in
  sequence [
    dec_counter;
    send_frame
  ]

let ndp_router =
  pipeline ndp_parser ndp_ingress ndp_egress

