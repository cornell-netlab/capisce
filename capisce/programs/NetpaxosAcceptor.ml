open Core
open Capisce
open ASTs.GPL
open V1ModelUtils


type local_metadata_t = {
  proposal : Var.t
}
let local_metadata = {
  proposal = Var.make "meta.local_metadata.proposal" 16
}

type meta_t = {
  local_metadata : local_metadata_t
}
let meta : meta_t = {local_metadata}

let npa_parser =
  let open BExpr in
  let open Expr in
  sequence [
    assign zombie.parse_result bfalse;
    assign hdr.ethernet.isValid bfalse;
    assign hdr.ipv4.isValid bfalse;
    assign hdr.udp.isValid bfalse;
    assign hdr.paxos.isValid bfalse;
    assign hdr.ethernet.isValid btrue;
    (* assert_ @@ eq_ (var hdr.ethernet.isValid) btrue; *)
    ifte_seq (eq_ (var hdr.ethernet.etherType) (bvi 2048 16))
      [ (* PARSE_IPv4 *)
        assign hdr.ipv4.isValid btrue;
        (* assert_ @@ eq_ (var hdr.ipv4.isValid) btrue; *)
        ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 17 8))
          [ (* PARSE UDP *)
            assign hdr.udp.isValid btrue;
            ifte_seq (eq_ (var hdr.udp.dstPort) (bvi 34952 16))
              [ (* PARSE PAXOS *)
                assign hdr.paxos.isValid btrue;
                transition_accept
              ]
              [transition_accept]
          ]
          [transition_accept]
      ]
      [ transition_accept ]
  ]

let npa_psm =
  let open EmitP4.Parser in
  let open Expr in 
  of_state_list [
    noop_state "start" "parse_ethernet"
    ;
    state "parse_ethernet" hdr.ethernet.isValid @@
    select hdr.ethernet.etherType [
      bvi 2048 16, "parse_ipv4";
    ] "accept"
    ;
    state "parse_ipv4" hdr.ipv4.isValid @@
    select hdr.ipv4.protocol [
      bvi 17 8, "parse_udp";
    ] "accept"
    ;
    state "parse_udp" hdr.udp.isValid @@
    select hdr.udp.dstPort [
      bvi 34952 16, "parse_paxos"
    ] "accept"
    ;
    state "parse_paxos" hdr.paxos.isValid @@
    direct "accept"
  ]
let npa_ingress =
  let open Expr in
  let open BExpr in
  let forward =
    let port = Var.make "port" 9 in
    [port], Primitives.Action.[assign standard_metadata.egress_spec (var port)]
  in
  let _drop =
    [], Primitives.Action.[assign standard_metadata.egress_spec (bvi 511 9)]
  in
  let fwd_tbl =
    table "fwd_tbl"
      [standard_metadata.ingress_port, Exact]
      [ forward; _drop;
        nop (*No default action assuming noop*)
  ] in
  let read_round =
    [],   
      (*proposal_register.read(meta.local_metadata.proposal, hdr.paxos.inst)*)
      register_read "proposal_register_read_round" meta.local_metadata.proposal (var hdr.paxos.inst)
  in
  let round_tbl =
    table "round_tbl" [] [read_round; nop] (* no default action assuming noop*)
  in
  let _no_op = [],[] in
  let handle_phase1a =
    [], 
    (* proposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal); *)
    register_write "proposal_register_1a" (var hdr.paxos.inst) (var hdr.paxos.proposal) @
    (* vproposal_register.read(hdr.paxos.vproposal, (bit<32>)hdr.paxos.inst); *)
    register_read "vproposal_register_1a" hdr.paxos.vproposal (var hdr.paxos.inst) @
    (* val_register.read(hdr.paxos.val, (bit<32>)hdr.paxos.inst); *)
    register_read "val_register_1a" hdr.paxos.value (var hdr.paxos.inst) @
    (* acceptor_id.read(hdr.paxos.acpt, (bit<32>)32w0); *)
    register_read "acceptor_id_1a" hdr.paxos.acpt (bvi 0 32) @
    Primitives.Action.[
        assign hdr.udp.checksum @@ bvi 0 16
      ]
  in
  let handle_phase2a =
    let open Primitives.Action in
    [], 
        (* proposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal); *)
        register_write "proposal_register_2a" (var hdr.paxos.inst) (var hdr.paxos.proposal) @
        (* vproposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal); *)
        register_write "vproposal_register_2a" (var hdr.paxos.inst) (var hdr.paxos.proposal) @
        (* val_register.write((bit<32>)hdr.paxos.inst, (bit<32>)hdr.paxos.val); *)
        register_write "val_register" (var hdr.paxos.inst) (var hdr.paxos.value) @
      [ 
        assign hdr.paxos.msgtype @@ bvi 4 16;
        assign hdr.paxos.vproposal @@ var hdr.paxos.proposal
      ] @
        (* acceptor_id.read(hdr.paxos.acpt, (bit<32>)32w0); *)
        register_read "acceptor_id" hdr.paxos.acpt (bvi 0 32) @
      [
        assign hdr.udp.checksum @@ bvi 0 16;
      ]
  in
  let paxos_tbl =
    table "paxos_tbl"
      [ hdr.paxos.msgtype, Exact ]
      [ handle_phase1a;
        handle_phase2a;
        _no_op;
        (* no default action specified assuming noop, 
          but making no changes,
          because we already have an action _no_op*)
      ]
in
  let drop_tbl =
    table "drop_tbl" [] [_drop; nop] (* adding dummy default action noop *)
  in
  sequence [
    ifte_seq (eq_ (var hdr.ipv4.isValid) btrue)
      [fwd_tbl]
      [ (* FIX-- DELETED ] *)
    ifte_seq (eq_ (var hdr.paxos.isValid) btrue)
      [round_tbl;
       ifte_seq (ule_ (var meta.local_metadata.proposal) (var hdr.paxos.proposal))
         [paxos_tbl]
         [drop_tbl]
      ] [
        (* FIX-- ADDED assignment*)
        assign standard_metadata.egress_spec @@ bvi 511 9;
      ];
    (* FIX-- ADDED ] *)
    ]
  ]


let npa_egress = skip

let netpaxos_acceptor =
  npa_psm, npa_ingress, npa_egress
