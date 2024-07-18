open Core
open Capisce
open DependentTypeChecker
open V1ModelUtils

type custom_metadata_t = {
  count_val1 : Var.t;
  count_val2 : Var.t;
  nhop_ipv4 : Var.t;
  hash_val1 : Var.t;
  hash_val2 : Var.t;
}

let custom_metadata : custom_metadata_t = {
  count_val1 = Var.make "meta.custom_metadata.count_val2" 16;
  count_val2 = Var.make "meta.custom_metadata.count_val1" 16;
  nhop_ipv4 = Var.make "meta.custom_metadata.nhop_ipv4" 32;
  hash_val1 = Var.make "meta.custom_metadata.hash_val1" 16;
  hash_val2 = Var.make "meta.custom_metadata.hash_val2" 16;
}

type meta_t =  {
  custom_metadata : custom_metadata_t
}

let meta : meta_t = {custom_metadata}

let hh2_parser =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let parse_tcp =
    sequence [
      assign hdr.tcp.isValid btrue;
      transition_accept
    ]
  in
  let parse_ipv4 =
    sequence [
        assign hdr.ipv4.isValid btrue;
        ifte_seq (eq_ (var hdr.ipv4.protocol) (bvi 6 8))
          [ parse_tcp ]
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
      assign hdr.tcp.isValid bfalse;
      parse_ethernet
    ]
  in
  start

let hh2_ingress fixed =
  let open HoareNet in
  let open BExpr in
  let open Expr in
  let set_heavy_hitter_count =
    [], Primitives.Action.[
        (* // Count the hash 1 for indexing *)
        (* hash(meta.custom_metadata.hash_val1, HashAlgorithm.csum16, (bit<16>)16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort }, (bit<32>)32w16); *)
        hash_ meta.custom_metadata.hash_val1 "csum16" (bvi 0 16) [var hdr.ipv4.srcAddr;var hdr.ipv4.dstAddr;var hdr.ipv4.protocol;var hdr.tcp.srcPort;var hdr.tcp.dstPort] (bvi 16 32) "set_heavy_hitter_count";
        (* // Read the value in the register with that index *)
        (* heavy_hitter_counter1.read(meta.custom_metadata.count_val1, (bit<32>)meta.custom_metadata.hash_val1); *)
        register_read "heavy_hitter_counter1_set_heavy_hitter_count" meta.custom_metadata.count_val1 (var meta.custom_metadata.hash_val1);
        (* // Incremet the value with 1 *)
        [assign meta.custom_metadata.count_val1 @@ badd (var meta.custom_metadata.count_val1) (bvi 1 16)];
        (* // Write the value back to the register with that index *)
        (* heavy_hitter_counter1.write((bit<32>)meta.custom_metadata.hash_val1, (bit<16>)meta.custom_metadata.count_val1); *)
        register_write "heavy_hitter_counter1_set_heavy_hitter_count" (var meta.custom_metadata.hash_val1) (var meta.custom_metadata.count_val1);
        (* // Count the hash 2 for another indexing, similar to the first hash *)
        (* hash(meta.custom_metadata.hash_val2, HashAlgorithm.crc16, (bit<16>)16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort }, (bit<32>)32w16); *)
        hash_ meta.custom_metadata.hash_val2 "crc16" (bvi 0 16) [var hdr.ipv4.srcAddr; var hdr.ipv4.dstAddr; var hdr.ipv4.protocol; var hdr.tcp.srcPort; var hdr.tcp.dstPort] (bvi 16 32) "set_heavy_hitter_count";
        (* heavy_hitter_counter2.read(meta.custom_metadata.count_val2, (bit<32>)meta.custom_metadata.hash_val2); *)
        register_read "heavy_hitter_counter2_set_heavy_hitter_count" meta.custom_metadata.count_val2 (var meta.custom_metadata.hash_val2);
        [assign meta.custom_metadata.count_val2 @@ badd (var meta.custom_metadata.count_val2) (bvi 1 16)];
        (* heavy_hitter_counter2.write((bit<32>)meta.custom_metadata.hash_val2, (bit<16>)meta.custom_metadata.count_val2); *)
        register_write "heavy_hitter_counter2_set_heavy_hitter_count" 
          (var meta.custom_metadata.hash_val2)
          (var meta.custom_metadata.count_val2)
      ] |> List.concat
  in
  let set_heavy_hitter_count_table =
    instr_table (
      "set_heavy_hitter_count_table",
      [], [
        set_heavy_hitter_count;
        nop (*Unspecified default action, assuming nop*);
      ]
    )
  in
  let _drop =
    [], Primitives.Action.[
        assign standard_metadata.egress_spec @@ bvi 511 9
      ]
  in
  let drop_heavy_hitter_table =
    instr_table (
      "drop_heavy_hitter_table",
      [],[
        _drop;
        nop (*Unspecified default action, assuming nop*)
      ]
    )
  in
  let set_nhop  =
    let nhop_ipv4 = Var.make "nhop_ipv4" 32 in
    let port = Var.make "port" 9 in
    [nhop_ipv4; port], Primitives.Action.[
        assign meta.custom_metadata.nhop_ipv4 @@ var nhop_ipv4;
        assign standard_metadata.egress_spec @@ var port;
        assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8);
      ]
  in
  let ipv4_lpm =
    instr_table (
      "ipv4_lpm",
      [hdr.ipv4.dstAddr, Maskable], [
        set_nhop; _drop;
        nop (*Unspecified default action, assuming nop*)
      ]
    )
  in
  let set_dmac =
    let dmac = Var.make "dmac" 48 in
    [dmac], Primitives.Action.[
        assign hdr.ethernet.dstAddr @@ var dmac
      ]
  in
  let forward =
    instr_table (
      "forward",
      [meta.custom_metadata.nhop_ipv4, Exact],[
        set_dmac; _drop;
        nop (*Unspecified default action, assuming nop*)  
      ]
    )
  in
  sequence [
    begin if fixed then assume @@ ands_ [
        eq_ btrue @@ var hdr.ipv4.isValid;
        eq_ btrue @@ var hdr.tcp.isValid;
      ]
    else skip end;
    set_heavy_hitter_count_table;
    ifte_seq (ands_ [
        ugt_ (var meta.custom_metadata.count_val1) (bvi 100 16);
        ugt_ (var meta.custom_metadata.count_val2) (bvi 100 16);
      ]) [
      drop_heavy_hitter_table;
    ] [
      ipv4_lpm;
      forward
    ]
  ]

let hh2_egress =
  let open HoareNet in
  let open Expr in
  let rewrite_mac =
    let smac = Var.make "smac" 48 in
    [smac], Primitives.Action.[
      assign hdr.ethernet.srcAddr @@ var smac
    ]
  in
  let _drop = [], Primitives.Action.[
      assign standard_metadata.egress_spec @@ bvi 511 9
    ]
  in
  let send_frame =
    instr_table ("send_frame",
                  [standard_metadata.egress_port, Exact],
                  [
                    rewrite_mac; _drop;
                    nop (*Unspecified default action, assuming nop*)
                  ]
                )
  in
  send_frame

let heavy_hitter_2 fixed =
  pipeline hh2_parser (hh2_ingress fixed) hh2_egress
