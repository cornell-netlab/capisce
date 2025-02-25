open Core
open Capisce
open ASTs.GPL
open V1ModelUtils

type location_t = {
  index : Var.t
}

let location : location_t = {
index = Var.make "meta.location.index" 16;
}

type my_md_t = {
  ipaddress : Var.t;
  role : Var.t;
  failed : Var.t;
}

let my_md : my_md_t =
  let f s w = Var.make (Printf.sprintf "meta.my_md.%s" s) w in
  {
    ipaddress = f "ipaddress" 32;
    role = f "role" 16;
    failed = f "failed" 16;
  }

type reply_addr_t = {
  ipv4_srcAddr : Var.t;
  ipv4_dstAddr : Var.t
}

let reply_to_client_md =
  let f s w = Var.make (Printf.sprintf "meta.reply_to_client_md.%s" s) w in
  {
    ipv4_srcAddr = f "ipv4_srcAddr" 32;
    ipv4_dstAddr = f "ipv4_dstAddr" 32;
  }

type sequence_md_t = {
  seq : Var.t;
  tmp : Var.t
}

let sequence_md : sequence_md_t =
  let f s w = Var.make (Printf.sprintf "meta.sequence_md.%s" s) w in
  {
    seq = f "seq" 16;
    tmp = f "tmp" 16
  }

type metadata_t = {
  location : location_t;
  my_md : my_md_t;
  reply_to_client_md : reply_addr_t;
  sequence_md : sequence_md_t;
}
let meta : metadata_t = {
  location;
  my_md;
  reply_to_client_md;
  sequence_md;
}

type overlay_t =
  { isValid : Var.t;
    swip : Var.t;
  }

let overlay i : overlay_t =
  let field f sz = Var.make (Printf.sprintf "hdr.overlay_%d_.%s" i f) sz in
  { isValid = field "isValid" 1;
    swip = field "swip" 32}

let overlay_pop_front ident max i =
  let open BExpr in
  let open Expr in
  let rec pop_front_aux cur =
    let cur_header = overlay cur in 
    let next_header_index = Int.(cur + i) in
    let havoc_var = Printf.sprintf "havoc_%s_%i" ident next_header_index in
    let havoc hdr = havoc hdr havoc_var |> active in
    if next_header_index >= max then
      [ assign cur_header.isValid bfalse;
        havoc cur_header.swip;
      ]
    else
      let next_header = overlay next_header_index in
      [
        assign cur_header.isValid @@ Expr.var next_header.isValid;
        ifte_seq (eq_ btrue @@ var next_header.isValid) [
          assign cur_header.swip @@ Expr.var next_header.swip;
        ] [
          havoc cur_header.swip
        ]
        ] @ pop_front_aux Int.(cur + 1)
  in
  pop_front_aux 0

let netchain_parser =
  let open Expr in
  let open BExpr in
  let parse_nc_hdr =
    sequence [
      assign hdr.nc_hdr.isValid btrue;
      (* transition select(hdr.nc_hdr.op) { *)
      (*     8w10: accept; *)
      (*     8w12: accept; *)
      (*     default: accept; *)
      (* } *)
      transition_accept
    ]
  in
  let rec parse_overlay (i : Int.t) =
    if Int.(i >= 7) then
      sequence [
        assign (overlay 7).isValid btrue;
        assume @@ eq_ (bvi 0 32) @@ var (overlay 7).swip;
        parse_nc_hdr
      ]
    else
      sequence [
        assign (overlay i).isValid btrue;
        ifte (eq_ (bvi 0 32) @@ var (overlay i).swip)
          parse_nc_hdr
          (parse_overlay @@ Int.(i + 1))
      ]
  in
  let parse_udp =
    sequence [
      assign hdr.udp.isValid btrue;
      select (var hdr.udp.dstPort) [
        bvi 8888 16, parse_overlay 0;
        bvi 8889 16, parse_overlay 0
      ] transition_accept
    ]
  in
  let parse_tcp =
    sequence [
      assign hdr.tcp.isValid btrue;
      transition_accept
    ]
  in
  let parse_ipv4 =
    sequence [
      assign hdr.ipv4.isValid btrue;
      select (var hdr.ipv4.protocol) [
        bvi 6  8, parse_tcp;
        bvi 17 8, parse_udp;
      ] transition_accept
    ]
  in
  let parse_ethernet =
    sequence [
      assign hdr.ethernet.isValid btrue;
      select (var hdr.ethernet.etherType) [
        bvi 2048 16, parse_ipv4
      ] transition_accept
    ]

  in
  let start =
    parse_ethernet
  in
  sequence [
    assign hdr.ethernet.isValid bfalse;
    assign hdr.ipv4.isValid bfalse;
    assign hdr.tcp.isValid bfalse;
    assign hdr.udp.isValid bfalse;
    assign (overlay 0).isValid bfalse;
    assign (overlay 1).isValid bfalse;
    assign (overlay 2).isValid bfalse;
    assign (overlay 3).isValid bfalse;
    assign (overlay 4).isValid bfalse;
    assign (overlay 5).isValid bfalse;
    assign (overlay 6).isValid bfalse;
    assign (overlay 7).isValid bfalse;
    assign (overlay 8).isValid bfalse;
    assign (overlay 9).isValid bfalse;
    assign hdr.nc_hdr.isValid bfalse;
    start
  ]

let netchain_psm =
  let open EmitP4.Parser in 
  let open Expr in 
  let parse_overlay_name i = Printf.sprintf "parse_overlay_%d" i in 
  let parse_overlay (i : Int.t) : state =
    let post =
      let open ASTs.GCL in 
      if Int.(i >= 7) then
        assign (overlay 7).swip @@ bvi 0 32
      else 
        skip
    in
    let transition = 
      if Int.(i >= 7) then 
        direct "accept"
      else
        select (overlay i).swip [
          bvi 0 32, "parse_nc_header"
        ] (parse_overlay_name Int.(i + 1))
    in
    state (parse_overlay_name i) 
      (overlay i).isValid 
      ~post 
      transition
  in
  of_state_list @@ [
    noop_state "start" "parse_ethernet"
    ;
    state "parse_ethernet" hdr.ethernet.isValid @@
    select hdr.ethernet.etherType [
      bvi 2048 16, "parse_ipv4";
    ] "accept"
    ;
    state "parse_ipv4" hdr.ipv4.isValid @@
    select hdr.ipv4.protocol [
      bvi  6 8, "parse_tcp";
      bvi 17 8, "parse_udp"
    ] "accept"
    ;
    state "parse_tcp" hdr.tcp.isValid @@
    direct "accept"
    ;
    state "parse_udp" hdr.udp.isValid @@
    select hdr.udp.dstPort [
      bvi 8888 16, parse_overlay_name 0;
      bvi 8889 16, parse_overlay_name 0
    ] "accept"
    ;
    state "parse_nc_header" hdr.nc_hdr.isValid @@
    direct "accept"
    ;
  ] @ List.init 8 ~f:parse_overlay

let netchain_ingress =
  let open Expr in
  let open BExpr in
  let open Primitives in
  let get_my_address_act =
    let sw_ip = Var.make "sw_ip" 32 in
    let sw_role = Var.make "sw_role" 16 in
    [sw_ip;sw_role], Action.[
      assign meta.my_md.ipaddress (var sw_ip);
      assign meta.my_md.role (var sw_role)
    ]
  in
  let get_my_address = 
   table "get_my_address"
      [hdr.nc_hdr.op, Exact]
      [
        get_my_address_act;
        nop (*Unspecified default action, assuming nop*)
      ]
  in
  let find_index_act = 
    let index = Var.make "index" 16 in
    [index], Action.[
      assign meta.location.index (var index);
    ]
  in
  let find_index = 
    table "find_index"
      [hdr.nc_hdr.key, Exact]
      [
        find_index_act;
        nop (*Unspecified default action, assuming nop*)
      ]
  in
  let get_sequence_act =
    [], 
      (* sequence_reg.read(meta.sequence_md.seq, (bit<32>)meta.location.index); *)
      register_read "sequence_reg_get_sequence_act" meta.sequence_md.seq (var meta.location.index);
    
  in
  let get_sequence =
    table "get_sequence" [] [
      get_sequence_act;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  let read_value_act =
    [], 
      (* value_reg.read(hdr.nc_hdr.value, (bit<32>)meta.location.index); *)
      register_read "value_reg_read_value_act" hdr.nc_hdr.value (var meta.location.index)
  in
  let read_value =
    table "read_value" [] [
      read_value_act;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  let maintain_sequence_act =
    [], Action.[
      [assign meta.sequence_md.seq @@ badd (var meta.sequence_md.seq) (bvi 1 16)];
      (* sequence_reg.write((bit<32>)meta.location.index, (bit<16>)meta.sequence_md.seq); *)
      register_write "sequence_reg_maintain_sequence_act" (var meta.location.index) (var meta.sequence_md.seq);
      (* sequence_reg.read(hdr.nc_hdr.seq, (bit<32>)meta.location.index); *)
      register_read "sequence_reg_maintain_sequence_act" hdr.nc_hdr.seq (var meta.location.index)
    ] |> List.concat
  in
  let maintain_sequence =
    table "maintain_sequence" [] [
      maintain_sequence_act;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  let assign_value_act = 
    [], 
      (* sequence_reg.write((bit<32>)meta.location.index, (bit<16>)hdr.nc_hdr.seq); *)
      register_write "sequence_reg_assign_value_act" (var meta.location.index) (var hdr.nc_hdr.seq) @
      (* value_reg.write((bit<32>)meta.location.index, (bit<128>)hdr.nc_hdr.value);  *)
      register_write "value_reg_assign_value_act" (var meta.location.index) (var hdr.nc_hdr.value)
  in
  let assign_value =
    table "assign_value" [] [
      assign_value_act;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  let did_pop_front = Var.make "did_pop_front" 1 in
  let pop_chain_act = 
    [], Action.[
      assign hdr.nc_hdr.sc @@ badd (var hdr.nc_hdr.sc) (bvi 255 8);
      (* hdr.overlay.pop_front(1); *)
      assign did_pop_front btrue;
      assign hdr.udp.length @@ badd (var hdr.udp.length) (bvi 65532 16);
      assign hdr.ipv4.totalLen @@ badd (var hdr.ipv4.totalLen) (bvi 65532 16);
    ]
  in
  let pop_chain =
    sequence [
      assign did_pop_front bfalse;
      table "pop_chain" [] [
        pop_chain_act;
        nop (*Unspecified default action, assuming nop*)
      ];
      ifte_seq (eq_ btrue @@ var did_pop_front) 
        (overlay_pop_front "pop_chain" 9 1) [];
    ]
  in
  let drop_packet_act = 
    [], [mark_to_drop]
  in
  let drop_packet =
    table "drop_packet" [] [
      drop_packet_act;
      nop (*Unspecified default action, assuming nop*)
    ]
  in
  let failover_act = [], Action.[
    assign hdr.ipv4.dstAddr @@ var @@ (overlay 1).swip] 
    @ snd pop_chain_act
  in
  let failover_write_reply_act = [],Action.[
      assign meta.reply_to_client_md.ipv4_srcAddr @@ var hdr.ipv4.dstAddr;
      assign meta.reply_to_client_md.ipv4_dstAddr @@ var hdr.ipv4.srcAddr;
      assign hdr.ipv4.srcAddr @@ var meta.reply_to_client_md.ipv4_srcAddr;
      assign hdr.ipv4.dstAddr @@ var meta.reply_to_client_md.ipv4_dstAddr;
      assign hdr.nc_hdr.op @@ bvi 13 8;
      assign hdr.udp.dstPort @@ bvi 8889 16;
  ] in
  let failure_recovery_act = 
    let nexthop = Var.make "nexthop" 32 in
    [nexthop], Action.[
    assign (overlay 0).swip @@ var nexthop;
    assign hdr.ipv4.dstAddr @@ var nexthop;
  ] in
  let nop = [],[] in
  let failure_recovery =
    table "failure_recovery"
    [ hdr.ipv4.dstAddr, Maskable;
      (overlay 1).swip, Maskable;
      hdr.nc_hdr.vgroup, Maskable;
    ]
    [failover_act; failover_write_reply_act; 
    failure_recovery_act; nop; drop_packet_act]
    (*Unspecified default action, assuming extant nop*)
  in
  let set_egress =
    let egress_spec = Var.make "egress_spec" 9 in
    [egress_spec], Action.[
      assign standard_metadata.egress_spec @@ var egress_spec;
      assign hdr.ipv4.ttl @@ badd (var hdr.ipv4.ttl) (bvi 255 8);
    ]
  in
  let ipv4_route =  
      table "ipv4_route"
        [hdr.ipv4.dstAddr, Exact]
        [
          set_egress;
          nop (*Unspecified default action, assuming nop*)
        ]
  in
  sequence [
    ifte_seq (eq_ (var hdr.nc_hdr.isValid) btrue) [
      get_my_address;
      ifte_seq (eq_ (var hdr.ipv4.dstAddr) (var meta.my_md.ipaddress)) [
        find_index;
        get_sequence;
        ifte_seq (eq_ (var hdr.nc_hdr.op) (bvi 10 8)) [ 
         read_value 
        ] [ 
          ifte_seq (eq_ (var hdr.nc_hdr.op) (bvi 12 8)) [ 
            ifte_seq (eq_ (var meta.my_md.role) (bvi 100 16)) [ 
              maintain_sequence
            ] []; 
            ifte_seq (or_ (eq_ (var meta.my_md.role) (bvi 10051 16)) (ugt_ (var hdr.nc_hdr.seq) (var meta.sequence_md.seq))) [ 
              assign_value; 
              pop_chain; 
            ] [ 
              drop_packet 
            ]
          ] [] 
        ] 
      ] [] 
    ] [];
    ifte_seq (eq_ (var hdr.nc_hdr.isValid) btrue) [
      failure_recovery
    ] [];
    ifte_seq (or_ (eq_ (var hdr.tcp.isValid) btrue) (eq_ (var hdr.udp.isValid) btrue)) [
      ipv4_route
    ] []
  ]

let netchain_egress =
  let open Expr in
  let open Primitives in
  let ethernet_set_mac_act =
    let smac = Var.make "smac" 48 in
    let dmac = Var.make "dmac" 48 in
    [smac; dmac],
    Action.[
      assign hdr.ethernet.srcAddr @@ var smac;
      assign hdr.ethernet.dstAddr @@ var dmac
    ]

  in
  let ethernet_set_mac =
    table "ethernet_set_mac"
      [standard_metadata.egress_spec, Exact]
      [ 
        ethernet_set_mac_act;
        nop (*Unspecified default action, assuming nop*)
      ]
  in
  ethernet_set_mac

let netchain =
  netchain_psm, netchain_ingress, netchain_egress
