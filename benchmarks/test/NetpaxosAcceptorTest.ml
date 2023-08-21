open Pbench
open DependentTypeChecker
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
  let open HoareNet in
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

let npa_ingress =
  let open HoareNet in
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
    instr_table ("fwd_tbl",
                 [`Exact standard_metadata.ingress_port],
                 [forward; _drop])
  in
  let read_round =
    [], Primitives.Action.[assert_ @@ eq_ btrue @@ var hdr.paxos.isValid]
    (*proposal_register.read(meta.local_metadata.proposal, hdr.paxos.inst)*)
  in
  let round_tbl =
    instr_table ("round_tbl", [], [read_round])
  in
  let _no_op = [],[] in
  let handle_phase1a =
    [], Primitives.Action.[
        assert_ @@ eq_ btrue @@ var hdr.paxos.isValid;
        (* proposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal); *)
        assert_ @@ eq_ btrue @@ var hdr.paxos.isValid;
        (* vproposal_register.read(hdr.paxos.vproposal, (bit<32>)hdr.paxos.inst); *)
        assert_ @@ eq_ btrue @@ var hdr.paxos.isValid;
        (* val_register.read(hdr.paxos.val, (bit<32>)hdr.paxos.inst); *)
        assign hdr.paxos.msgtype @@ bvi 2 16;
        (* acceptor_id.read(hdr.paxos.acpt, (bit<32>)32w0); *)
        (* assert_ @@ eq_ btrue @@ var hdr.udp.isValid; *)
        assign hdr.udp.checksum @@ bvi 0 16
      ]
  in
  let handle_phase2a =
    [], Primitives.Action.[
        assert_ @@ eq_ btrue @@ var hdr.paxos.isValid;
        (* proposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal); *)
        assert_ @@ eq_ btrue @@ var hdr.paxos.isValid;
        (* vproposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal); *)
        assert_ @@ eq_ btrue @@ var hdr.paxos.isValid;
        (* val_register.write((bit<32>)hdr.paxos.inst, (bit<32>)hdr.paxos.val); *)
        (* assert_ @@ eq_ btrue @@ var hdr.paxos.isValid; *)
        assign hdr.paxos.msgtype @@ bvi 4 16;
        (* assert_ @@ eq_ btrue @@ var hdr.paxos.isValid; *)
        assign hdr.paxos.vproposal @@ var hdr.paxos.proposal;
        (* acceptor_id.read(hdr.paxos.acpt, (bit<32>)32w0); *)
        (* assert_ @@ eq_ btrue @@ var hdr.udp.isValid; *)
        assign hdr.udp.checksum @@ bvi 0 16;
      ]
  in
  let paxos_tbl =
    sequence [
      (* assert_ @@ eq_ btrue @@ var hdr.paxos.isValid; *)
      instr_table ("paxos_tbl",
                   [ `Exact hdr.paxos.msgtype ],
                   [ handle_phase1a;
                     handle_phase2a;
                     _no_op;
                   ])
    ]
  in
  let drop_tbl =
    table ("drop_tbl", [], [_drop])
  in
  sequence [
    ifte_seq (eq_ (var hdr.ipv4.isValid) btrue)
      [fwd_tbl]
      [];
    ifte_seq (eq_ (var hdr.paxos.isValid) btrue)
      [round_tbl;
       ifte_seq (ule_ (var meta.local_metadata.proposal) (var hdr.paxos.proposal))
         [paxos_tbl]
         [drop_tbl]
      ] []
  ]


let npa_egress = HoareNet.skip

let npa =
  pipeline npa_parser npa_ingress npa_egress
  |> HoareNet.assert_valids

(*TESTS*)

let test_annotations () =
  HoareNet.check_annotations npa
  |> Alcotest.(check bool) "check_annotations should pass" true

let test_enum () =
  HoareNet.infer ~qe:`Enum npa None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is Valid using enum"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc npa None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid using concolic"
    BExpr.true_

let tests = [
  Alcotest.test_case "netpaxos_acceptor annotations" `Quick test_annotations;
  Alcotest.test_case "netpaxos_acceptor enum" `Quick test_enum;
  Alcotest.test_case "netpaxos_acceptor concolic" `Quick test_concolic;

]
