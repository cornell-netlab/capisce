open Core
open Pbench

let () = Pbench.Log.override ()


let vlan_100 = (Bigint.of_int 100, 12)
let port_1 = (Bigint.of_int 1, 9)
let src_mac = (Bigint.of_int 1, 32)
let dst_mac = (Bigint.of_int 2, 32)
let mpls_10 = (Bigint.of_int 10, 20)

let get_info_from_p4 source =
  Log.debug_s "Parsing 99";
  let _,coq_pipe = P4Parse.tbl_abstraction_from_file ["./examples/includes"] source 1000 1 false true in
  Log.debug_s "Compiling to GPL";
  let pipe = Translate.gcl_to_gpl coq_pipe in
  Log.debug_s "Computing tables";
  let tables = ASTs.GPL.(tables @@ normalize_names pipe) in
  Log.debug_s "Computing symbolic interface";
  let cvs =
    List.bind tables ~f:(Primitives.Table.symbolic_interface)
    |> List.map ~f:(fun x -> if Var.is_indexed x then x else Var.index x 0)
  in
  Log.debug_s "passifying tables keys";
  let tables =
    let open List.Let_syntax in
    let%map t = tables in
    {t with keys = List.map t.keys ~f:(fun k -> Var.index k 0)}
  in
  Log.debug_s "all info got";
  (tables, cvs)
   (* ASTs.(GPL.(seq prsr pipe |> normalize_names |> encode_tables |> Psv.passify |> snd |> Psv.vars))) *)

let parse_smtlib source filepaths =
  let open List.Let_syntax in
  Log.debug "Getting vars from: %s" @@ lazy source;
  let tables, cvs = get_info_from_p4 source in
  let%map filepath = filepaths in
  Log.debug "reading smtlib file from: %s " @@ lazy filepath;
  let cpf_string = In_channel.read_all filepath in
  Log.debug_s "cpf read, parsing";
  let cpf = Pbench.Solver.of_smtlib ~dvs:[] ~cvs cpf_string in
  (cvs, tables, cpf, filepath)

let fabric =
  let psis =
    List.init 700 ~f:Fn.id
    |> List.map ~f:(Printf.sprintf "fabric_cpis/slice_700_%d")
    |> parse_smtlib "./examples/bf4_failing/fabric_no_consts.p4"
  in
  Log.debug_s "got_cpis";
  psis

let empty_control_plane =
  let module Schema = Primitives.Table in
  let open Table.ORG in
  String.Map.of_alist_exn [
    ("ingress_port_vlan",
     Default ({ id=(Bigint.zero, 2);
                data=[];
                dont_care=[true;true;true]}));
    ("fwd_classifier",
     Default ({id=(Bigint.zero, 1);
               data=[(Bigint.zero,3)];
               dont_care=[true;true;true;true]
              })
    );
    ("bridging",
     Default ({id=(Bigint.one, 2);
               data=[];
               dont_care=[true;true]
              })
    );
    ("mpls",
     Default ({id=(Bigint.one, 2);
               data=[];
               dont_care=[true]
              })
    );
    ("routing_v4",
     Default ({id=(Bigint.of_int 2, 2);
               data=[];
               dont_care=[true];
              })
    );
    ("next_mpls",
     Default ({id=(Bigint.one, 2);
               data=[];
               dont_care=[true]
              })
    );
    ("next_vlan",
     Default ({id=(Bigint.one, 2);
               data=[];
               dont_care=[true]
              })
    );
    ("acl",
     Default ({id=(Bigint.of_int 4, 3);
               data=[];
               dont_care=[true; (* standard_metadata.ingress_port*)
                          true; (* hdr.ethernet.dst_addr *)
                          true; (* hdr.ethernet.src_addr *)
                          true; (* hdr.vlan_tag.vlan_id *)
                          true; (* hdr.eth_type.value *)
                          true; (* fabric_md.lkp.ipv4_src *)
                          true; (* fabric_md.lkp.ipv4_dst *)
                          true; (* fabric_md.lkp.ip_proto *)
                          true; (* hdr.icmp.icmp_type *)
                          true; (* hdr.icmp.icmp_code *)
                          true; (* fabric_md.lkp.l4_sport *)
                          true; (* fabric_md.lkp.l4_dport *)
                          true; (* fabric_md.port_type *)
                         ]
              })
    );
    ("xconnect",
     Default ({id=(Bigint.of_int 2, 2);
               data=[];
               dont_care=[true;true]
              })
    );
    ("hashed",
     Default ({id=(Bigint.of_int 2, 2);
               data=[];
               dont_care=[true] (*;true;true;true;true;true]*)
              })
    );
    ("multicast",
     Default ({id=(Bigint.of_int 1, 2);
               data=[];
               dont_care=[true]
              })
    );
    ("egress_vlan",
     Default ({id=(Bigint.of_int 2, 2);
               data=[];
               dont_care=[true;true]
              })
    );
    ("classifier",
     Default ({id=(Bigint.of_int 0, 1);
               data=[ (Bigint.zero, 4); (*DEFAULT_SLICE_ID*)
                      (Bigint.zero, 2); (*DEFAULT_TC*)
                    ];
               dont_care=[true;true;true;true;true;true]
       })
    );
    ("queues",
     Default ({id=(Bigint.zero, 1);
               data=[(Bigint.zero, 5)];
               dont_care=[true;true;true];
              })
    );
    ("rewriter",
     Default ({id=(Bigint.of_int 2, 2);
               data=[];
               dont_care=[true];
              })
    );
  ]

let valid_fabric_tables name map =
  let open List.Let_syntax in
  let test_case_name file =  Printf.sprintf "[fabric_ptf] %s formula %s" name file in
  let%map cvs, schemata, cpf, cpf_filepath = fabric in
  let control_plane = Table.zip schemata map in
  Log.debug_s "Checking state";
  begin fun () ->
    Monitor.check_state cvs control_plane FabricInfo.info cpf
    |> Alcotest.(check bool) "control plane is a satisfying instance" true
  end
  |> Alcotest.test_case (test_case_name cpf_filepath) `Quick

let fabric_ptf runtime name =
  runtime
  |> Runtime.to_control_plane FabricInfo.info empty_control_plane
  |> valid_fabric_tables name

let tests : unit Alcotest.test_case list =
  List.bind ~f:Fn.id  [
    "TEST empty control plane"
    |> fabric_ptf [];
    "TEST bridging_0"
    |> fabric_ptf PTFBridging.test_0;
    "TEST bridging_1"
    |> fabric_ptf PTFBridging.test_1;
    "TEST bridging_2"
    |> fabric_ptf PTFBridging.test_2;
    "TEST bridging_3"
    |> fabric_ptf PTFBridging.test_3;
    "TEST bridging_4"
    |> fabric_ptf PTFBridging.test_4;
    "TEST bridging_5"
    |> fabric_ptf PTFBridging.test_5;
    "TEST bridging_6"
    |> fabric_ptf PTFBridging.test_6;
    "TEST bridging_7"
    |> fabric_ptf PTFBridging.test_7;
    "TEST bridging_8"
    |> fabric_ptf PTFBridging.test_8;
    "TEST bridging_9"
    |> fabric_ptf PTFBridging.test_9;
    "TEST bridging_10"
    |> fabric_ptf PTFBridging.test_10;
    "TEST bridging_11"
    |> fabric_ptf PTFBridging.test_11;
    "TEST FabricArpBroadcastMixedTest"
    |> fabric_ptf PTFFabricArpBroadcastMixedTest.test;
    "TEST FabricArpBroadcastTaggedTest"
    |> fabric_ptf PTFFabricArpBroadcastTaggedTest.test;
    "TEST FabricArpBroadcastUntaggedTest"
    |> fabric_ptf PTFFabricArpBroadcastUntaggedTest.test;
    "TEST FabricArpPacketInTest"
    |> fabric_ptf PTFFabricArpPacketInTest.test;
    (* "Test FabricArpPacketOutTest" *)
    (*  No Log is generated for this test! *)
    (* |> fabric_ptf PTFFabricArpPacketOutTest.test; *)
    "Test FabricDoubleVlanXConnectTest 0"
    |> fabric_ptf PTFFabricDoubleVlanXConnectTest.test_0;
    "Test FabricDoubleVlanXConnectTest 1"
    |> fabric_ptf PTFFabricDoubleVlanXConnectTest.test_1;
    "Test FabricDoubleVlanXConnectTest 2"
    |> fabric_ptf PTFFabricDoubleVlanXConnectTest.test_2;
    "TEST FabricGtpEndMarkerPacketOut 0"
    |> fabric_ptf PTFFabricGtpEndMarkerPacketOut.test_0;
    "TEST FabricGtpEndMarkerPacketOut 1"
    |> fabric_ptf PTFFabricGtpEndMarkerPacketOut.test_1;
    "TEST FabricIPv4DefaultRouteTest"
    |> fabric_ptf PTFFabricIPv4DefaultRouteTest.test;
    "TEST IPv4DoNotOverrideInfraTest 0"
    |> fabric_ptf PTFFabricIPv4DoNotOverrideInfraTest.test_0;
    "TEST IPv4DoNotOverrideInfraTest 1"
    |> fabric_ptf PTFFabricIPv4DoNotOverrideInfraTest.test_1;
    "TEST IPv4DoNotOverrideInfraTest 2"
    |> fabric_ptf PTFFabricIPv4DoNotOverrideInfraTest.test_2;
  ]
