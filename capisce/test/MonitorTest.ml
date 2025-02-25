 open Core 
 open Capisce

 let () = Log.override () 


 let vlan_100 = (Bigint.of_int 100, 12) 
 let port_1 = (Bigint.of_int 1, 9) 
 let src_mac = (Bigint.of_int 1, 32) 
 let dst_mac = (Bigint.of_int 2, 32) 
 let mpls_10 = (Bigint.of_int 10, 20) 

 let get_info_from_program prog = 
   let tables = ASTs.GPL.(tables prog) in 
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

 let parse_smtlib source filepaths = 
   let open List.Let_syntax in 
   let gpl = DependentTypeChecker.HoareNet.annotated_to_gpl source in
   let tables, cvs = get_info_from_program gpl in 
   let%map filepath = filepaths in 
   let cpf_string = In_channel.read_all filepath in 
   let cpf = Solver.of_smtlib ~dvs:[] ~cvs cpf_string in 
   (cvs, tables, cpf, filepath) 

 let fabric () = 
   (* let total = 700 in *) 
   let total = 1 in 
   let psis = 
     List.init total ~f:Fn.id 
     |> List.map ~f:(Printf.sprintf "fabric_cpis/slice_%d_%d" total) 
     |> parse_smtlib (Programs.Fabric.fabric true)
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
                data=[(Bigint.zero, 3)]; 
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
  let%map cvs, schemata, cpf, cpf_filepath = fabric () in
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
    "TEST IPv4MPLSTest"
    |> fabric_ptf PTFFabricIPv4MPLSTest.test;
    "TEST FabricIPv4MplsDoNotOverrideTest 0"
    |> fabric_ptf PTFFabricIPv4MplsDoNotOverrideTest.test_0;
    "TEST FabricIPv4MplsDoNotOverrideTest 1"
    |> fabric_ptf PTFFabricIPv4MplsDoNotOverrideTest.test_1;
    "TEST FabricIPv4MplsDoNotOverrideTest 2"
    |> fabric_ptf PTFFabricIPv4MplsDoNotOverrideTest.test_2;
    "TEST FabricIPv4MplsDoNotOverrideTest 3"
    |> fabric_ptf PTFFabricIPv4MplsDoNotOverrideTest.test_3;
    "TEST FabricIPv4MplsDoNotOverrideTest 4"
    |> fabric_ptf PTFFabricIPv4MplsDoNotOverrideTest.test_4;
    "TEST FabricIPv4MplsDoNotOverrideTest 5"
    |> fabric_ptf PTFFabricIPv4MplsDoNotOverrideTest.test_5;
    "TEST FabricIPv4MplsOverrideEdgeTest 0"
    |> fabric_ptf PTFFabricIPv4MplsOverrideEdgeTest.test_0;
    "TEST FabricIPv4MplsOverrideEdgeTest 1"
    |> fabric_ptf PTFFabricIPv4MplsOverrideEdgeTest.test_1;
    "TEST FabricIPv4MplsOverrideEdgeTest 2"
    |> fabric_ptf PTFFabricIPv4MplsOverrideEdgeTest.test_2;
    "TEST FabricIPv4MplsOverrideEdgeTest 3"
    |> fabric_ptf PTFFabricIPv4MplsOverrideEdgeTest.test_3;
    "TEST FabricIPv4MplsOverrideEdgeTest 4"
    |> fabric_ptf PTFFabricIPv4MplsOverrideEdgeTest.test_4;
    "TEST FabricIPv4MplsOverrideEdgeTest 5"
    |> fabric_ptf PTFFabricIPv4MplsOverrideEdgeTest.test_5;
    "TEST FabricIPv4nicastAclOuterDropTest"
    |> fabric_ptf PTFFabricIPv4UnicastAclOuterDropTest.test;
    "Test FabricIPv4UnicastGroupTest"
    |> fabric_ptf PTFFabricIPv4UnicastGroupTest.test;
    "TEST FabricIPv4UnicastGroupTestAllPortIpDst 1"
    |> fabric_ptf PTFFabricIPv4UnicastGroupTestAllPortIpDst.test_1;
    "TEST FabricIPv4UnicastGroupTestAllPortIpDst 2"
    |> fabric_ptf PTFFabricIPv4UnicastGroupTestAllPortIpDst.test_2;
    "TEST PTFFabricIPv4UnicastGroupTestAllPortIpSrc 0"
    |> fabric_ptf PTFFabricIPv4UnicastGroupTestAllPortIpSrc.test_0;
    "TEST PTFFabricIPv4UnicastGroupTestAllPortIpSrc 1"
    |> fabric_ptf PTFFabricIPv4UnicastGroupTestAllPortIpSrc.test_1;
    "TEST FabricIPv4UnicastGroupTestAllPortTcpDport"
    |> fabric_ptf PTFFabricIPv4UnicastGroupTestAllPortTcpDport.test;
    "TEST FabricIPv4UnicastGtpAclInnerDropTest"
    |> fabric_ptf PTFFabricIPv4UnicastGtpAclInnerDropTest.test;
    "TEST FabricIPv4UnicastGtpTest"
    |> fabric_ptf PTFFabricIPv4UnicastGtpTest.test;
    "TEST FabricIPv4UnicastTest 0"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_0;
    "TEST FabricIPv4UnicastTest 1"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_1;
    "TEST FabricIPv4UnicastTest 2"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_2;
    "TEST FabricIPv4UnicastTest 3"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_3;
    "TEST FabricIPv4UnicastTest 4"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_4;
    "TEST FabricIPv4UnicastTest 5"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_5;
    "TEST FabricIPv4UnicastTest 6"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_6;
    "TEST FabricIPv4UnicastTest 7"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_7;
    "TEST FabricIPv4UnicastTest 8"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_8;
    "TEST FabricIPv4UnicastTest 9"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_9;
    "TEST FabricIPv4UnicastTest 10"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_10;
    "TEST FabricIPv4UnicastTest 11"
    |> fabric_ptf PTFFabricIPv4UnicastTest.test_11;
    "TEST FabricIpv4UnicastFromPacketOutTest 0"
    |> fabric_ptf PTFFabricIpv4UnicastFromPacketOutTest.test_0;
    "TEST FabricIpv4UnicastFromPacketOutTest 1"
    |> fabric_ptf PTFFabricIpv4UnicastFromPacketOutTest.test_1;
    "TEST FabricIpv4UnicastFromPacketOutTest 2"
    |> fabric_ptf PTFFabricIpv4UnicastFromPacketOutTest.test_2;
    "TEST FabricIpv4UnicastFromPacketOutTest 3"
    |> fabric_ptf PTFFabricIpv4UnicastFromPacketOutTest.test_3;
    "TEST FabricIpv4UnicastFromPacketOutTest 4"
    |> fabric_ptf PTFFabricIpv4UnicastFromPacketOutTest.test_4;
    "TEST FabricIpv4UnicastFromPacketOutTest 5"
    |> fabric_ptf PTFFabricIpv4UnicastFromPacketOutTest.test_5;
    "TEST FabricLongIpPacketInTest"
    |> fabric_ptf PTFFabricLongIpPacketInTest.test;
    (* "TEST FabricLongIpPacketOutTest" *)
    (* |> fabric_ptf PTFFabricLongIpPacketOutTest.test; *)
    "TEST FabricMplsSegmentRoutingTest 0"
    |> fabric_ptf PTFFabricMplsSegmentRoutingTest.test_0;
    "TEST FabricMplsSegmentRoutingTest 1"
    |> fabric_ptf PTFFabricMplsSegmentRoutingTest.test_1;
    "TEST FabricMplsSegmentRoutingTest 2"
    |> fabric_ptf PTFFabricMplsSegmentRoutingTest.test_2;
    "TEST FabricMplsSegmentRoutingTest 3"
    |> fabric_ptf PTFFabricMplsSegmentRoutingTest.test_3;
    "TEST FabricMplsSegmentRoutingTest 4"
    |> fabric_ptf PTFFabricMplsSegmentRoutingTest.test_4;
    "TEST FabricMplsSegmentRoutingTest 5"
    |> fabric_ptf PTFFabricMplsSegmentRoutingTest.test_5;
    "TEST FabricMplsSegmentRoutingTest 6"
    |> fabric_ptf PTFFabricMplsSegmentRoutingTest.test_6;
    "TEST PTFFabricShortIpPacketInTest"
    |> fabric_ptf PTFFabricShortIpPacketInTest.test;
    (* "TEST PTFFabricShortIpPacketOutTest" *)
    (* |> fabric_ptf PTFFabricShortIpPacketOutTest.test *)
    "TEST PTFFabricTaggedPacketInTest"
    |> fabric_ptf PTFFabricTaggedPacketInTest.test;
    "TEST PTFIPv4MplsGroupTest 0"
    |> fabric_ptf PTFIPv4MplsGroupTest.test_0;
    "TEST PTFIPv4MplsGroupTest 1"
    |> fabric_ptf PTFIPv4MplsGroupTest.test_1;
    "TEST PTFIPv4MplsGroupTest 2"
    |> fabric_ptf PTFIPv4MplsGroupTest.test_2;
    "TEST PTFIPv4MplsGroupTest 3"
    |> fabric_ptf PTFIPv4MplsGroupTest.test_3;
    "TEST PTFIPv4MplsGroupTest 4"
    |> fabric_ptf PTFIPv4MplsGroupTest.test_4;
    "TEST PTFIPv4MplsGroupTest 5"
    |> fabric_ptf PTFIPv4MplsGroupTest.test_5;
    "TEST PTFIPv4UnicastGroupTestAllPortTcpSport"
    |> fabric_ptf PTFIPv4UnicastGroupTestAllPortTcpSport.test;
  ]
