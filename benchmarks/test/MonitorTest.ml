open Core
open Pbench

let () = Pbench.Log.override ()


let vlan_100 = (Bigint.of_int 100, 12)
let port_1 = (Bigint.of_int 1, 9)
let src_mac = (Bigint.of_int 1, 32)
let dst_mac = (Bigint.of_int 2, 32)
let mpls_10 = (Bigint.of_int 10, 20)

let get_vars_from_p4 source =
  Log.debug_s "Parsing";
  let coq_gcl = P4Parse.tbl_abstraction_from_file ["./examples/includes"] source 1000 1 false true in
  Log.debug_s "Compiling to GPL";
  let (prsr, pipe) = Tuple2.map ~f:(Translate.gcl_to_gpl) coq_gcl in
  Log.debug_s "Computing variables";
  ASTs.(GPL.(seq prsr pipe |> normalize_names |> encode_tables |> Psv.passify |> snd |> Psv.vars))


let parse_smtlib source filepath =
  Log.debug "reading smtlib file from: %s " @@ lazy filepath;
  Log.debug "Getting vars from: %s" @@ lazy source;
  (* let _ = get_vars_from_p4 source |> List.filter ~f:Var.is_symbRow in *)
  let cpf_string = In_channel.read_all filepath in
  Pbench.Solver.of_smtlib ~dvs:[] cpf_string
    ~cvs:[
      Var.make "_symb$classifier$action$_$0" 2;
      Var.make "_symb$ingress_port_vlan$match_2$DONT_CARE$_$0" 1;
      Var.make "_symb$fwd_classifier$set_forwarding_type$arg$fwd_type$_$0" 1;
    ]

let fabric_cpf = parse_smtlib "./examples/bf4_failing/fabric_no_consts.p4" "fabric_output.log"

let valid_fabric_tables map =
  Monitor.check_state map fabric_cpf
  |> Option.is_none
  |> Alcotest.(check bool) "table state is valid" true

let test_case_test () =
  String.Map.of_alist_exn [
    "routing_v4", [Model.of_alist_exn [
      Var.make "_symb$routing_v4$action$_$0" 2, (Bigint.of_int 0, 2);
    ]];
    "classifier", [Model.of_alist_exn [
        Var.make "_symb$classifier$action$_$0" 2, (Bigint.of_int 0, 2);
        Var.make "_symb$classifier$arg_0$_$0" 4, (Bigint.of_int 0, 4);
        Var.make "_symb$classifier$arg_1$_$0" 2, (Bigint.of_int 0, 2);
      ]];
    "ingress_port_vlan", [Model.of_alist_exn [
        Var.make "_symb$ingress_port_vlan$match_2$DONT_CARE$_$0" 1, (Bigint.of_int 1, 1);
      ]
    ];
    "fwd_classifier", [Model.of_alist_exn [
      Var.make "_symb$fwd_classifier$set_forwarding_type$arg$fwd_type$_$0" 1, (Bigint.of_int 0, 0);
    ]
  ]
  ]  |> valid_fabric_tables

let test_routing_v4_treatment_empty () =
  (* https://github.com/opennetworkinglab/onos/blob/master/pipelines/fabric/impl/src/test/java/org/onosproject/pipelines/fabric/impl/behaviour/FabricInterpreterTest.java#L78 *)
  (* Routing V4: * -> NOP *)
  String.Map.empty
  |> valid_fabric_tables

let tests =
  [
    Alcotest.test_case "[Fabric] CPI passes trivial test case" `Quick test_case_test;
    Alcotest.test_case "[ONOS Test] testRoutingV4TreatmentEmpty" `Quick test_routing_v4_treatment_empty;
  ]
