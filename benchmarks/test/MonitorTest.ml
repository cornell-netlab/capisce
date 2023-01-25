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
  Log.debug_s "passifying tables keys";
  let tables =
    let open List.Let_syntax in
    let%map t = tables in
    {t with keys = List.map t.keys ~f:(fun k -> Var.index k 0)}
  in
  Log.debug_s "Computing symbolic interface";
  let cvs =
    List.bind tables ~f:(Primitives.Table.symbolic_interface)
    |> List.map ~f:(fun x -> if Var.is_indexed x then x else Var.index x 0)
  in
  Log.debug_s "all info got";
  (tables, cvs)
   (* ASTs.(GPL.(seq prsr pipe |> normalize_names |> encode_tables |> Psv.passify |> snd |> Psv.vars))) *)

let parse_smtlib source filepath =
  Log.debug "reading smtlib file from: %s " @@ lazy filepath;
  Log.debug "Getting vars from: %s" @@ lazy source;
  let tables, cvs = get_info_from_p4 source in
  Log.debug "Got tables & variables: parsing smt from %s " @@ lazy filepath;
  let cpf_string = In_channel.read_all filepath in
  Log.debug_s "cpf read, parsing";
  let cpf = Pbench.Solver.of_smtlib ~dvs:[] ~cvs cpf_string in
  (cvs, tables, cpf)

let fabric () =
  let psi = parse_smtlib "./examples/bf4_failing/fabric_no_consts.p4" "fabric_output.log" in
  Log.debug_s "got_cpi";
  psi


let empty_control_plane =
  let module Schema = Primitives.Table in
  let open Table.ORG in
  String.Map.of_alist_exn [
    ("ingress_port_vlan",
     Default ({id=(Bigint.zero, 2); data=[]}));
    ("fwd_classifier",
     Default ({id=(Bigint.zero, 1); data=[(Bigint.zero,3)]})
    );
    ("bridging",
     Default ({id=(Bigint.one, 1); data=[]})
    );
    ("mpls",
     Default ({id=(Bigint.one, 1); data=[]})
    );
    ("routing_v4",
     Default ({id=(Bigint.of_int 2, 2); data=[]})
    );
    ("next_mpls",
     Default ({id=(Bigint.one, 1); data=[]})
    );
    ("next_vlan",
     Default ({id=(Bigint.one, 1); data=[]})
    );
    ("acl",
     Default ({id=(Bigint.of_int 4, 3); data=[]})
    );
    ("xconnect",
     Default ({id=(Bigint.of_int 2, 2); data=[]})
    );
    ("hashed",
     Default ({id=(Bigint.of_int 2, 2); data=[]})
    );
    ("multicast",
     Default ({id=(Bigint.of_int 1, 1); data=[]})
    );
    ("egress_vlan",
     Default ({id=(Bigint.of_int 2, 2); data=[]})
    );
    ("classifier",
     Default ({id=(Bigint.of_int 0, 1); data=[
         (Bigint.zero, 4); (*DEFAULT_SLICE_ID*)
         (Bigint.zero, 2); (*DEFAULT_TC*)
       ]})
    );
    ("queues",
     Default ({id=(Bigint.zero, 1); data=[(Bigint.zero, 5)]})
    );
    ("rewriter",
     Default ({id=(Bigint.of_int 2, 2); data=[]})
    );
  ]

let valid_fabric_tables map =
  let cvs, schemata, cpf = fabric () in
  let control_plane = Table.zip schemata map in
  Log.debug_s "Checking state";
  Monitor.check_state cvs control_plane cpf
  |> Alcotest.(check bool) "table state is valid" true

let test_case_test () =
  valid_fabric_tables empty_control_plane

let test_routing_v4_treatment_empty () =
  (* https://github.com/opennetworkinglab/onos/blob/master/pipelines/fabric/impl/src/test/java/org/onosproject/pipelines/fabric/impl/behaviour/FabricInterpreterTest.java#L78 *)
  (* Routing V4: * -> NOP *)
  empty_control_plane
  |> valid_fabric_tables

let tests =
  [
    Alcotest.test_case "[Fabric] CPI passes trivial test case" `Quick test_case_test;
    Alcotest.test_case "[ONOS Test] testRoutingV4TreatmentEmpty" `Quick test_routing_v4_treatment_empty;
  ]
