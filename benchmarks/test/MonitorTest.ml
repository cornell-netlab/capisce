open Core
open Pbench

let () = Pbench.Log.override ()

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
  Pbench.Solver.of_smtlib ~dvs:[] ~cvs:[] cpf_string

let fabric_cpf = parse_smtlib "./examples/bf4_failing/fabric_no_consts.p4" "fabric_output.log"

let valid_fabric_tables map =
  Monitor.check_state map fabric_cpf
  |> Option.is_none
  |> Alcotest.(check bool) "table state is valid" true

let test_case_test () =
  String.Map.empty
  |> valid_fabric_tables

let tests =
  [
    Alcotest.test_case "[Fabric] CPI passes trivial test case" `Quick test_case_test;
  ]
