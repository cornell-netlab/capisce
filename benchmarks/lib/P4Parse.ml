open Petr4
open Poulet4
open Unix.Driver
open Core

(* End Construct Parser *)


let as_p4cub_from_file includes p4file verbose =
  let cfg = Pass.{cfg_infile=p4file; cfg_includes=includes; cfg_verbose= verbose} in
  match run_parser cfg with
  | Error _ -> failwith "parsing failed"
  | Ok (typed : Surface.program) ->
    let typed, renamer = Elaborate.elab typed in
    let _, prog = Checker.check_program renamer typed in
    Log.compiler "%s" @@ lazy "got p4light";
    let p4cub = ToP4cub.translate_program (P4info.dummy) prog in
    Log.compiler "%s" @@ lazy "Got p4cub";
    p4cub


let as_cmd_from_file (includes : string list) p4file gas unroll verbose hv =
  let p4cub = as_p4cub_from_file includes p4file verbose in
  match p4cub with
  | Error s ->
    failwith (Printf.sprintf "Compilation Error in stage [P4light->P4cub]: %s" s)
  | Ok p4cub ->
    let coq_gcl = V1model.gcl_from_p4cub TableInstr.instr hv gas unroll p4cub in
    Log.compiler "%s" @@ lazy "Got coq_gcl";
    match coq_gcl with
    | Error s ->
      failwith (Printf.sprintf "Compilation Error in stage [P4cub->GCL]: %s" s)
    | Ok prog ->
      (* Translate.gcl_to_cmd prog *)
      (* |> ASTs.GCL.normalize_names *)
      Tuple2.map ~f:Translate.gcl_to_cmd prog
      |> Util.uncurry ASTs.GCL.seq
      |> ASTs.GCL.normalize_names

let tbl_abstraction_from_file (includes : string list) p4file gas unroll verbose hv =
  let p4cub = as_p4cub_from_file includes p4file verbose in
  match p4cub with
  | Error s ->
    failwithf "Compilation Error in stage [P4light -> P4cub]: %s" s ()
  | Ok p4cub ->
    let instr tbl_name keys actions =
      let keys = List.map keys ~f:(fun ((_, k), mk) -> (k, mk)) in
      GCL.GCL.GTable (tbl_name, keys, actions)
      |> Poulet4.Result.ok
    in
    let coq_gcl = V1model.gcl_from_p4cub instr hv gas unroll p4cub in
    Log.compiler "%s" @@ lazy "[TFG] got coq_gcl";
    match coq_gcl with
    | Error s ->
      failwithf "Compilation Error in stage [P4cub->GCL]: %s" s ()
    | Ok gcl ->
      gcl
