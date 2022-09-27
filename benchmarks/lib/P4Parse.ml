open Petr4
open Common   
open Poulet4
open Core   

   
(* Begin Construct Parser*)
let colorize colors s = ANSITerminal.sprintf colors "%s" s

module Conf: Parse_config = struct
  let red s = colorize [ANSITerminal.red] s
  let green s = colorize [ANSITerminal.green] s

  let preprocess (include_dirs : string list) p4file =
    let cmd =
      String.concat ~sep:" "
        (["cc"] @
         (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
          ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in
    let in_chan = Core_unix.open_process_in cmd in
    let str = In_channel.input_all in_chan in
    let (_ : (unit, [ `Exit_non_zero of int | `Signal of Signal.t ]) result) =
      Core_unix.close_process_in in_chan
    in
    str
end

module Parse = Make_parse(Conf)

open Parse
(* End Construct Parser *)


let as_p4cub_from_file includes p4file verbose =
  match parse_file includes p4file verbose with
  | `Error _ -> failwith "parsing failed"
  | `Ok (typed : Surface.program) ->
    let typed, renamer = Elaborate.elab typed in
    let _, prog = Checker.check_program renamer typed in
    Log.print @@ lazy "got p4light";
    let p4cub = ToP4cub.translate_program (P4info.dummy) prog in
    Log.print @@ lazy "Got p4cub";
    p4cub


let as_cmd_from_file (includes : string list) p4file gas unroll verbose =
  let p4cub = as_p4cub_from_file includes p4file verbose in
  match p4cub with
  | Error s ->
    failwith (Printf.sprintf "Compilation Error in stage [P4light->P4cub]: %s" s)
  | Ok p4cub ->
    let instr tbl_name _ = TableInstr.instr tbl_name in
    let coq_gcl = V1model.gcl_from_p4cub (P4info.dummy) instr true gas unroll p4cub in
    Log.print @@ lazy "Got coq_gcl";
    match coq_gcl with
    | Error s ->
      failwith (Printf.sprintf "Compilation Error in stage [P4cub->GCL]: %s" s)
    | Ok gcl ->
      Translate.gcl_to_cmd gcl
      |> Cmd.GCL.normalize_names

let tbl_abstraction_from_file (includes : string list) p4file gas unroll verbose =
  let p4cub = as_p4cub_from_file includes p4file verbose in
  match p4cub with
  | Error s ->
    failwithf "Compilation Error in stage [P4light -> P4cub]: %s" s ()
  | Ok p4cub ->
    let instr tbl_name _ _ _ = Poulet4.Result.Result.ok (GCL.GCL.GExternVoid (tbl_name, [])) in
    let coq_gcl = V1model.gcl_from_p4cub (P4info.dummy) instr true gas unroll p4cub in
    Log.print @@ lazy "Got Coq_gcl";
    match coq_gcl with
    | Error s ->
      failwithf "Compilation Error in stage [P4cub->GCL]: %s" s ()
    | Ok gcl ->
      gcl
