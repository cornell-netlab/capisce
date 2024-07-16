module P4Info = Info
open Core
module Info = P4Info

let z3_path = ref "../solvers/z3.4.8.13"
let princess_path = ref "../solvers/princess"

let princess_exe () = Printf.sprintf "%s -inputFormat=smtlib +mostGeneralConstraint +incremental +stdin " (!princess_path)

let z3_exe () = Printf.sprintf "%s -smt2 -in" (!z3_path)


let close_process_in in_chan =
  try
    Core_unix.close_process_in in_chan |> ignore;
    In_channel.close in_chan
  with _ ->
    Log.warn "%s" @@ lazy "process already closed\n%!"

let run_proc_file p str =
  let str = Printf.sprintf "%s\n(exit)\n%!" str in
  Log.smt "starting process:%s" (lazy p);
  Log.smt "SENDING SMT QUERY:\n\"%s\"\n%!" (lazy str);
  (* let file = FileIO.tmp_write str in *)
  let in_chan, out_chan = Core_unix.open_process (Printf.sprintf "%s" p) in
  Out_channel.fprintf out_chan "%s\n%!" str; Out_channel.flush out_chan;
  let strs = In_channel.input_lines in_chan in
  Log.smt "Got a result:\n%s" @@ lazy (String.concat strs ~sep:"\n");
  Core_unix.close_process (in_chan, out_chan) |> ignore;
  Log.smt "%s" @@ lazy "Closed processes";
  String.concat strs ~sep:"\n"

(* let run_proc (in_chan,out_chan) str = *)
(*   let s = Printf.sprintf "(push)\n%s\n(pop 1)\n%!" str in *)
(*   Log.smt "%s" @@ lazy s; *)
(*   fprintf out_chan "%s\n%!" s; *)
(*   Out_channel.flush out_chan; *)
(*   Log.smt "%s" @@ lazy "sent"; *)
(*   let lines = In_channel.input_lines in_chan in *)
(*   Log.smt "%s" @@ lazy "got"; *)
(*   String.concat lines ~sep:"\n" *)

  
let run_princess str = run_proc_file (princess_exe ()) str
let run_z3 str =
  (* let table = String.Table.create () in *)
  (* fun str ->
  match String.Table.find table str with
  | Some res ->
     res
  | None -> *)
     let res = run_proc_file (z3_exe ()) str in
     (* String.Table.set table ~key:str ~data:res; *)
     res

let of_smtlib ~cvs ~dvs smt : BExpr.t =
  (* Log.print @@ lazy (Printf.sprintf "parsing string with vars:\n control %s,\n data %s\n%!"
   *                (List.to_string cvs ~f:Var.str) (List.to_string cvs ~f:Var.str)); *)
  Log.smt "parsing:\n%s\n" (lazy smt);
  let ast = SmtParser.parse_string smt in
  Log.smt "%s" (lazy "translating");
  try
    let b = SmtAst.translate ast ~cvs ~dvs in
    Log.smt "%s" (lazy "type anotations (is this even necessary anymore?)");
    let b = BExpr.coerce_types (TypeContext.of_list cvs) b in
    Log.smt "%s" (lazy "done_parsing");
    b
  with except ->
    Printf.eprintf "Failed to parse:\n%s\n%!" smt;
    raise except

let equisat_cnf phi =
  let dvs, cvs = BExpr.vars phi in
  Smt.tseitin (dvs @ cvs) (BExpr.to_smtlib phi)
  |> run_z3
  |> of_smtlib ~cvs ~dvs

let z3_simplify dvs cvs phi =
  Smt.simplify dvs (BExpr.to_smtlib phi)
  |> run_z3 
  |> of_smtlib ~cvs ~dvs
  
let check_sat ?(timeout=None) consts phi =
  BExpr.to_smtlib phi
  |> Smt.check_sat ~timeout consts
  |> run_z3
  |> Smt.is_sat

let check_unsat ?(timeout=None) consts phi =
  BExpr.to_smtlib phi
  |> Smt.check_sat ~timeout consts
  |> run_z3 
  |> Smt.is_unsat

let check_unsat_cex ?(timeout=None) consts phi =
  BExpr.to_smtlib phi
  |> Smt.check_sat_model ~timeout consts
  |> run_z3
  |> Smt.extract_model consts

let check_valid_tables ?(timeout=None) consts tables info phi =
  let funs = let open List.Let_syntax in
    let%map table = tables in
    Table.to_smtlib table info
    |> Option.value_exn ~message:"Failed to extract smt encoding of table"
  in
  let smtlib_str =
    BExpr.not_ phi
    |> BExpr.to_smtlib
    |> Smt.check_sat_funs ~timeout consts @@ String.concat ~sep:"\n" funs
  in
  Log.smt "check_valid_tables:\n%s" @@ lazy smtlib_str;
  run_z3 smtlib_str
  |> Smt.is_unsat

let check_sat_model ?(timeout=None) consts phi =
  BExpr.to_smtlib phi
  |> Smt.check_sat_model ~timeout consts
  |> run_z3
  |> Smt.extract_model consts

  
let check_iff (b1 : BExpr.t) (b2 : BExpr.t) : bool =
  let smtlib_exp = BExpr.equivalence b1 b2
                   |> BExpr.to_smtlib
                   |> Smt.check_sat ~timeout:(Some 1000) [] in
  let res = run_z3 smtlib_exp in
  Smt.is_unsat res

let check_iff_str ?(timeout=None)  (b1 : BExpr.t) (b2 : BExpr.t) : string =
  let smtlib_exp = BExpr.equivalence b1 b2
                   |> BExpr.to_smtlib
                   |> Smt.check_sat ~timeout [] in
  run_z3 smtlib_exp
