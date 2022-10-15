open Core

let princess_exe = "/home/ericthewry/Downloads/princess-bin-2021-05-10/princess -inputFormat=smtlib +mostGeneralConstraint +incremental "
(* let z3_exe = "/usr/bin/z3 -smt2 -t:30000" *)

let z3_exe = "/usr/bin/z3 -smt2"
           
let cvc4_exe = "/usr/bin/cvc5 --lang smt2" 
  
let run_proc p str =
  Log.print @@ lazy (Printf.sprintf "SMT Query:\n%s\n%!" str);
  Printf.printf "SMT Query:\n%s\n%!" str;
  Breakpoint.set true;
  let file = FileIO.tmp_write str in
  (* let chan = Unix.open_process_in (Printf.sprintf "%s %s 2> /tmp/errors.log" p file) in *)
  let chan = Core_unix.open_process_in (Printf.sprintf "%s %s" p file) in
    (* let chan = Unix.open_process_in (Printf.sprintf "%s %s" p file) in   *)
  let strs = In_channel.input_lines chan in
  In_channel.close chan;
  String.concat strs ~sep:"\n"
  
let run_princess = run_proc princess_exe
let run_z3 =
  let table = String.Table.create () in
  fun str ->
  match String.Table.find table str with
  | Some res ->
     res
  | None ->
     let res = run_proc z3_exe str in
     String.Table.set table ~key:str ~data:res;
     res
     
let run_cvc4 = run_proc cvc4_exe               

let of_smtlib ~cvs ~dvs smt : BExpr.t =
  (* Log.print @@ lazy (Printf.sprintf "parsing string with vars:\n control %s,\n data %s\n%!"
   *                (List.to_string cvs ~f:Var.str) (List.to_string cvs ~f:Var.str)); *)
  Log.print @@ lazy (Printf.sprintf "parsing:\n%s\n" smt);
  let ast = SmtParser.parse_string smt in
  Log.print @@ lazy "translating";
  let b = SmtAst.translate ast ~cvs ~dvs in
  Log.print @@ lazy "type anotations (is this even necessary anymore?)";
  let b = BExpr.coerce_types (TypeContext.of_list cvs) b in
  Log.print @@ lazy "done parsing";
  b
  
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
