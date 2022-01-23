open Core

let princess_exe = "/home/ericthewry/Downloads/princess-bin-2021-05-10/princess -inputFormat=smtlib +mostGeneralConstraint +incremental "
(* let z3_exe = "/usr/bin/z3 -smt2 -t:30000" *)

let z3_exe = "/usr/bin/z3 -smt2"
           
let cvc4_exe = "/usr/bin/cvc5 --lang smt2" 
  
let run_proc p str =
  Log.print @@ lazy (Printf.sprintf "SMT Query:\n%s\n%!" str);
  let file = FileIO.tmp_write str in
  (* let chan = Unix.open_process_in (Printf.sprintf "%s %s 2> /tmp/errors.log" p file) in *)
  let chan = Unix.open_process_in (Printf.sprintf "%s %s" p file) in
    (* let chan = Unix.open_process_in (Printf.sprintf "%s %s" p file) in   *)
  let strs = In_channel.input_lines chan in
  In_channel.close chan;
  String.concat strs ~sep:"\n"
  
let run_princess = run_proc princess_exe
let run_z3 = run_proc z3_exe
let run_cvc4 = run_proc cvc4_exe               


