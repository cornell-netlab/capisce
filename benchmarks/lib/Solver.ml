open Core
   
let princess_exe = "/home/ericthewry/Downloads/princess-bin-2021-05-10/princess -inputFormat=smtlib +mostGeneralConstraint +incremental "
let z3_exe = "/usr/bin/z3 -smt2 -t:30000"
let cvc4_exe = "/usr/bin/cvc4 --lang smt2"           


let print_position outx lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
             
let parse_with_error lexbuf =
  try Parser.program Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
     fprintf stderr "%a: %s\n" print_position lexbuf msg;
     exit (-1)
  | Parser.Error ->
     fprintf stderr "%a: syntax error\n" print_position lexbuf;
     exit (-1)

let parse filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_with_error lexbuf

             
let tmp () =
  Printf.sprintf "/tmp/tmp_%d.smt2" (Random.int 1000)

let write data ~to_ =
  Out_channel.write_all to_ ~data

let tmp_write str =
  let file = tmp () in
  write str ~to_:file;
  file
  
let run_proc p str =
  Log.print @@ lazy (Printf.sprintf "SMT Query:\n%s\n%!" str);
  let file = tmp_write str in
  let chan = Unix.open_process_in (Printf.sprintf "%s %s 2> /tmp/errors.log" p file) in
  (* let chan = Unix.open_process_in (Printf.sprintf "%s %s" p file) in   *)
  let strs = In_channel.input_lines chan in
  In_channel.close chan;
  String.concat strs ~sep:"\n"
  
let run_princess = run_proc princess_exe
let run_z3 = run_proc z3_exe
let run_cvc4 = run_proc cvc4_exe               


let extract_z3_goals smtstring =
  let open SmtAst in
  let file = tmp_write smtstring in
  let ast = parse file () in
  match ast with
  | [App (Id "goals" :: (App (Id "goal" :: goal :: _)) :: _)] ->
     to_string goal
  | t ->
     Printf.eprintf "WARNING:: expected z3 goals, but got the following:\n%s\n%!" (to_sexp_string ast);
     list_to_string t
                 
