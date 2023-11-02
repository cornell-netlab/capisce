open Core
                     
let print_position outx lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
             
let parse_with_error lexbuf =
  try Parser.program Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
     fprintf stderr "%a: %s\n" print_position lexbuf msg;
     failwith "Lexer Error"
  | Parser.Error ->
     fprintf stderr "%a: syntax error\n" print_position lexbuf;
     failwith "parser Error"

let parse filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let prog = parse_with_error lexbuf in
  In_channel.close inx;
  prog


let parse_string smtstring =
  Lexing.from_string smtstring 
  |> parse_with_error
