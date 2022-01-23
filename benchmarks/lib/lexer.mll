{
open Lexing
open Parser     
exception SyntaxError of string


let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = pos.pos_cnum;
               pos_lnum = pos.pos_lnum + 1
    }
}

let white = [' ' '\t' ]+
let digit = ['0' - '9']
let num = digit+
let newline = '\r' | '\n' | "\r\n"
let ident = [^ '(' ')' '#' ' ' '\t' '\r' '\n']+

rule read =
  parse
  | white { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "let" { LET }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "#b" { BITLIT }
  | "#x" { HEXLIT }
  | ident as x { ID x }
  | eof { EOF }
