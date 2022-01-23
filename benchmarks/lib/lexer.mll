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
  (* | "=>" { ARR } *)
  | "forall" { FORALL }
  | "exists" { EXISTS }
  (* | "_" { UNDERSCORE } *)
  | "#b" { BITLIT }
  | "#x" { HEXLIT }
  (* | "=" { EQ } *)
  (* | "bvult" { BVULT }  
   * | "bvule" { BVULE }
   * | "bvuge" { BVUGE }
   * | "bvugt" { BVUGT }
   * | "bvslt" { BVSLT }
   * | "bvsle" { BVSLE }
   * | "bvsgt" { BVSGT }
   * | "bvsge" { BVSGE }  
   * | "bvand" { BVAND }  
   * | "bvor"  { BVOR }  
   * | "bvxor" { BVXOR } 
   * | "bvadd" { BVADD } 
   * | "bvmul" { BVMUL } 
   * | "bvsub" { BVSUB } 
   * | "concat" { CONCAT }
   * | "bvshl" { BVSHL }
   * | "bvashr" { BVASHR }
   * | "bvlshr" { BVLSHR }
   * | "bvnot" { BVNOT }
   * | "and" { AND }
   * | "not" { NOT }
   * | "or" { OR }
   * | "=>" { ARR } *)
  | ident as x { ID x }
  | eof { EOF }
