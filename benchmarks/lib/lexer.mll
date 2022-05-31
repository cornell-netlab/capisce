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
  | "assert" { ASSERT }
  | "goals" { GOALS }
  | "goal"  { GOAL }
  | ":precision" { PRECISION }
  | ":depth" { DEPTH }
  | "true" { TRUE }
  | "false" { FALSE }
  | "not" { NOT } 
  | "let" { LET }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "=>" { IMP }
  | "or" { OR }
  | "and" { AND }
  | "="  { EQ }
  | "_" { UNDERSCORE }
  | "BitVec" { BITVEC }
  | "#b" { BITLIT }
  | "#x" { HEXLIT }
  | "bvand" { BVAND }
  | "bvor" { BVOR }
  | "bvxor" { BVXOR }
  | "bvadd" { BVADD }
  | "bvmul" { BVMUL }
  | "bvsub" { BVSUB }  
  | "concat" { BVCONCAT }
  | "extract" { BVEXTRACT }
  | "bvshl" { SHL }
  | "bvashr" { ASHR }
  | "bvlshr" { LSHR }
  | "bvult" { ULT }
  | "bvule" { ULE }
  | "bvugt" { UGT }
  | "bvuge" { UGE }
  | "bvslt" { SLT }
  | "bvsle" { SLE }
  | "bvsgt" { SGT }
  | "bvsge" { SGE }
  | ident as x { ID x }
  | eof { EOF }
