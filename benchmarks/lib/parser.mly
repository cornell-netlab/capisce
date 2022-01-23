%token <int> INT
%token <string> ID
%token LPAREN
%token RPAREN
%token LET
%token EQ
%token FORALL
%token EXISTS
%token UNDERSCORE
%token BVULE
%token BVULT
%token BVSUB
%token BVUGE
%token BVUGT
%token BVSLT
%token BVSLE
%token BVSGT
%token BVSGE  
%token BVAND  
%token BVOR  
%token BVXOR
%token BVADD
%token BVMUL
%token CONCAT
%token BVSHL
%token BVASHR
%token BVLSHR
%token BVNOT
%token DECLIT
%token BITLIT
%token HEXLIT
%token AND
%token NOT
%token OR
%token ARR
%token EOF

%start <SmtAst.t list> program

%%

term :
  | s = ID
     { SmtAst.Id s }
  | LPAREN; FORALL; LPAREN; terms = term_list; RPAREN; t = term; RPAREN;
     { SmtAst.Forall (terms, t) }
  | LPAREN; EXISTS; LPAREN; terms = term_list; RPAREN; t = term; RPAREN;
     { SmtAst.Exists (terms, t) }
  | LPAREN; LET; LPAREN; terms = term_list; RPAREN; t = term; RPAREN;
     { SmtAst.Let (terms, t) }
  | LPAREN; f = term; terms = term_list; RPAREN;
    { SmtAst.Fun (f, terms) }
  | BITLIT; n = ID; 
    { SmtAst.BV (Bigint.of_string ("0b" ^ n), String.length n) }
  | HEXLIT; n = ID; 
    { SmtAst.BV (Bigint.of_string ("0b" ^ n), String.length n) }
  
term_list : ts = rev_term_list { List.rev ts }

rev_term_list :
  | (*empty*) { [] }
  | ts = rev_term_list; t = term
    { t :: ts }

program :
  | EOF { [] }
  | c = term; cs = program
    { c::cs  }
