%token <string> ID
%token LPAREN
%token RPAREN
%token LET
%token FORALL
%token EXISTS
%token DECLIT
%token BITLIT
%token HEXLIT
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
    { SmtAst.BV (Bigint.of_string ("0x" ^ n), (String.length n) * 4) }
  
term_list : ts = rev_term_list { List.rev ts }

rev_term_list :
  | (*empty*) { [] }
  | ts = rev_term_list; t = term
    { t :: ts }

program :
  | EOF { [] }
  | c = term; cs = program
    { c::cs  }

