%token <int> INT
%token <string> ID
%token LPAREN
%token RPAREN
%token EOF

%start <SmtAst.t list> program

%%

term :
  | s = ID
    { SmtAst.Id s }
  | LPAREN; terms = term_list; RPAREN
    { SmtAst.App terms }

term_list : ts = rev_term_list { List.rev ts }

rev_term_list :
  | (*empty*) { [] }
  | ts = rev_term_list; t = term
    { t :: ts }

program :
  | EOF { [] }
  | c = term; cs = program
    { c::cs  }
