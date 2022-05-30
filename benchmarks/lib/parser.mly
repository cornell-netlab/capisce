%token <string> ID
%token LPAREN
%token RPAREN
%token ASSERT
%token GOALS
%token GOAL
%token PRECISION
%token DEPTH
%token LET
%token FORALL
%token EXISTS
%token BITLIT
%token HEXLIT
%token TRUE
%token FALSE
%token NOT
%token IMP
%token OR
%token AND
%token EQ
%token UNDERSCORE
%token BITVEC
%token BVAND
%token BVOR
%token BVADD
%token BVMUL
%token BVSUB
%token BVXOR
%token BVCONCAT
%token SHL
%token LSHR
%token ASHR
%token ULT
%token ULE
%token UGT
%token UGE
%token SLT
%token SLE
%token SGT
%token SGE
%token EOF

%start <BExpr.t list> program

%%

rev_exprs :
  | e = expr; { [e] }
  | es = exprs; e = expr { e::es }

exprs :
  | es = rev_exprs { List.rev es }                      

expr_bop :
  | BVAND    { Expr.band }
  | BVOR     { Expr.bor }
  | BVADD    { Expr.badd }
  | BVMUL    { Expr.bmul }
  | BVSUB    { Expr.bsub }
  | BVXOR    { Expr.bxor }
  | BVCONCAT { Expr.bconcat }
     
expr :
  | x = ID;
    { Expr.var (Var.make x (-1)) }
  | BITLIT; n = ID; 
    { Expr.bv (Bigint.of_string ("0b" ^ n)) (String.length n) }
  | HEXLIT; n = ID; 
    { Expr.bv (Bigint.of_string ("0x" ^ n)) ((String.length n) * 4) }
  | LPAREN; bop=expr_bop; es=exprs; RPAREN;
    { Expr.nary bop es }
  | LPAREN; SHL; e1 = expr; e2 = expr; RPAREN;
    { Expr.shl_ e1 e2  }
  | RPAREN; LSHR; e1 = expr; e2 = expr; RPAREN;
    { Expr.lshr_ e1 e2 }
  | RPAREN; ASHR; e1 = expr; e2 = expr; RPAREN;
    { Expr.ashr_ e1 e2 }

bindings :
  | (*empty*)
    { Expr.var, BExpr.lvar  }
  | LPAREN; x = ID; e = expr; RPAREN; bindings = bindings;
    { (fun y -> if Core.String.(x = Var.str y) then e else (fst bindings) y ), (snd bindings) }
  | LPAREN; x = ID; b = bexpr; RPAREN; bindings = bindings;
    { (fst bindings), (fun y -> if Core.String.(x = y) then b else (snd bindings) y) }

sort :
  | LPAREN; UNDERSCORE; BITVEC; n = ID;
    { Bigint.of_string n }

qvars :
  | (*empty*) { TypeContext.empty }
  | LPAREN; x = ID; w = sort; RPAREN; xs = qvars
    { TypeContext.set (Var.make x (Bigint.to_int_exn w)) xs }

bexpr_list :
  | b = bexpr;  { [b] }
  | b = bexpr; bs = bexpr_list; { b::bs }
    
bexpr :
  | TRUE; { BExpr.true_ }
  | FALSE; { BExpr.false_ }
  | x = ID { BExpr.lvar x } 
  | LPAREN; FORALL; LPAREN; xs = qvars; RPAREN; b = bexpr; RPAREN;
    { BExpr.(forall (TypeContext.to_list xs) (coerce_types xs b)) }
  | LPAREN; EXISTS; LPAREN; xs = qvars; RPAREN; b = bexpr; RPAREN;
    { BExpr.(exists (TypeContext.to_list xs) (coerce_types xs b)) }
  | LPAREN; LET; LPAREN; bindings = bindings; RPAREN; b = bexpr; RPAREN;
    { BExpr.fun_subst (fst bindings) b |> BExpr.fun_subst_lvar (snd bindings) }
  | LPAREN; NOT; b = bexpr; RPAREN;
    { BExpr.not_ b }
  | LPAREN; AND; bs = bexpr_list; RPAREN;
    { BExpr.ands_ bs }
  | LPAREN; OR; bs = list(bexpr); RPAREN;
    { BExpr.ors_ bs }
  | LPAREN; IMP; bs = bexpr_list; RPAREN;
    { BExpr.imps_ bs }
  | LPAREN; EQ; bs = bexpr_list; RPAREN;
    { BExpr.iffs_ bs }
  | LPAREN; EQ; e1 = expr; e2 = expr; RPAREN;
    { BExpr.eq_ e1 e2 }
  | LPAREN; ULT; e1 = expr; e2 = expr; RPAREN;
    { BExpr.ult_ e1 e2 }
  | LPAREN; ULE; e1 = expr; e2 = expr; RPAREN;
    { BExpr.ule_ e1 e2 }
  | LPAREN; UGT; e1 = expr; e2 = expr; RPAREN;
    { BExpr.ugt_ e1 e2 }
  | LPAREN; UGE; e1 = expr; e2 = expr; RPAREN;
    { BExpr.uge_ e1 e2 }
  | LPAREN; SLT; e1 = expr; e2 = expr; RPAREN;
    { BExpr.slt_ e1 e2 }
  | LPAREN; SLE; e1 = expr; e2 = expr; RPAREN;
    { BExpr.sle_ e1 e2 }
  | LPAREN; SGT; e1 = expr; e2 = expr; RPAREN;
    { BExpr.sgt_ e1 e2 }
  | LPAREN; SGE; e1 = expr; e2 = expr; RPAREN;
    { BExpr.sge_ e1 e2 }

term :
  | LPAREN; GOALS; LPAREN; GOAL; b = bexpr; PRECISION; p=ID; DEPTH; d=ID; RPAREN; RPAREN;
    { Printf.printf ":precision %s :depth %s\n%!" p d;  b }
  | b = bexpr;
    { b }
  | LPAREN; ASSERT; b = bexpr; RPAREN;
    { b }

program :
  | EOF { [] }
  | c = term; cs = program;
    { c::cs  }

