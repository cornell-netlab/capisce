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
%token BVNOT
%token BVNEG
%token BVAND
%token BVOR
%token BVADD
%token BVMUL
%token BVSUB
%token BVXOR
%token BVCONCAT
%token BVEXTRACT 
%token ZEROEXTEND
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

%start <SmtAst.t> program

%%

expr_nary_op :
  | BVAND    { fun ts -> SmtAst.BVAnd ts }
  | BVOR     { fun ts -> SmtAst.BVOr ts }
  | BVADD    { fun ts -> SmtAst.BVAdd ts }
  | BVMUL    { fun ts -> SmtAst.BVMul ts }
  | BVSUB    { fun ts -> SmtAst.BVSub ts }
  | BVXOR    { fun ts -> SmtAst.BVXor ts }
  | BVCONCAT { fun ts -> SmtAst.BVConcat ts }

extract :
  | LPAREN; UNDERSCORE; BVEXTRACT; hi=ID; lo=ID; RPAREN;
    { Bigint.(of_string lo |> to_int_exn, of_string hi |> to_int_exn) }

bitvec :
  | BITLIT; n = ID; 
    { SmtAst.BV (Bigint.of_string ("0b" ^ n), String.length n) }
  | HEXLIT; n = ID; 
    { SmtAst.BV (Bigint.of_string ("0x" ^ n), (String.length n) * 4) }
  | LPAREN; UNDERSCORE; bv=ID; w=ID; RPAREN;
    { SmtAst.BV (Core.String.chop_prefix_exn bv ~prefix:"bv" |> Bigint.of_string, Bigint.(of_string w |> to_int_exn)) }


bindings :
  | (*empty*)
    { [] }
  | LPAREN; x = ID; t = term; RPAREN; bindings = bindings;
    { (x, t) :: bindings }
  
sort :
  | LPAREN; UNDERSCORE; BITVEC; n = ID; RPAREN;
    { Bigint.of_string n }

qvars :
  | (*empty*) { TypeContext.empty }
  | LPAREN; x = ID; w = sort; RPAREN; xs = qvars
    { TypeContext.set (Var.make x (Bigint.to_int_exn w)) xs }

term_list :
  | t = term;  { [t] }
  | t = term; ts = term_list; { t::ts }
    
term :
  | TRUE;
    { SmtAst.True }
  | FALSE;
    { SmtAst.False }
  | x = ID
    { SmtAst.(Id (x, Unknown)) } 
  | bv = bitvec;
    { bv }
  | LPAREN; LPAREN; UNDERSCORE; ZEROEXTEND; w=ID; RPAREN; t = term; RPAREN;
    { SmtAst.( BVConcat [ BV(Bigint.zero, Bigint.(of_string w |> to_int_exn )); t] ) }
  | LPAREN; FORALL; LPAREN; xs = qvars; RPAREN; t = term; RPAREN;
    { SmtAst.(Forall (TypeContext.to_list xs, t)) }
  | LPAREN; EXISTS; LPAREN; xs = qvars; RPAREN; t = term; RPAREN;
    { SmtAst.(Exists (TypeContext.to_list xs, t)) }
  | LPAREN; LET; LPAREN; bindings = bindings; RPAREN; t = term; RPAREN;
    { SmtAst.Let (bindings, t)  }
  | LPAREN; BVNOT; t = term; RPAREN;
    { SmtAst.BVNot t }
  | LPAREN; BVNEG; t = term; RPAREN;
    { SmtAst.BVNeg t }
  | LPAREN; op=expr_nary_op; ts = term_list; RPAREN;
    { op ts }
  | LPAREN; SHL; t1 = term; t2 = term; RPAREN;
    { SmtAst.Shl(t1, t2)  }
  | LPAREN; LSHR; t1 = term; t2 = term; RPAREN;
    { SmtAst.Lshr (t1, t2) }
  | LPAREN; ASHR; t1 = term; t2 = term; RPAREN;
    { SmtAst.Ashr (t1, t2) }
  | LPAREN; idxs=extract; t = term; RPAREN;
    { SmtAst.BVExtract (fst idxs, snd idxs, t) }
  | LPAREN; NOT; t = term; RPAREN;
    { SmtAst.Not t }
  | LPAREN; AND; ts = term_list; RPAREN;
    { SmtAst.And ts }
  | LPAREN; OR; ts = term_list; RPAREN;
    { SmtAst.Or ts }
  | LPAREN; IMP; ts = term_list; RPAREN;
    { SmtAst.Imp ts }
  | LPAREN; EQ; t1 = term; t2 = term; RPAREN;
    { SmtAst.Eq (t1, t2) }
  | LPAREN; ULT; t1 = term; t2 = term; RPAREN;
    { SmtAst.Ult (t1, t2) }
  | LPAREN; ULE; t1 = term; t2 = term; RPAREN;
    { SmtAst.Ule (t1, t2) }
  | LPAREN; UGT; t1 = term; t2 = term; RPAREN;
    { SmtAst.Ugt (t1, t2) }
  | LPAREN; UGE; t1 = term; t2 = term; RPAREN;
    { SmtAst.Uge (t1, t2) }
  | LPAREN; SLT; t1 = term; t2 = term; RPAREN;
    { SmtAst.Slt (t1, t2) }
  | LPAREN; SLE; t1 = term; t2 = term; RPAREN;
    { SmtAst.Sle (t1, t2) }
  | LPAREN; SGT; t1 = term; t2 = term; RPAREN;
    { SmtAst.Sgt (t1, t2) }
  | LPAREN; SGE; t1 = term; t2 = term; RPAREN;
    { SmtAst.Sge (t1, t2) }

decl :
  | LPAREN; GOALS; LPAREN; GOAL; ts = term_list; PRECISION; ID; DEPTH; ID; RPAREN; RPAREN;
    { SmtAst.And ts }
  | t = term;
    { t }
  | LPAREN; GOALS; LPAREN; GOAL; PRECISION; ID; DEPTH; ID; RPAREN; RPAREN
    {SmtAst.(True) }
  | LPAREN; ASSERT; t = term; RPAREN;
    { t }

program :
  | ds = list(decl); EOF
    { SmtAst.And ds }

