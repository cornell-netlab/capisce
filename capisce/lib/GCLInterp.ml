open Core
open ASTs.GCL

type memory = Model.t

let interp (gcl : t) (_ : memory) = 
  match gcl with 
  | Prim active ->
    begin match active.data with 
      | Assign (x,e) -> 
        failwithf "[TODO] Interpret %s := %s (hint use Expr.eval)"
          (Var.str x)
          (Expr.to_smtlib e) ()
      | Passive (Assert phi) ->
        failwithf "[TODO] interpret assert %s (hint use BExpr.eval)"
          (BExpr.to_smtlib phi) ()
      | Passive (Assume phi) -> 
        failwithf "[TODO] interpret assume %s (hint use BExpr.eval)"
          (BExpr.to_smtlib phi) ()
  end
  | Seq cs -> 
    failwithf "[TODO] interpret sequence of length %d"
      (List.length cs) ()
  | Choice cxs ->  
    failwithf "[TODO] interpret nondeterministic choice of length %d" 
      (List.length cxs) ()