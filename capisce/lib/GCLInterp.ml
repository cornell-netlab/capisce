open Core
open ASTs.GCL

let interp (gcl : t) = 
  match gcl with 
  | Prim active ->
    begin match active.data with 
      | Assign (x,e) -> 
        failwithf "[TODO] Interpret %s := %s"
          (Var.str x)
          (Expr.to_smtlib e) ()
      | Passive (Assert phi) ->
        failwithf "[TODO] interpret assert %s"
          (BExpr.to_smtlib phi) ()
      | Passive (Assume phi) -> 
        failwithf "[TODO] interpret assume %s"
          (BExpr.to_smtlib phi) ()
  end
  | Seq cs -> 
    failwithf "[TODO] interpret sequence of length %d"
      (List.length cs) ()
  | Choice cxs ->  
    failwithf "[TODO] interpret nondeterministic choice of length %d" 
      (List.length cxs) ()