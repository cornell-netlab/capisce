
let check_state (cvs : Var.t list) (tables : Table.t list) (phi : BExpr.t) : bool =
  Solver.check_valid_tables cvs tables phi
