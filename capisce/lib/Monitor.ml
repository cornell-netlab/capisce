
let check_state (cvs : Var.t list) (tables : Table.t list) (info : Info.t) (phi : BExpr.t) : bool =
  Solver.check_valid_tables cvs tables info phi
