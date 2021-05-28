type t =
  | Assume of Test.t
  | Assert of Test.t
  | Assign of Var.t * Expr.t
  | Seq of t * t
  | Choice of t * t
                    
