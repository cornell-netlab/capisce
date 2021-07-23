val simplify : Var.t list -> BExpr.t -> string
val simplify_str : Var.t list -> string -> string   
val assert_apply : Var.t list -> BExpr.t -> string
val check_sat : ?timeout:int option -> Var.t list -> BExpr.t -> string                                      
