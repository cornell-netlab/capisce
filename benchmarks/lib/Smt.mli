val simplify : Var.t list -> BExpr.t -> string
val simplify_str : Var.t list -> string -> string   
val assert_apply : Var.t list -> BExpr.t -> string 
val assert_apply_str : Var.t list -> string -> string
val check_sat : ?timeout:int option -> Var.t list -> BExpr.t -> string
val check_equiv : Var.t list -> string -> Var.t list -> string -> string
