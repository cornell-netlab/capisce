val simplify : Var.t list -> string -> string
val assert_apply : Var.t list -> string -> string 
val assert_apply_light : Var.t list -> string -> string
val check_sat : ?timeout:int option -> Var.t list -> string -> string
val check_equiv : Var.t list -> string -> Var.t list -> string -> string

val success : string -> bool
val is_sat : string -> bool
val is_unsat : string -> bool
val is_unknown : string -> bool 
val qf : string -> bool
                          
