val simplify : Var.t list -> string -> string
val tseitin : Var.t list -> string -> string
val assert_apply : ?timeout:int -> Var.t list -> string -> string
val assert_apply_light : Var.t list -> string -> string
val check_sat : ?timeout:int option -> Var.t list -> string -> string
val check_sat_model : ?timeout:int option -> Var.t list -> string -> string
val check_equiv : Var.t list -> string -> Var.t list -> string -> string
val check_sat_funs : ?timeout:int option -> Var.t list -> string -> string -> string

val success : string -> bool
val is_sat : string -> bool
val is_unsat : string -> bool
val is_unknown : string -> bool 
val qf : string -> bool

val extract_model : Var.t list -> string -> Model.t option
