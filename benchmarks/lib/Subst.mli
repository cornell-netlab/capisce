type t


val init : Var.t list -> t   
val to_vsub_list : t -> (Var.t * Var.t) list
val symm_diff : t -> t -> t
val max : t -> t -> t  
val incr : t option -> Var.t -> (Var.t * t) option
val sync : t -> t -> (Var.t * Var.t) list
