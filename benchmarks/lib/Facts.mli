type t

val empty : t
val to_string : t -> string
val remove : t -> Var.t -> t
val update : t -> Var.t -> Expr.t -> t
val lookup : t -> Var.t -> Expr.t
val merge : t -> t -> t                             
