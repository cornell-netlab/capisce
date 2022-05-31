type t

val empty : t
val rem : Var.t -> t -> t
val set : Var.t -> t -> t
val get : Var.t -> t -> Var.t option 
val singleton : Var.t -> t
val to_list : t -> Var.t list
val of_list : Var.t list -> t                     
