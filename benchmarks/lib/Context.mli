
type t

val empty : t
val set : Var.t -> int -> t -> t
val label : t -> Var.t -> Var.t
val increment : t -> Var.t -> t                            

val merge : t -> t -> init:'a -> update:(Var.t -> int -> int -> 'a -> 'a)
            -> t * 'a * 'a                                
