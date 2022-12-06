type t
val to_string : t -> string
val empty : t
val update : t -> Var.t -> (Bigint.t * int) -> t
val lookup : t -> Var.t -> (Bigint.t * int) option
val project_inputs : t -> t