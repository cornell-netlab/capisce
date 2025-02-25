type t
val to_string : t -> string
val empty : t
val update : t -> Var.t -> (Bigint.t * int) -> t
val lookup : t -> Var.t -> (Bigint.t * int) option
val disjoint_union : t -> t -> t
val project_inputs : t -> t
val of_alist_exn : (Var.t * (Bigint.t * int)) list -> t
val of_map : (Bigint.t * int) Var.Map.t -> t
