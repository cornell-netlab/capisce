(** Quantifier elimination-driven specification inference *)

(** [cegqe gcl] computes the control plane interface specification
    for a GCL program using counterexamples.
*)
val cegqe : ASTs.GCL.t -> BExpr.t


(** [num_cexs] captures the number of counterexamples used by [cegqe]*)
val num_cexs : Bigint.t ref


(** [data] captures a trace through [cegqe]. 
    After running [ceqge], [data] captures each path condition 
    inferred by [cegqe] as well as the timestamp at which it 
    was inferred 
*)
val data : (float * BExpr.t) list ref

(** [replay data gcl] replays the trace [data] computing the number of additional 
    paths through [gcl] that are made safe by assuming each successive path condition
*)
val replay : (float * BExpr.t) list -> ASTs.GCL.t -> (float * int) list

