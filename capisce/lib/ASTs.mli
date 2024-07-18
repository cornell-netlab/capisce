(** [ASTs] houses the collection of ASTs used in verification condition generation, notably [GPL], [GCL], and [Psv] *)

open Primitives

module GCL : sig
  (**
    GCL represents a simple variant of Dijksta's
    Guarded Command Language. Specifically the
    variant presented in Flanagan & Saxe's 2001
    POPL paper _Avoiding Exponential Explosion:
    Generating Compact Verification Conditions_
  *)

  (** [GCL] is defined as an extension of [Cmd.Make(Primtives.Active)]
     See [Cmd.Make] for a specification of those functions. *)
    type t = 
    Prim of Active.t
  | Seq of t list
  | Choice of t list

  (** [GCL] adds a few additional functions, specified below *)

  (** [assign x e] construct an assignment statement, which sets the
      value of [x] to [e] *)
  val assign : Var.t -> Expr.t -> t

  (** [ite b c1 c2] constructs an if statment, executing [c1] when 
     [b] evaluates to [true] and [c2] otherwise *)
  val ite : BExpr.t -> t -> t -> t

  (** [wp c phi] computes the weakest precondition of [c] with respect
     to [phi] *)
  val wp : t -> BExpr.t -> BExpr.t

  (** [all_pat
  hs c] produces a list [cs : t list] of all
      paths through the program *)
  val all_paths : t -> t list 

  (** [single_assert_nf c] converts [cs] into a list of paths
     each of which has only a single assert. 
     If a sequence has mulitple assertions, for instance 
     [sequence [assert_ phi; c; assert_ psi]],
     preceeding asserts are replaced by assumes, that is
     the following list is produced:
     [[sequence [assume phi; c; assert_ psi]; sequence [assert_ phi]]]
    *)
  val single_assert_nf : t -> t list

  (** [simplify_path p] takes a gcl program p that is in
     single assert normal form, that is, it is a single path
     and has a single, terminal assertion, and performs 
     both dead code elimination and constant propagation.
    *)
  val simplify_path : t -> t 

  (** [normalize_names c] reformats all of the variables in [c] so
    that they are well-defined SMTLIB variable names.*)
  val normalize_names : t -> t

  (** [assert_valids c] instruments [c] with assertions
    that ensure that anytime a variable with the prefix "hdr." 
    is read, its validity bit is set to 1 *)
    val assert_valids : t -> t 

  (** [track_assigns x c] instruments [c] with a ghost variable [g] that 
    is set to 1 whenever [x] is on the LHS of an assignment.
    Additionally, sets [g] to [0] at the start of the instrumented code, 
    and asserts that it must not be [0] at the end. Something like:
    [x := 0; c; assert x != 0] *)
    val track_assigns : Var.t -> t -> t
  
  (**/**)
  val prim : Active.t -> t
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t

  val seq : t -> t -> t
  val sequence : t list -> t
  val sequence_map : 'a list -> f:('a -> t) -> t
  val sequence_opt : t option list -> t option

  val choice : t -> t -> t
  val choices : t list -> t
  val choices_map : 'a list -> f:('a -> t) -> t
  val choices_opt : t option list -> t option

  val choice_seq : t list -> t list -> t
  val choice_seqs : t list list -> t

  val skip : t
  val pass : t
  val dead : t
  val abort : t

  val contra : t -> t -> bool
  val to_string : t -> string
  val size : t -> int
  val vars : t -> Var.t list

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexplib.Sexp.t
  val t_of_sexp : Sexplib.Sexp.t -> t

  val quickcheck_generator : t Base_quickcheck.Generator.t
  val quickcheck_observer : t Base_quickcheck.Observer.t
  val quickcheck_shrinker : t Base_quickcheck.Shrinker.t

  val hash_fold_t : t Base__Ppx_hash_lib.hash_fold
  val hash : t -> Base__Ppx_hash_lib.Std.Hash.hash_value

  val const_prop : t -> t
  val optimize : t -> t
  (**/**)
end

module Psv : sig 
  (**
    Psv represents a restriction on Dijkstra's
    guarded command logic called the passive form.
    This was defined in Flanagan & Saxe's 2001
    POPL paper _Avoiding Exponential Explosion:
    Generating Compact Verification Conditions_
  *)

  (** PSV is a [Cmd] defined using the [Passive] 
     [Primitive], i.e. via
     [include Cmd.Make (Passive)]
  *)
  type t =
  | Prim of Passive.t
  | Seq of t list
  | Choice of t list

  (** [normal c] computes a formula describing the normal executions
     of the passive program [c]. The "normal executions", are the
     ones for which every assertion and every assumption is satisfied.
     A formal definition can be found in Flanagan & Saxe 2001 *)
  val normal : t -> BExpr.t

  (** [wrong c] computes the "wrong" executions of a passive program
     [c]. In a wrong execution, every assumption is satisfied, 
     and some assertion is violated*)
  val wrong : t -> BExpr.t

  (** [passify c] converts a [GCL] program into a [Psv] program.
      The transformation can be found in Flanagan & Saxe 2001 *)
  val passify : GCL.t -> Context.t * t
  
  (** [vc phi] computes the verificaiton condition for
      a passive program. *)
  val vc : t -> BExpr.t

  (**/**)
  val remove_asserts : t -> t

  val prim : Passive.t -> t
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t

  val seq : t -> t -> t
  val sequence : t list -> t
  val sequence_map : 'a list -> f:('a -> t) -> t 
  val sequence_opt : t option list -> t option

  val choice : t -> t -> t
  val choices : t list -> t
  val choices_map : 'a list -> f:('a -> t) -> t
  val choices_opt : t option list -> t option

  val skip : t
  val pass : t
  val dead : t
  val abort : t

  val contra : t -> t -> bool
  val to_string : t -> string
  val equal : t -> t -> bool 
  val compare : t -> t -> int
  val size : t -> int
  val vars : t -> Var.t list
  val sexp_of_t : t -> Sexplib.Sexp.t
  val t_of_sexp : Sexplib.Sexp.t -> t

  val quickcheck_generator : t Base_quickcheck.Generator.t
  val quickcheck_observer : t Base_quickcheck.Observer.t
  val quickcheck_shrinker : t Base_quickcheck.Shrinker.t

  val hash_fold_t : t Base__Ppx_hash_lib.hash_fold
  val hash : t -> Base__Ppx_hash_lib.Std.Hash.hash_value
  (**/*)
end



module GPL : sig
  (**
    GPL, i.e. the Guarded Pipeline Language, is the 
    core IR for computing control plane
    interface specifications for data plane programs.
  *)

  (* A GPL program
     is a [Cmd] that instantiated over the [Pipeline] [Primitive] 
  *)
  type t = 
    Prim of Pipeline.t
  | Seq of t list
  | Choice of t list

  (** Constructing a table using [table name keys actions]
     requires a string identifier [name], a list of annotated [keys],
     and a list of [actions].
    
     A single key, is a [Var.t] annotated with one of three flags.
     [`Exact] indicates that the variable should be understood as
     an [exact] match kind as in p4, meaning that every bit must be
     read. [`Maskable] indicates the other extreme 
     ([ternary], [lpm], [optional], etc), where it is possible
     to skip reading any and every bit. [MaskableDegen] is semantically 
     equivalent to `Exact] and is used to capture the case when the
     key is [Maskable], AND we can detect that safety does not
     require masking. For example, when checking header validity,
     if the key is a metadata field (metadata fields are always valid).
  *)
  val table : string 
  -> (Var.t * Table.kind) list 
  -> (Var.t list * Primitives.Action.t list) list
  -> t

  (** [encode_tables t] transforms tables into an equivalent GCL implementation *)
  val encode_tables : t -> GCL.t

  (** [tables t] computes the list of tables in a GPL program *)
  val tables : t -> Table.t list

  (** [assign x e] constructs an assignment *)
  val assign : Var.t -> Expr.t -> t

  (** [active a] injects an Active primitive [a] into [GPL] *)
  val active : Primitives.Active.t -> t

  (** [of_gcl gcl] injects the [GCL] program [gcl] into [GPL]*)
  val of_gcl : GCL.t -> t

  (** [wp c phi] computes the weakest precondition of [c] w.r.t [phi]*)
  val wp : t -> BExpr.t -> BExpr.t

  (** [symbolize c phi] computes a symbolic representation of [c] via the 
   * passive form *)
  val symbolize : t -> t

  (** [normalize_names c] normalizes the names in c so that they are SMT-friendly *)
  val normalize_names : t -> t

  (** [count_paths c] returns the number of paths through the program [c]*)
  val count_paths : t -> Bigint.t
   
  (**/**)

  val prim : Pipeline.t -> t
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t

  val seq : t -> t -> t
  val sequence : t list -> t
  val sequence_map : 'a list -> f:('a -> t) -> t
  val sequence_opt : t option list -> t option

  val choice : t -> t -> t
  val choices : t list -> t
  val choices_map : 'a list -> f:('a -> t) -> t
  val choices_opt : t option list -> t option

  val choice_seqs : t list list -> t

  val skip : t
  val pass : t
  val dead : t
  val abort : t

  val contra : t -> t -> bool
  val to_string : t -> string
  val size : t -> int
  val vars : t -> Var.t list

  val dead_code_elim : Var.Set.t -> t -> Var.Set.t * t
  val const_prop : Expr.t Var.Map.t -> t -> (t * Expr.t Var.Map.t) option

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexplib.Sexp.t
  val t_of_sexp : Sexplib.Sexp.t -> t

  val quickcheck_generator : t Base_quickcheck.Generator.t
  val quickcheck_observer : t Base_quickcheck.Observer.t
  val quickcheck_shrinker : t Base_quickcheck.Shrinker.t

  val hash_fold_t : t Base__Ppx_hash_lib.hash_fold
  val hash : t -> Base__Ppx_hash_lib.Std.Hash.hash_value
  (**/**)
end



module Concrete : sig 
  (** [Concrete] specifies a [GCL] operation that
      computes slices of programs *)
  
  (** [slice m c] computes the programs slice of [c]
    * that will be executed by [m] *)
  val slice : Model.t -> GCL.t -> GCL.t option

end

val passive_vc : GCL.t -> BExpr.t