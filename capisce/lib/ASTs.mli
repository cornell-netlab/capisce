module GCL :
  sig
    module Pack :
      sig
        type t =
          Cmd.Make(Primitives.Active).t =
            Prim of Primitives.Active.t
          | Seq of t list
          | Choice of t list
        val equal : t -> t -> bool
        val quickcheck_generator : t Base_quickcheck.Generator.t
        val quickcheck_observer : t Base_quickcheck.Observer.t
        val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
        val t_of_sexp : Sexplib0.Sexp.t -> t
        val sexp_of_t : t -> Sexplib0.Sexp.t
        val compare :
          t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
        val hash_fold_t :
          t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
        val hash : t -> int
        val assume : BExpr.t -> t
        val assert_ : BExpr.t -> t
        val skip : t
        val pass : t
        val dead : t
        val abort : t
        val zero : t
        val one : t
        val prim : Primitives.Active.t -> t
        val ( + ) : t -> t -> t
        val ( * ) : t -> t -> t
        val contra : t -> t -> bool
        val to_string : t -> string
        val size : t -> int
        val seq : t -> t -> t
        val sequence : t list -> t
        val sequence_opt : t option list -> t option
        val sequence_map : 'a list -> f:('a -> t) -> t
        val choice : t -> t -> t
        val choices : t list -> t
        val choices_map : 'a list -> f:('a -> t) -> t
        val choices_opt : t option list -> t option
        val choice_seq : t list -> t list -> t
        val choice_seqs : t list list -> t
        val is_primitive : t -> bool
        val vars : t -> Var.t list
        val assign : Var.t -> Expr.t -> t
        val table :
          string * Var.t list * (Var.t list * Primitives.Action.t list) list ->
          t
        val ite : BExpr.t -> t -> t -> t
        val wp : t -> BExpr.t -> BExpr.t
        val all_paths : t -> t list
        val single_assert_nf : t -> t list
        val simplify_path : t -> t
      end
    module CP :
      sig
        val psubst :
          Expr.t Var.Map.t ->
          Primitives.Active.pre_t Primitives.alt ->
          Primitives.Active.pre_t Primitives.alt * Expr.t Var.Map.t
        val merge : Expr.t option -> Expr.t option -> Expr.t option
        module S :
          sig
            val with_map :
              Expr.t Var.Map.t ->
              Pack.t -> (Pack.t * Expr.t Var.Map.t) option
            val one :
              Var.t -> Expr.t -> Pack.t -> (Pack.t * Expr.t Var.Map.t) option
          end
        val propagate_with_map :
          Expr.t Var.Map.t -> Pack.t -> (Pack.t * Expr.t Var.Map.t) option
        val propagate_exn : Pack.t -> Pack.t
      end
    val const_prop :
      Cmd.Make(Primitives.Active).t -> Cmd.Make(Primitives.Active).t
    module O :
      sig
        module CP :
          sig
            val psubst :
              Expr.t Var.Map.t ->
              Primitives.Active.pre_t Primitives.alt ->
              Primitives.Active.pre_t Primitives.alt * Expr.t Var.Map.t
            val merge : Expr.t option -> Expr.t option -> Expr.t option
            module S :
              sig
                val with_map :
                  Expr.t Var.Map.t ->
                  Pack.t -> (Pack.t * Expr.t Var.Map.t) option
                val one :
                  Var.t ->
                  Expr.t -> Pack.t -> (Pack.t * Expr.t Var.Map.t) option
              end
            val propagate_with_map :
              Expr.t Var.Map.t ->
              Pack.t -> (Pack.t * Expr.t Var.Map.t) option
            val propagate_exn : Pack.t -> Pack.t
          end
        module DC :
          sig
            val elim_with_reads : Var.Set.t -> Pack.t -> Var.Set.t * Pack.t
            val elim : Pack.t -> Pack.t
          end
        val optimize : Pack.t -> Pack.t
        val optimize_seq_pair : Pack.t * Pack.t -> Pack.t * Pack.t
      end
    module N : sig val normalize : Pack.t -> Pack.t end
    val optimize :
      Cmd.Make(Primitives.Active).t -> Cmd.Make(Primitives.Active).t
    val normalize_names :
      Cmd.Make(Primitives.Active).t -> Cmd.Make(Primitives.Active).t
    type t =
      Pack.t =
        Prim of Primitives.Active.t
      | Seq of t list
      | Choice of t list
    val equal : t -> t -> bool
    val quickcheck_generator : t Base_quickcheck.Generator.t
    val quickcheck_observer : t Base_quickcheck.Observer.t
    val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
    val hash_fold_t :
      t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
    val hash : t -> int
    val assume : BExpr.t -> t
    val assert_ : BExpr.t -> t
    val skip : t
    val pass : t
    val dead : t
    val abort : t
    val zero : t
    val one : t
    val prim : Primitives.Active.t -> t
    val ( + ) : t -> t -> t
    val ( * ) : t -> t -> t
    val contra : t -> t -> bool
    val to_string : t -> string
    val size : t -> int
    val seq : t -> t -> t
    val sequence : t list -> t
    val sequence_opt : t option list -> t option
    val sequence_map : 'a list -> f:('a -> t) -> t
    val choice : t -> t -> t
    val choices : t list -> t
    val choices_map : 'a list -> f:('a -> t) -> t
    val choices_opt : t option list -> t option
    val choice_seq : t list -> t list -> t
    val choice_seqs : t list list -> t
    val is_primitive : t -> bool
    val vars : t -> Var.t list
    val assign : Var.t -> Expr.t -> t
    val table :
      string * Var.t list * (Var.t list * Primitives.Action.t list) list -> t
    val ite : BExpr.t -> t -> t -> t
    val wp : t -> BExpr.t -> BExpr.t
    val all_paths : t -> t list
    val single_assert_nf : t -> t list
    val simplify_path : t -> t
  end
module Psv :
  sig
    type t =
      Cmd.Make(Primitives.Passive).t =
        Prim of Primitives.Passive.t
      | Seq of t list
      | Choice of t list
    val equal : t -> t -> bool
    val quickcheck_generator : t Base_quickcheck.Generator.t
    val quickcheck_observer : t Base_quickcheck.Observer.t
    val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
    val hash_fold_t :
      t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
    val hash : t -> int
    val assume : BExpr.t -> t
    val assert_ : BExpr.t -> t
    val skip : t
    val pass : t
    val dead : t
    val abort : t
    val zero : t
    val one : t
    val prim : Primitives.Passive.t -> t
    val ( + ) : t -> t -> t
    val ( * ) : t -> t -> t
    val contra : t -> t -> bool
    val to_string : t -> string
    val size : t -> int
    val seq : t -> t -> t
    val sequence : t list -> t
    val sequence_opt : t option list -> t option
    val sequence_map : 'a list -> f:('a -> t) -> t
    val choice : t -> t -> t
    val choices : t list -> t
    val choices_map : 'a list -> f:('a -> t) -> t
    val choices_opt : t option list -> t option
    val choice_seq : t list -> t list -> t
    val choice_seqs : t list list -> t
    val is_primitive : t -> bool
    val vars : t -> Var.t list
    val normal : t -> BExpr.t
    val wrong : t -> BExpr.t
    val update_resid : Var.t -> int -> int -> BExpr.t -> BExpr.t
    val passify : GCL.t -> Context.t * t
    val vc : t -> BExpr.t
    val remove_asserts : t -> t
  end
module GPL :
  sig
    module Pack :
      sig
        type t =
          Cmd.Make(Primitives.Pipeline).t =
            Prim of Primitives.Pipeline.t
          | Seq of t list
          | Choice of t list
        val equal : t -> t -> bool
        val quickcheck_generator : t Base_quickcheck.Generator.t
        val quickcheck_observer : t Base_quickcheck.Observer.t
        val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
        val t_of_sexp : Sexplib0.Sexp.t -> t
        val sexp_of_t : t -> Sexplib0.Sexp.t
        val compare :
          t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
        val hash_fold_t :
          t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
        val hash : t -> int
        val assume : BExpr.t -> t
        val assert_ : BExpr.t -> t
        val skip : t
        val pass : t
        val dead : t
        val abort : t
        val zero : t
        val one : t
        val prim : Primitives.Pipeline.t -> t
        val ( + ) : t -> t -> t
        val ( * ) : t -> t -> t
        val contra : t -> t -> bool
        val to_string : t -> string
        val size : t -> int
        val seq : t -> t -> t
        val sequence : t list -> t
        val sequence_opt : t option list -> t option
        val sequence_map : 'a list -> f:('a -> t) -> t
        val choice : t -> t -> t
        val choices : t list -> t
        val choices_map : 'a list -> f:('a -> t) -> t
        val choices_opt : t option list -> t option
        val choice_seq : t list -> t list -> t
        val choice_seqs : t list list -> t
        val is_primitive : t -> bool
        val vars : t -> Var.t list
        val assign : Var.t -> Expr.t -> t
        val raw_table :
          string ->
          Var.t list -> (Var.t list * Primitives.Action.t list) list -> t
        val table :
          string ->
          [< `Exact of Var.t | `Maskable of Var.t | `MaskableDegen of Var.t ]
          list -> (Var.t list * Primitives.Action.t list) list -> t
        val of_gcl : GCL.t -> t
        val count_paths : t -> Bigint.t
        val encode_tables : t -> GCL.t
        module type CanAssert = sig type t val assert_ : BExpr.t -> t end
        module Asserter :
          functor (Prim : CanAssert) ->
            sig val from_vars : Var.t list -> Prim.t list end
        val assert_valids_action :
          Var.t list * Primitives.Action.t list ->
          Var.t list * Primitives.Action.t list
        val assert_valids : t -> t
        val wp : t -> BExpr.t -> BExpr.t
        val symbolize : t -> t
        val tables : t -> Primitives.Table.t list
      end
    module N : sig val normalize : Pack.t -> Pack.t end
    val normalize_names :
      Cmd.Make(Primitives.Pipeline).t -> Cmd.Make(Primitives.Pipeline).t
    module D :
      sig
        val elim_with_reads : Var.Set.t -> Pack.t -> Var.Set.t * Pack.t
        val elim : Pack.t -> Pack.t
      end
    val dead_code_elim :
      Var.Set.t ->
      Cmd.Make(Primitives.Pipeline).t ->
      Var.Set.t * Cmd.Make(Primitives.Pipeline).t
    module C :
      sig
        val psubst :
          Expr.t Var.Map.t ->
          Primitives.Pipeline.t -> Primitives.Pipeline.t * Expr.t Var.Map.t
        val merge : Expr.t option -> Expr.t option -> Expr.t option
        module S :
          sig
            val with_map :
              Expr.t Var.Map.t ->
              Pack.t -> (Pack.t * Expr.t Var.Map.t) option
            val one :
              Var.t -> Expr.t -> Pack.t -> (Pack.t * Expr.t Var.Map.t) option
          end
        val propagate_with_map :
          Expr.t Var.Map.t -> Pack.t -> (Pack.t * Expr.t Var.Map.t) option
        val propagate_exn : Pack.t -> Pack.t
      end
    val const_prop :
      Expr.t Var.Map.t ->
      Cmd.Make(Primitives.Pipeline).t ->
      (Cmd.Make(Primitives.Pipeline).t * Expr.t Var.Map.t) option
    module O :
      sig
        module CP :
          sig
            val psubst :
              Expr.t Var.Map.t ->
              Primitives.Pipeline.t ->
              Primitives.Pipeline.t * Expr.t Var.Map.t
            val merge : Expr.t option -> Expr.t option -> Expr.t option
            module S :
              sig
                val with_map :
                  Expr.t Var.Map.t ->
                  Pack.t -> (Pack.t * Expr.t Var.Map.t) option
                val one :
                  Var.t ->
                  Expr.t -> Pack.t -> (Pack.t * Expr.t Var.Map.t) option
              end
            val propagate_with_map :
              Expr.t Var.Map.t ->
              Pack.t -> (Pack.t * Expr.t Var.Map.t) option
            val propagate_exn : Pack.t -> Pack.t
          end
        module DC :
          sig
            val elim_with_reads : Var.Set.t -> Pack.t -> Var.Set.t * Pack.t
            val elim : Pack.t -> Pack.t
          end
        val optimize : Pack.t -> Pack.t
        val optimize_seq_pair : Pack.t * Pack.t -> Pack.t * Pack.t
      end
    val optimize :
      Cmd.Make(Primitives.Pipeline).t -> Cmd.Make(Primitives.Pipeline).t
    val optimize_seq_pair :
      Cmd.Make(Primitives.Pipeline).t * Cmd.Make(Primitives.Pipeline).t ->
      Cmd.Make(Primitives.Pipeline).t * Cmd.Make(Primitives.Pipeline).t
    type t =
      Pack.t =
        Prim of Primitives.Pipeline.t
      | Seq of t list
      | Choice of t list
    val equal : t -> t -> bool
    val quickcheck_generator : t Base_quickcheck.Generator.t
    val quickcheck_observer : t Base_quickcheck.Observer.t
    val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
    val hash_fold_t :
      t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
    val hash : t -> int
    val assume : BExpr.t -> t
    val assert_ : BExpr.t -> t
    val skip : t
    val pass : t
    val dead : t
    val abort : t
    val zero : t
    val one : t
    val prim : Primitives.Pipeline.t -> t
    val ( + ) : t -> t -> t
    val ( * ) : t -> t -> t
    val contra : t -> t -> bool
    val to_string : t -> string
    val size : t -> int
    val seq : t -> t -> t
    val sequence : t list -> t
    val sequence_opt : t option list -> t option
    val sequence_map : 'a list -> f:('a -> t) -> t
    val choice : t -> t -> t
    val choices : t list -> t
    val choices_map : 'a list -> f:('a -> t) -> t
    val choices_opt : t option list -> t option
    val choice_seq : t list -> t list -> t
    val choice_seqs : t list list -> t
    val is_primitive : t -> bool
    val vars : t -> Var.t list
    val assign : Var.t -> Expr.t -> t
    val raw_table :
      string ->
      Var.t list -> (Var.t list * Primitives.Action.t list) list -> t
    val table :
      string ->
      [< `Exact of Var.t | `Maskable of Var.t | `MaskableDegen of Var.t ]
      list -> (Var.t list * Primitives.Action.t list) list -> t
    val of_gcl : GCL.t -> t
    val count_paths : t -> Bigint.t
    val encode_tables : t -> GCL.t
    module type CanAssert = Pack.CanAssert
    module Asserter = Pack.Asserter
    val assert_valids_action :
      Var.t list * Primitives.Action.t list ->
      Var.t list * Primitives.Action.t list
    val assert_valids : t -> t
    val wp : t -> BExpr.t -> BExpr.t
    val symbolize : t -> t
    val tables : t -> Primitives.Table.t list
  end
  
module Concrete : sig val slice : Model.t -> GCL.t -> GCL.t option end
val passive_vc : GCL.t -> BExpr.t
