module type Primitive =
  sig
    type t
    val equal : t -> t -> bool
    val quickcheck_generator : t Base_quickcheck.Generator.t
    val quickcheck_observer : t Base_quickcheck.Observer.t
    val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
    val hash_fold_t :
      t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
    val assume : BExpr.t -> t
    val assert_ : BExpr.t -> t
    val contra : t -> t -> bool
    val to_smtlib : t -> string
    val size : t -> int
    val vars : t -> Var.t list
  end
type 'a alt = { data : 'a; alt : 'a option; }
val equal_alt : ('a -> 'a -> bool) -> 'a alt -> 'a alt -> bool
val quickcheck_generator_alt :
  'a Base_quickcheck.Generator.t -> 'a alt Base_quickcheck.Generator.t
val quickcheck_observer_alt :
  'a Base_quickcheck.Observer.t -> 'a alt Base_quickcheck.Observer.t
val quickcheck_shrinker_alt :
  'a Base_quickcheck.Shrinker.t -> 'a alt Base_quickcheck.Shrinker.t
val hash_fold_alt :
  (Base_internalhash_types.state -> 'a -> Base_internalhash_types.state) ->
  Base_internalhash_types.state -> 'a alt -> Base_internalhash_types.state
val alt_of_sexp : (Sexplib0.Sexp.t -> 'a) -> Sexplib0.Sexp.t -> 'a alt
val sexp_of_alt : ('a -> Sexplib0.Sexp.t) -> 'a alt -> Sexplib0.Sexp.t
val compare_alt : ('a -> 'a -> int) -> 'a alt -> 'a alt -> int
val substitution_of : Expr.t Var.Map.t -> Var.t -> Expr.t
module Assert :
  sig
    type t = BExpr.t
    val equal : t -> t -> bool
    val quickcheck_generator : BExpr.t Base_quickcheck.Generator.t
    val quickcheck_observer : BExpr.t Base_quickcheck.Observer.t
    val quickcheck_shrinker : BExpr.t Base_quickcheck.Shrinker.t
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val assert_ : BExpr.t -> t
    val contra : t -> t -> bool
    val to_smtlib : t -> string
    val name : 'a -> string
    val count_asserts : t -> int
    val size : t -> int
    val subst : Var.t -> Expr.t -> t -> t
    val wp : t -> BExpr.t -> BExpr.t
    val normalize_names : BExpr.t -> BExpr.t
    val comparisons : BExpr.t -> (Var.t * Expr.t) list option
    val is_table : t -> bool
    val vars : t -> Var.t list
    val const_prop : Expr.t Var.Map.t -> t -> t * Expr.t Var.Map.t
    val dead_code_elim : Var.Set.t -> t -> (Var.Set.t * BExpr.t) option
    val explode : t -> t list list
  end
module Assume :
  sig
    type t = BExpr.t
    val equal : t -> t -> bool
    val quickcheck_generator : BExpr.t Base_quickcheck.Generator.t
    val quickcheck_observer : BExpr.t Base_quickcheck.Observer.t
    val quickcheck_shrinker : BExpr.t Base_quickcheck.Shrinker.t
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val assume : BExpr.t -> BExpr.t
    val contra : 'a -> 'b -> bool
    val to_smtlib : t -> string
    val name : 'a -> string
    val count_asserts : t -> int
    val size : t -> int
    val subst : Var.t -> Expr.t -> t -> t
    val wp : t -> BExpr.t -> BExpr.t
    val normalize_names : BExpr.t -> BExpr.t
    val comparisons : BExpr.t -> (Var.t * Expr.t) list option
    val is_table : t -> bool
    val const_prop : Expr.t Var.Map.t -> t -> BExpr.t * Expr.t Var.Map.t
    val dead_code_elim : Var.Set.t -> t -> (Var.Set.t * BExpr.t) option
    val explode : t -> t list list
    val vars : t -> Var.t list
  end
module Passive :
  sig
    type t = Assume of BExpr.t | Assert of BExpr.t
    val equal : t -> t -> bool
    val quickcheck_generator : t Base_quickcheck.Generator.t
    val quickcheck_observer : t Base_quickcheck.Observer.t
    val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val assume : BExpr.t -> t
    val assert_ : BExpr.t -> t
    val contra : t -> t -> bool
    val to_smtlib : t -> string
    val name : t -> string
    val count_asserts : t -> int
    val size : t -> int
    val subst : Var.t -> Expr.t -> t -> t
    val wp : t -> BExpr.t -> BExpr.t
    val normalize_names : t -> t
    val comparisons : t -> (Var.t * Expr.t) list option
    val is_node : t -> bool
    val is_table : t -> bool
    val const_prop : Expr.t Var.Map.t -> t -> t * Expr.t Var.Map.t
    val dead_code_elim : t -> Var.Set.t -> (Var.Set.t * t) option
    val explode : t -> t list list
    val vars : t -> Var.t list
  end
module Assign :
  sig
    type t = Var.t * Expr.t
    val equal : t -> t -> bool
    val quickcheck_generator : (Var.t * Expr.t) Base_quickcheck.Generator.t
    val quickcheck_observer : (Var.t * Expr.t) Base_quickcheck.Observer.t
    val quickcheck_shrinker : (Var.t * Expr.t) Base_quickcheck.Shrinker.t
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val to_smtlib : Var.t * Expr.t -> string
    val name : 'a -> string
    val assign : 'a -> 'b -> 'a * 'b
    val count_asserts : t -> int
    val size : 'a * Expr.t -> int
    val subst : Var.t -> Expr.t -> t -> Var.t * Expr.t
    val wp : Var.t * Expr.t -> BExpr.t -> BExpr.t
    val normalize_names : Var.t * Expr.t -> Var.t * Expr.t
    val is_table : t -> bool
    val const_prop :
      Expr.t Var.Map.t ->
      Var.t * Expr.t -> (Var.t * Expr.t) * Expr.t Var.Map.t
    val dead_code_elim :
      Var.t * Expr.t -> Var.Set.t -> (Var.Set.t * (Var.t * Expr.t)) option
    val explode : 'a -> 'a list list
    val reads : 'a * Expr.t -> Var.t list
    val vars : Var.t * Expr.t -> Var.t list
  end
module Active :
  sig
    type pre_t = Passive of Passive.t | Assign of Assign.t
    val equal_pre_t : pre_t -> pre_t -> bool
    val quickcheck_generator_pre_t : pre_t Base_quickcheck.Generator.t
    val quickcheck_observer_pre_t : pre_t Base_quickcheck.Observer.t
    val quickcheck_shrinker_pre_t : pre_t Base_quickcheck.Shrinker.t
    val hash_fold_pre_t :
      Base_internalhash_types.state -> pre_t -> Base_internalhash_types.state
    val hash_pre_t : pre_t -> int
    val pre_t_of_sexp : Sexplib0.Sexp.t -> pre_t
    val sexp_of_pre_t : pre_t -> Sexplib0.Sexp.t
    val compare_pre_t : pre_t -> pre_t -> int
    type t = pre_t alt
    val equal : t -> t -> bool
    val quickcheck_generator : pre_t alt Base_quickcheck.Generator.t
    val quickcheck_observer : pre_t alt Base_quickcheck.Observer.t
    val quickcheck_shrinker : pre_t alt Base_quickcheck.Shrinker.t
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val passive : Passive.t -> t
    val assume : BExpr.t -> t
    val annotate : t -> t option -> pre_t alt
    val assert_ : BExpr.t -> t
    val assign_ : Assign.t -> pre_t alt
    val assign : Var.t -> Expr.t -> pre_t alt
    val contra : pre_t alt -> pre_t alt -> bool
    val to_smtlib : pre_t alt -> string
    val count_asserts : pre_t alt -> int
    val size : pre_t alt -> int
    val subst : Var.t -> Expr.t -> pre_t alt -> t
    val wp : pre_t alt -> BExpr.t -> BExpr.t
    val normalize_names : pre_t alt -> t
    val comparisons : pre_t alt -> (Var.t * Expr.t) list option
    val name : pre_t alt -> string
    val is_node : t -> bool
    val is_table : pre_t alt -> bool
    val const_prop : Expr.t Var.Map.t -> pre_t alt -> t * Expr.t Var.Map.t
    val dead_code_elim : pre_t alt -> Var.Set.t -> (Var.Set.t * t) option
    val explode : pre_t alt -> t list list
    val vars : pre_t alt -> Var.t list
    val reads : pre_t alt -> Var.t list
  end
module Action :
  sig
    type pre_t = Active.pre_t = Passive of Passive.t | Assign of Assign.t
    val equal_pre_t : pre_t -> pre_t -> bool
    val quickcheck_generator_pre_t : pre_t Base_quickcheck.Generator.t
    val quickcheck_observer_pre_t : pre_t Base_quickcheck.Observer.t
    val quickcheck_shrinker_pre_t : pre_t Base_quickcheck.Shrinker.t
    val hash_fold_pre_t :
      Base_internalhash_types.state -> pre_t -> Base_internalhash_types.state
    val hash_pre_t : pre_t -> int
    val pre_t_of_sexp : Sexplib0.Sexp.t -> pre_t
    val sexp_of_pre_t : pre_t -> Sexplib0.Sexp.t
    val compare_pre_t : pre_t -> pre_t -> int
    type t = pre_t alt
    val equal : t -> t -> bool
    val quickcheck_generator : pre_t alt Base_quickcheck.Generator.t
    val quickcheck_observer : pre_t alt Base_quickcheck.Observer.t
    val quickcheck_shrinker : pre_t alt Base_quickcheck.Shrinker.t
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val passive : Passive.t -> t
    val assume : BExpr.t -> t
    val annotate : t -> t option -> pre_t alt
    val assert_ : BExpr.t -> t
    val assign_ : Assign.t -> pre_t alt
    val assign : Var.t -> Expr.t -> pre_t alt
    val contra : pre_t alt -> pre_t alt -> bool
    val to_smtlib : pre_t alt -> string
    val count_asserts : pre_t alt -> int
    val size : pre_t alt -> int
    val subst : Var.t -> Expr.t -> pre_t alt -> t
    val wp : pre_t alt -> BExpr.t -> BExpr.t
    val normalize_names : pre_t alt -> t
    val comparisons : pre_t alt -> (Var.t * Expr.t) list option
    val name : pre_t alt -> string
    val is_node : t -> bool
    val is_table : pre_t alt -> bool
    val const_prop : Expr.t Var.Map.t -> pre_t alt -> t * Expr.t Var.Map.t
    val dead_code_elim : pre_t alt -> Var.Set.t -> (Var.Set.t * t) option
    val vars : pre_t alt -> Var.t list
    val reads : pre_t alt -> Var.t list
    val explode : 'a -> 'a list list
    val cp_action : string -> int -> Var.t
    val cp_data : string -> int -> Var.t -> Var.t
    val symbolize :
      string ->
      num_actions:int ->
      act_size:int -> idx:int -> Var.t list * t list -> BExpr.t * t list
  end
module Table :
  sig
    type t = {
      name : string;
      keys : Var.t list;
      actions : (Var.t list * Action.t list) list;
    }
    val equal : t -> t -> bool
    val quickcheck_generator : t Base_quickcheck.Generator.t
    val quickcheck_observer : t Base_quickcheck.Observer.t
    val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val make : string -> Var.t list -> (Var.t list * Action.t list) list -> t
    val to_smtlib : t -> string
    val name : t -> string
    val size : t -> int
    val subst : Var.t -> Expr.t -> t -> t
    val normalize_names : t -> t
    val is_table : t -> bool
    val const_prop : Expr.t Var.Map.t -> t -> t * Expr.t Var.Map.t
    val dead_code_elim : t -> Var.Set.t -> (Var.Set.t * t) option
    val act_size : t -> int
    val explode : 'a -> 'b
    val vars : t -> Var.t list
    val symbolic_interface : t -> Var.t list
  end
module Pipeline :
  sig
    module P :
      sig
        type t = Active of Active.t | Table of Table.t
        val equal : t -> t -> bool
        val quickcheck_generator : t Base_quickcheck.Generator.t
        val quickcheck_observer : t Base_quickcheck.Observer.t
        val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
        val hash_fold_t :
          Base_internalhash_types.state -> t -> Base_internalhash_types.state
        val hash : t -> int
        val t_of_sexp : Sexplib0.Sexp.t -> t
        val sexp_of_t : t -> Sexplib0.Sexp.t
        val compare : t -> t -> int
        val active : Active.t -> t
        val assign : Var.t -> Expr.t -> t
        val action : Action.t -> t
        val table :
          string -> Var.t list -> (Var.t list * Action.t list) list -> t
        val to_smtlib : t -> string
        val name : t -> string
        val count_asserts : t -> int
        val size : t -> int
        val subst : Var.t -> Expr.t -> t -> t
        val normalize_names : t -> t
        val contra : t -> t -> bool
        val comparisons : t -> (Var.t * Expr.t) list option
        val assume : BExpr.t -> t
        val assert_ : BExpr.t -> t
        val is_node : t -> bool
        val is_table : t -> bool
        val const_prop : Expr.t Var.Map.t -> t -> t * Expr.t Var.Map.t
        val dead_code_elim : t -> Var.Set.t -> (Var.Set.t * t) option
        val explode : t -> t list list
        val to_active_exn : t -> Active.t
        val vars : t -> Var.t list
      end
    module Map :
      sig
        module Key :
          sig
            type t = P.t
            val t_of_sexp : Sexplib0.Sexp.t -> t
            val sexp_of_t : t -> Sexplib0.Sexp.t
            type comparator_witness = Core.Map.Make(P).Key.comparator_witness
            val comparator :
              (t, comparator_witness) Core.Comparator.comparator
          end
        type 'a t = (P.t, 'a, Key.comparator_witness) Base.Map.t
        val compare :
          'a Base.Exported_for_specific_uses.Ppx_compare_lib.compare ->
          'a t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
        val empty : 'a t
        val singleton : Key.t -> 'a -> 'a t
        val map_keys :
          'v t ->
          f:(Key.t -> Key.t) -> [ `Duplicate_key of Key.t | `Ok of 'v t ]
        val map_keys_exn : 'v t -> f:(Key.t -> Key.t) -> 'v t
        val of_alist :
          (Key.t * 'a) list -> [ `Duplicate_key of Key.t | `Ok of 'a t ]
        val of_alist_or_error : (Key.t * 'a) list -> 'a t Base.Or_error.t
        val of_alist_exn : (Key.t * 'a) list -> 'a t
        val of_alist_multi : (Key.t * 'a) list -> 'a list t
        val of_alist_fold :
          (Key.t * 'a) list -> init:'b -> f:('b -> 'a -> 'b) -> 'b t
        val of_alist_reduce : (Key.t * 'a) list -> f:('a -> 'a -> 'a) -> 'a t
        val of_sorted_array : (Key.t * 'a) array -> 'a t Base.Or_error.t
        val of_sorted_array_unchecked : (Key.t * 'a) array -> 'a t
        val of_increasing_iterator_unchecked :
          len:int -> f:(int -> Key.t * 'a) -> 'a t
        val of_increasing_sequence :
          (Key.t * 'a) Base.Sequence.t -> 'a t Base.Or_error.t
        val of_sequence :
          (Key.t * 'a) Base.Sequence.t ->
          [ `Duplicate_key of Key.t | `Ok of 'a t ]
        val of_sequence_or_error :
          (Key.t * 'a) Base.Sequence.t -> 'a t Base.Or_error.t
        val of_sequence_exn : (Key.t * 'a) Base.Sequence.t -> 'a t
        val of_sequence_multi : (Key.t * 'a) Base.Sequence.t -> 'a list t
        val of_sequence_fold :
          (Key.t * 'a) Base.Sequence.t ->
          init:'b -> f:('b -> 'a -> 'b) -> 'b t
        val of_sequence_reduce :
          (Key.t * 'a) Base.Sequence.t -> f:('a -> 'a -> 'a) -> 'a t
        val of_iteri :
          iteri:(f:(key:Key.t -> data:'v -> unit) -> unit) ->
          [ `Duplicate_key of Key.t | `Ok of 'v t ]
        val of_iteri_exn :
          iteri:(f:(key:Key.t -> data:'v -> unit) -> unit) -> 'v t
        val of_tree :
          (Key.t, 'a, Key.comparator_witness) Core.Map_intf.Tree.t -> 'a t
        val of_hashtbl_exn : (Key.t, 'a) Core.Hashtbl.t -> 'a t
        val of_key_set :
          (Key.t, Key.comparator_witness) Base.Set.t ->
          f:(Key.t -> 'v) -> 'v t
        val quickcheck_generator :
          Key.t Core.Quickcheck.Generator.t ->
          'a Core.Quickcheck.Generator.t -> 'a t Core.Quickcheck.Generator.t
        val invariants : 'a t -> bool
        val is_empty : 'a t -> bool
        val length : 'a t -> int
        val add :
          'a t -> key:Key.t -> data:'a -> 'a t Base.Map.Or_duplicate.t
        val add_exn : 'a t -> key:Key.t -> data:'a -> 'a t
        val set : 'a t -> key:Key.t -> data:'a -> 'a t
        val add_multi : 'a list t -> key:Key.t -> data:'a -> 'a list t
        val remove_multi : 'a list t -> Key.t -> 'a list t
        val find_multi : 'a list t -> Key.t -> 'a list
        val change : 'a t -> Key.t -> f:('a option -> 'a option) -> 'a t
        val update : 'a t -> Key.t -> f:('a option -> 'a) -> 'a t
        val find : 'a t -> Key.t -> 'a option
        val find_exn : 'a t -> Key.t -> 'a
        val remove : 'a t -> Key.t -> 'a t
        val mem : 'a t -> Key.t -> bool
        val iter_keys : 'a t -> f:(Key.t -> unit) -> unit
        val iter : 'a t -> f:('a -> unit) -> unit
        val iteri : 'a t -> f:(key:Key.t -> data:'a -> unit) -> unit
        val iteri_until :
          'a t ->
          f:(key:Key.t -> data:'a -> Base.Map.Continue_or_stop.t) ->
          Base.Map.Finished_or_unfinished.t
        val iter2 :
          'a t ->
          'b t ->
          f:(key:Key.t ->
             data:('a, 'b) Base__Map_intf.Merge_element.t -> unit) ->
          unit
        val map : 'a t -> f:('a -> 'b) -> 'b t
        val mapi : 'a t -> f:(key:Key.t -> data:'a -> 'b) -> 'b t
        val fold :
          'a t -> init:'b -> f:(key:Key.t -> data:'a -> 'b -> 'b) -> 'b
        val fold_until :
          'a t ->
          init:'acc ->
          f:(key:Key.t ->
             data:'a ->
             'acc -> ('acc, 'final) Base.Container.Continue_or_stop.t) ->
          finish:('acc -> 'final) -> 'final
        val fold_right :
          'a t -> init:'b -> f:(key:Key.t -> data:'a -> 'b -> 'b) -> 'b
        val fold2 :
          'a t ->
          'b t ->
          init:'c ->
          f:(key:Key.t ->
             data:('a, 'b) Base__Map_intf.Merge_element.t -> 'c -> 'c) ->
          'c
        val filter_keys : 'a t -> f:(Key.t -> bool) -> 'a t
        val filter : 'a t -> f:('a -> bool) -> 'a t
        val filteri : 'a t -> f:(key:Key.t -> data:'a -> bool) -> 'a t
        val filter_map : 'a t -> f:('a -> 'b option) -> 'b t
        val filter_mapi :
          'a t -> f:(key:Key.t -> data:'a -> 'b option) -> 'b t
        val partition_mapi :
          'a t ->
          f:(key:Key.t -> data:'a -> ('b, 'c) Base.Either.t) -> 'b t * 'c t
        val partition_map :
          'a t -> f:('a -> ('b, 'c) Base.Either.t) -> 'b t * 'c t
        val partitioni_tf :
          'a t -> f:(key:Key.t -> data:'a -> bool) -> 'a t * 'a t
        val partition_tf : 'a t -> f:('a -> bool) -> 'a t * 'a t
        val combine_errors : 'a Base.Or_error.t t -> 'a t Base.Or_error.t
        val compare_direct : ('a -> 'a -> int) -> 'a t -> 'a t -> int
        val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
        val keys : 'a t -> Key.t list
        val data : 'a t -> 'a list
        val to_alist :
          ?key_order:[ `Decreasing | `Increasing ] ->
          'a t -> (Key.t * 'a) list
        val merge :
          'a t ->
          'b t ->
          f:(key:Key.t ->
             ('a, 'b) Base__Map_intf.Merge_element.t -> 'c option) ->
          'c t
        val merge_skewed :
          'v t -> 'v t -> combine:(key:Key.t -> 'v -> 'v -> 'v) -> 'v t
        val symmetric_diff :
          'a t ->
          'a t ->
          data_equal:('a -> 'a -> bool) ->
          (Key.t, 'a) Base__Map_intf.Symmetric_diff_element.t Base.Sequence.t
        val fold_symmetric_diff :
          'a t ->
          'a t ->
          data_equal:('a -> 'a -> bool) ->
          init:'c ->
          f:('c -> (Key.t, 'a) Base__Map_intf.Symmetric_diff_element.t -> 'c) ->
          'c
        val min_elt : 'a t -> (Key.t * 'a) option
        val min_elt_exn : 'a t -> Key.t * 'a
        val max_elt : 'a t -> (Key.t * 'a) option
        val max_elt_exn : 'a t -> Key.t * 'a
        val for_all : 'a t -> f:('a -> bool) -> bool
        val for_alli : 'a t -> f:(key:Key.t -> data:'a -> bool) -> bool
        val exists : 'a t -> f:('a -> bool) -> bool
        val existsi : 'a t -> f:(key:Key.t -> data:'a -> bool) -> bool
        val count : 'a t -> f:('a -> bool) -> int
        val counti : 'a t -> f:(key:Key.t -> data:'a -> bool) -> int
        val split : 'a t -> Key.t -> 'a t * (Key.t * 'a) option * 'a t
        val append :
          lower_part:'a t ->
          upper_part:'a t -> [ `Ok of 'a t | `Overlapping_key_ranges ]
        val subrange :
          'a t ->
          lower_bound:Key.t Base.Maybe_bound.t ->
          upper_bound:Key.t Base.Maybe_bound.t -> 'a t
        val fold_range_inclusive :
          'a t ->
          min:Key.t ->
          max:Key.t -> init:'b -> f:(key:Key.t -> data:'a -> 'b -> 'b) -> 'b
        val range_to_alist :
          'a t -> min:Key.t -> max:Key.t -> (Key.t * 'a) list
        val closest_key :
          'a t ->
          [ `Greater_or_equal_to
          | `Greater_than
          | `Less_or_equal_to
          | `Less_than ] -> Key.t -> (Key.t * 'a) option
        val nth : 'a t -> int -> (Key.t * 'a) option
        val nth_exn : 'a t -> int -> Key.t * 'a
        val rank : 'a t -> Key.t -> int option
        val to_tree :
          'a t -> (Key.t, 'a, Key.comparator_witness) Core.Map_intf.Tree.t
        val to_sequence :
          ?order:[ `Decreasing_key | `Increasing_key ] ->
          ?keys_greater_or_equal_to:Key.t ->
          ?keys_less_or_equal_to:Key.t ->
          'a t -> (Key.t * 'a) Base.Sequence.t
        val binary_search :
          'a t ->
          compare:(key:Key.t -> data:'a -> 'key -> int) ->
          Base.Binary_searchable.Which_target_by_key.t ->
          'key -> (Key.t * 'a) option
        val binary_search_segmented :
          'a t ->
          segment_of:(key:Key.t -> data:'a -> [ `Left | `Right ]) ->
          Base.Binary_searchable.Which_target_by_segment.t ->
          (Key.t * 'a) option
        val binary_search_subrange :
          'a t ->
          compare:(key:Key.t -> data:'a -> 'bound -> int) ->
          lower_bound:'bound Base.Maybe_bound.t ->
          upper_bound:'bound Base.Maybe_bound.t -> 'a t
        val key_set : 'a t -> (Key.t, Key.comparator_witness) Base.Set.t
        val validate :
          name:(Key.t -> string) -> 'a Validate.check -> 'a t Validate.check
        val validatei :
          name:(Key.t -> string) ->
          (Key.t * 'a) Validate.check -> 'a t Validate.check
        val quickcheck_observer :
          Key.t Core.Quickcheck.Observer.t ->
          'v Core.Quickcheck.Observer.t -> 'v t Core.Quickcheck.Observer.t
        val quickcheck_shrinker :
          Key.t Core.Quickcheck.Shrinker.t ->
          'v Core.Quickcheck.Shrinker.t -> 'v t Core.Quickcheck.Shrinker.t
        module Provide_of_sexp :
          functor (Key : sig val t_of_sexp : Sexplib0.Sexp.t -> P.t end) ->
            sig
              val t_of_sexp :
                (Sexplib0.Sexp.t -> 'a__002_) ->
                Sexplib0.Sexp.t -> 'a__002_ t
            end
        module Provide_bin_io :
          functor
            (Key : sig
                     val bin_size_t : P.t Bin_prot.Size.sizer
                     val bin_write_t : P.t Bin_prot.Write.writer
                     val bin_read_t : P.t Bin_prot.Read.reader
                     val __bin_read_t__ : (int -> P.t) Bin_prot.Read.reader
                     val bin_shape_t : Bin_prot.Shape.t
                     val bin_writer_t : P.t Bin_prot.Type_class.writer
                     val bin_reader_t : P.t Bin_prot.Type_class.reader
                     val bin_t : P.t Bin_prot.Type_class.t
                   end)
            ->
            sig
              val bin_shape_t : Bin_prot.Shape.t -> Bin_prot.Shape.t
              val bin_size_t : ('a, 'a t) Bin_prot.Size.sizer1
              val bin_write_t : ('a, 'a t) Bin_prot.Write.writer1
              val bin_read_t : ('a, 'a t) Bin_prot.Read.reader1
              val __bin_read_t__ : ('a, int -> 'a t) Bin_prot.Read.reader1
              val bin_writer_t : ('a, 'a t) Bin_prot.Type_class.S1.writer
              val bin_reader_t : ('a, 'a t) Bin_prot.Type_class.S1.reader
              val bin_t : ('a, 'a t) Bin_prot.Type_class.S1.t
            end
        module Provide_hash :
          functor
            (Key : sig
                     val hash_fold_t :
                       Base_internalhash_types.state ->
                       P.t -> Base_internalhash_types.state
                   end)
            ->
            sig
              val hash_fold_t :
                'a Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold ->
                'a t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
            end
        val t_of_sexp : (Sexplib0.Sexp.t -> 'a) -> Sexplib0.Sexp.t -> 'a t
        val sexp_of_t : ('a -> Sexplib0.Sexp.t) -> 'a t -> Sexplib0.Sexp.t
      end
    module Set :
      sig
        module Elt :
          sig
            type t = P.t
            val t_of_sexp : Sexplib0.Sexp.t -> t
            val sexp_of_t : t -> Sexplib0.Sexp.t
            type comparator_witness = Core.Set.Make(P).Elt.comparator_witness
            val comparator :
              (t, comparator_witness) Core.Comparator.comparator
          end
        type t = (P.t, Elt.comparator_witness) Base.Set.t
        val compare :
          t Base.Exported_for_specific_uses.Ppx_compare_lib.compare
        type named = (P.t, Elt.comparator_witness) Base.Set.Named.t
        val length : t -> int
        val is_empty : t -> bool
        val iter : t -> f:(Elt.t -> unit) -> unit
        val fold :
          t -> init:'accum -> f:('accum -> Elt.t -> 'accum) -> 'accum
        val fold_result :
          t ->
          init:'accum ->
          f:('accum -> Elt.t -> ('accum, 'e) Base.Result.t) ->
          ('accum, 'e) Base.Result.t
        val exists : t -> f:(Elt.t -> bool) -> bool
        val for_all : t -> f:(Elt.t -> bool) -> bool
        val count : t -> f:(Elt.t -> bool) -> int
        val sum :
          (module Base__Container_intf.Summable with type t = 'sum) ->
          t -> f:(Elt.t -> 'sum) -> 'sum
        val find : t -> f:(Elt.t -> bool) -> Elt.t option
        val find_map : t -> f:(Elt.t -> 'a option) -> 'a option
        val to_list : t -> Elt.t list
        val to_array : t -> Elt.t array
        val invariants : t -> bool
        val mem : t -> Elt.t -> bool
        val add : t -> Elt.t -> t
        val remove : t -> Elt.t -> t
        val union : t -> t -> t
        val inter : t -> t -> t
        val diff : t -> t -> t
        val symmetric_diff :
          t -> t -> (Elt.t, Elt.t) Base.Either.t Base.Sequence.t
        val compare_direct : t -> t -> int
        val equal : t -> t -> bool
        val is_subset : t -> of_:t -> bool
        val are_disjoint : t -> t -> bool
        module Named :
          sig
            val is_subset : named -> of_:named -> unit Base.Or_error.t
            val equal : named -> named -> unit Base.Or_error.t
          end
        val fold_until :
          t ->
          init:'b ->
          f:('b -> Elt.t -> ('b, 'final) Base.Container.Continue_or_stop.t) ->
          finish:('b -> 'final) -> 'final
        val fold_right : t -> init:'b -> f:(Elt.t -> 'b -> 'b) -> 'b
        val iter2 :
          t ->
          t ->
          f:([ `Both of Elt.t * Elt.t | `Left of Elt.t | `Right of Elt.t ] ->
             unit) ->
          unit
        val filter : t -> f:(Elt.t -> bool) -> t
        val partition_tf : t -> f:(Elt.t -> bool) -> t * t
        val elements : t -> Elt.t list
        val min_elt : t -> Elt.t option
        val min_elt_exn : t -> Elt.t
        val max_elt : t -> Elt.t option
        val max_elt_exn : t -> Elt.t
        val choose : t -> Elt.t option
        val choose_exn : t -> Elt.t
        val split : t -> Elt.t -> t * Elt.t option * t
        val group_by : t -> equiv:(Elt.t -> Elt.t -> bool) -> t list
        val find_exn : t -> f:(Elt.t -> bool) -> Elt.t
        val nth : t -> int -> Elt.t option
        val remove_index : t -> int -> t
        val to_tree :
          t -> (Elt.t, Elt.comparator_witness) Core.Set_intf.Tree.t
        val to_sequence :
          ?order:[ `Decreasing | `Increasing ] ->
          ?greater_or_equal_to:Elt.t ->
          ?less_or_equal_to:Elt.t -> t -> Elt.t Base.Sequence.t
        val binary_search :
          t ->
          compare:(Elt.t -> 'key -> int) ->
          Base.Binary_searchable.Which_target_by_key.t ->
          'key -> Elt.t option
        val binary_search_segmented :
          t ->
          segment_of:(Elt.t -> [ `Left | `Right ]) ->
          Base.Binary_searchable.Which_target_by_segment.t -> Elt.t option
        val merge_to_sequence :
          ?order:[ `Decreasing | `Increasing ] ->
          ?greater_or_equal_to:Elt.t ->
          ?less_or_equal_to:Elt.t ->
          t ->
          t ->
          (Elt.t, Elt.t) Base__Set_intf.Merge_to_sequence_element.t
          Base.Sequence.t
        val to_map :
          t ->
          f:(Elt.t -> 'data) ->
          (Elt.t, 'data, Elt.comparator_witness) Base.Map.t
        val quickcheck_observer :
          Elt.t Core.Quickcheck.Observer.t -> t Core.Quickcheck.Observer.t
        val quickcheck_shrinker :
          Elt.t Core.Quickcheck.Shrinker.t -> t Core.Quickcheck.Shrinker.t
        val empty : t
        val singleton : Elt.t -> t
        val union_list : t list -> t
        val of_list : Elt.t list -> t
        val of_sequence : Elt.t Base.Sequence.t -> t
        val of_array : Elt.t array -> t
        val of_sorted_array : Elt.t array -> t Base.Or_error.t
        val of_sorted_array_unchecked : Elt.t array -> t
        val of_increasing_iterator_unchecked :
          len:int -> f:(int -> Elt.t) -> t
        val stable_dedup_list : Elt.t list -> Elt.t list
        val map : ('a, 'b) Base.Set.t -> f:('a -> Elt.t) -> t
        val filter_map : ('a, 'b) Base.Set.t -> f:('a -> Elt.t option) -> t
        val of_tree :
          (Elt.t, Elt.comparator_witness) Core.Set_intf.Tree.t -> t
        val of_hash_set : Elt.t Core.Hash_set.t -> t
        val of_hashtbl_keys : (Elt.t, 'a) Core.Hashtbl.t -> t
        val of_map_keys : (Elt.t, 'a, Elt.comparator_witness) Base.Map.t -> t
        val quickcheck_generator :
          Elt.t Core.Quickcheck.Generator.t -> t Core.Quickcheck.Generator.t
        module Provide_of_sexp :
          functor (Elt : sig val t_of_sexp : Sexplib0.Sexp.t -> P.t end) ->
            sig val t_of_sexp : Sexplib0.Sexp.t -> t end
        module Provide_bin_io :
          functor
            (Elt : sig
                     val bin_size_t : P.t Bin_prot.Size.sizer
                     val bin_write_t : P.t Bin_prot.Write.writer
                     val bin_read_t : P.t Bin_prot.Read.reader
                     val __bin_read_t__ : (int -> P.t) Bin_prot.Read.reader
                     val bin_shape_t : Bin_prot.Shape.t
                     val bin_writer_t : P.t Bin_prot.Type_class.writer
                     val bin_reader_t : P.t Bin_prot.Type_class.reader
                     val bin_t : P.t Bin_prot.Type_class.t
                   end)
            ->
            sig
              val bin_size_t : t Bin_prot.Size.sizer
              val bin_write_t : t Bin_prot.Write.writer
              val bin_read_t : t Bin_prot.Read.reader
              val __bin_read_t__ : (int -> t) Bin_prot.Read.reader
              val bin_shape_t : Bin_prot.Shape.t
              val bin_writer_t : t Bin_prot.Type_class.writer
              val bin_reader_t : t Bin_prot.Type_class.reader
              val bin_t : t Bin_prot.Type_class.t
            end
        module Provide_hash :
          functor
            (Elt : sig
                     val hash_fold_t :
                       Base_internalhash_types.state ->
                       P.t -> Base_internalhash_types.state
                   end)
            ->
            sig
              val hash_fold_t :
                t Base.Exported_for_specific_uses.Ppx_hash_lib.hash_fold
              val hash : t -> int
            end
        val t_of_sexp : Sexplib0.Sexp.t -> t
        val sexp_of_t : t -> Sexplib0.Sexp.t
      end
    type t = P.t = Active of Active.t | Table of Table.t
    val equal : t -> t -> bool
    val quickcheck_generator : t Base_quickcheck.Generator.t
    val quickcheck_observer : t Base_quickcheck.Observer.t
    val quickcheck_shrinker : t Base_quickcheck.Shrinker.t
    val hash_fold_t :
      Base_internalhash_types.state -> t -> Base_internalhash_types.state
    val hash : t -> int
    val t_of_sexp : Sexplib0.Sexp.t -> t
    val sexp_of_t : t -> Sexplib0.Sexp.t
    val compare : t -> t -> int
    val active : Active.t -> t
    val assign : Var.t -> Expr.t -> t
    val action : Action.t -> t
    val table :
      string -> Var.t list -> (Var.t list * Action.t list) list -> t
    val to_smtlib : t -> string
    val name : t -> string
    val count_asserts : t -> int
    val size : t -> int
    val subst : Var.t -> Expr.t -> t -> t
    val normalize_names : t -> t
    val contra : t -> t -> bool
    val comparisons : t -> (Var.t * Expr.t) list option
    val assume : BExpr.t -> t
    val assert_ : BExpr.t -> t
    val is_node : t -> bool
    val is_table : t -> bool
    val const_prop : Expr.t Var.Map.t -> t -> t * Expr.t Var.Map.t
    val dead_code_elim : t -> Var.Set.t -> (Var.Set.t * t) option
    val explode : t -> t list list
    val to_active_exn : t -> Active.t
    val vars : t -> Var.t list
  end
