open Core

module type Cmd_core = sig
  module P : sig
    type t
  end
  type t
  val skip : t
  val prim : P.t -> t
  val choices : t list -> t
  val sequence : t list -> t
end


module type Cmd_bottom = sig
  include Cmd_core
  val bottom_up :
    prim:(P.t -> 'a) ->
    sequence:('a list -> 'a) ->
    choices:('a list -> 'a) ->
    t ->
    'a
end

module type Cmd_fwd = sig
  include Cmd_core
  val forward :
    init:'a ->
    prim:('a -> P.t -> 'a) ->
    choices:('a list -> 'a)
    -> t
    -> 'a
end

module type Cmd_bwd = sig
  include Cmd_core
  val backward :
    init:'a ->
    prim:(P.t -> 'a -> 'a) ->
    choices:('a list -> 'a)
    -> t
    -> 'a
end

module type Cmd_fwd_bwd = sig
  include Cmd_core
  val forward :
    init:'a ->
    prim:('a -> P.t -> 'a) ->
    choices:('a list -> 'a)
    -> t
    -> 'a

  val backward :
    init:'a ->
    prim:(P.t -> 'a -> 'a) ->
    choices:('a list -> 'a)
    -> t
    -> 'a

end

module Substitutor (Cmd : sig
    include Cmd_fwd
    type elt
    val psubst : elt Var.Map.t -> P.t -> (P.t * elt Var.Map.t)
    val merge : elt option -> elt option -> elt option
  end ) = struct

  let with_map (subst : Cmd.elt Var.Map.t) c : (Cmd.t * Cmd.elt Var.Map.t) option =
    let open Option.Let_syntax in
    let open Cmd in
    forward c
      ~init:(Some (skip, subst))
      ~prim:(fun opt p ->
          let%map (c, subst) = opt in
          let p, subst = psubst subst p in
          sequence [c; prim p],
          subst
        )
      ~choices:(
        Util.fold_right1
          ~init:Fn.id
          ~f:(fun curr acc ->
              let%bind (curr_c, curr_subst) = curr in
              let%map  ( acc_c,  acc_subst) = acc in
              choices [curr_c; acc_c],
              Var.Map.merge curr_subst acc_subst
                ~f:(fun ~key:_ -> function
                    | `Left a     -> merge (Some a) None
                    | `Right b    -> merge None (Some b)
                    | `Both (a,b) -> merge (Some a) (Some b)))
        )

  let one (x : Var.t) (y : 'a) (c : Cmd.t) : (Cmd.t * Cmd.elt Var.Map.t) option =
    let m = Var.Map.singleton x y in
    with_map m c

end

module Normalize (Cmd : sig
    include Cmd_bottom
    val normalize_prim : P.t -> P.t
  end) = struct
  open Cmd

  let normalize c =
    let prim p = prim (normalize_prim p) in
    bottom_up c ~prim ~choices ~sequence

end

module ConstProp (Cmd : sig
    include Cmd_fwd
    val prim_const_prop : Expr.t Var.Map.t -> P.t -> (P.t * Expr.t Var.Map.t)
  end) = struct

  let psubst = Cmd.prim_const_prop
  let merge left right =
    match left, right with
    | Some x, Some y when Expr.equal x y ->
      Some x
    | _, _ ->
      None

  module S = Substitutor (struct
      include Cmd
      type elt = Expr.t
      let psubst = psubst
      let merge = merge
    end)

  let propagate_with_map = S.with_map

  let propagate_exn c =
    propagate_with_map Var.Map.empty c
    |> Option.value_exn ~message:"Constant Propagation Failed"
    |> fst

end


module DeadCodeElim (Cmd : sig
    include Cmd_bwd
    val prim_dead_code_elim : P.t -> Var.Set.t -> (Var.Set.t * P.t) option
  end) = struct

  open Cmd

  let elim_with_reads reads c =
    backward c
      ~init:(reads, skip)
      ~prim:(fun p (reads, acc) ->
          match prim_dead_code_elim p reads with
          | None -> (reads, acc)
          | Some (reads, p) ->
            (reads, sequence [prim p; acc])
        )
      ~choices:(fun results ->
          Util.fold_right1 results
            ~init:Fn.id
            ~f:(fun (reads, c) (reads_acc, c_acc) ->
                Var.Set.union reads reads_acc,
                choices [c; c_acc])
        )

  let elim c = elim_with_reads Var.Set.empty c |> snd

end


module Optimizer ( Cmd : sig
    include Cmd_fwd_bwd
    val equal : t -> t -> bool
    val prim_dead_code_elim : P.t -> Var.Set.t -> (Var.Set.t * P.t) option
    val prim_const_prop : Expr.t Var.Map.t -> P.t -> (P.t * Expr.t Var.Map.t)
  end ) = struct

  module CP = ConstProp (Cmd)
  module DC = DeadCodeElim (Cmd)

  let optimize : Cmd.t -> Cmd.t =
    Log.compiler_s "optimizing...";
    let o c = DC.elim (CP.propagate_exn c) in
    Util.fix ~equal:Cmd.equal o

  let optimize_seq_pair (c1,c2) =
    let open Option.Let_syntax in
    let dce (c1,c2) =
      let (reads, c2) = DC.elim_with_reads Var.Set.empty c2 in
      let (_    , c1) = DC.elim_with_reads reads c1 in
      (c1, c2)
    in
    let cp_o (c1, c2)=
      let%bind (c1, facts) = CP.propagate_with_map Var.Map.empty c1 in
      let%bind (c2, _    ) = CP.propagate_with_map facts c2 in
      return (c1, c2)
    in
    let cp (c1, c2) = cp_o (c1,c2) |> Option.value_exn ~message:"[optimize_seq_pair] constant_propagation failed" in
    let equal (c1,c2) (c1',c2') = Cmd.equal c1 c1' && Cmd.equal c2 c2' in
    let o (c1,c2) = dce @@ cp (c1,c2)  in
    Util.fix ~equal o (c1,c2)

end
