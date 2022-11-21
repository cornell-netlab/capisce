open Core

module type Cmd_core = sig
  module P : sig
    type t
  end
  type t
  val to_string : t -> string
  val size : t -> int
  val skip : t
  val dead : t
  val prim : P.t -> t
  val choices : t list -> t
  val sequence : t list -> t
  val top_down :
    init:'a ->
    prim:('a -> P.t -> 'a) ->
    sequence:('a -> t list -> ('a -> t -> 'a) -> 'a) ->
    choices:('a -> t list -> ('a -> t -> 'a) -> 'a) ->
    t ->
    'a

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

module Substitutor (Cmd : sig
    include Cmd_core
    type elt
    val psubst : elt Var.Map.t -> P.t -> (P.t * elt Var.Map.t)
    val merge : elt option -> elt option -> elt option
  end ) = struct

  let with_map (subst : Cmd.elt Var.Map.t) c : (Cmd.t * Cmd.elt Var.Map.t) option =
    let open Option.Let_syntax in
    let open Cmd in
    top_down c
      ~init:(Some (skip, subst))
      ~prim:(fun opt p ->
          let%map (_, subst) = opt in
          let  p', subst = psubst subst p in
          prim p', subst
        )
      ~sequence:(fun acc cs recursive_call ->
          let%bind (_, subst) = acc in
          List.fold_left ~init:(Some (skip, subst)) cs
            ~f:(fun acc c ->
                let%bind (acc_c, subst) = acc in
                let%map  (c', subst) = recursive_call (Some (skip, subst)) c in
                (sequence [acc_c; c'], subst)
              )
        )
      ~choices:(fun acc cs recursive_call ->
          let f = recursive_call acc in
          Util.fold_right1 cs
            ~init:f
            ~f:(fun curr_c acc ->
                let%bind (curr_c, curr_subst) = f curr_c in
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
    include Cmd_core
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
    include Cmd_core
    val prim_dead_code_elim : P.t -> Var.Set.t -> (Var.Set.t * P.t) option
  end) = struct

  open Cmd

  let elim_with_reads reads c =
    top_down c
      ~init:(reads, skip)
      ~prim:(fun (reads, _) p ->
          match prim_dead_code_elim p reads with
          | None -> (reads, skip)
          | Some (reads, p) ->
            (reads, prim p)
        )
      ~choices:(fun reads cs recursive_call ->
          let f = recursive_call reads in
          List.map cs ~f
          |> List.fold ~init:(Var.Set.empty, Cmd.dead)
            ~f:(fun (r_acc, c_acc) (r, c) ->
                (Var.Set.union r_acc r,
                 choices [c; c_acc]
                )
              )
        )
      ~sequence:(fun (reads,_) cs recursive_call ->
          List.fold_right cs ~init:(reads, skip)
            ~f:(fun c (reads, cs) ->
                let reads, c = recursive_call (reads, skip) c in
                reads, sequence [c;cs]
              )

        )
  let elim c = elim_with_reads Var.Set.empty c |> snd

end


module Optimizer ( Cmd : sig
    include Cmd_core
    val equal : t -> t -> bool
    val prim_dead_code_elim : P.t -> Var.Set.t -> (Var.Set.t * P.t) option
    val prim_const_prop : Expr.t Var.Map.t -> P.t -> (P.t * Expr.t Var.Map.t)
  end ) = struct

  module CP = ConstProp (Cmd)
  module DC = DeadCodeElim (Cmd)

  let optimize : Cmd.t -> Cmd.t =
    Log.compiler_s "optimizing...";
    let o c =
      Log.debug_s "FIX";
      let opt = DC.elim (CP.propagate_exn c) in
      if Cmd.size opt > Cmd.size c then begin
        let () = Log.irs "PRE: %s\n" @@ lazy (Cmd.to_string c) in
        let () = Log.irs "POST: %s\n" @@ lazy (Cmd.to_string opt) in
        failwithf "GOT BIGGER, from %d to %d" (Cmd.size c) (Cmd.size opt) ()
      end;
      opt

    in
    let equal c1 c2 =
      if Cmd.equal c1 c2 then
        true
      else
        let () = Log.irs "PRE: %s\n" @@ lazy (Cmd.to_string c1) in
        let () = Log.irs "POST: %s\n" @@ lazy (Cmd.to_string c2) in
        let () = Breakpoint.set true in
        false
    in

    Util.fix ~equal o

  let optimize_seq_pair (c1,c2) =
    (* let open Option.Let_syntax in *)
    let dce (c1,c2) =
      Log.compiler_s "DCE";
      let (reads, c2) = DC.elim_with_reads Var.Set.empty c2 in
      Log.compiler_s "C2 DONE";
      let (_    , c1) = DC.elim_with_reads reads c1 in
      Log.compiler_s "DCE DONE";
      (c1, c2)
    in
    let cp_o (c1, c2) =
      Log.compiler_s "CP";
      Some (c1,c2)
    in
    let cp (c1, c2) = cp_o (c1,c2) |> Option.value_exn ~message:"[optimize_seq_pair] constant_propagation failed" in
    let equal (c1,c2) (c1',c2') = Cmd.equal c1 c1' && Cmd.equal c2 c2' in
    let o (c1,c2) =
      Log.debug "FIX:\n%s" @@ lazy (Cmd.to_string c1);
      dce @@ cp (c1,c2)  in
    Util.fix ~equal o (c1,c2)

end
