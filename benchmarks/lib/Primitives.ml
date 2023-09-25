open Core
open Option.Let_syntax

module type Primitive = sig
  type t [@@deriving quickcheck, eq, hash, sexp, compare]
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val contra : t -> t -> bool
  val to_smtlib : t -> string
  val size : t -> int
  val vars : t -> Var.t list
end

let substitution_of facts x =
  match Var.Map.find facts x with
  | None -> Expr.var x
  | Some e -> e

module Assert = struct
  type t = BExpr.t
  [@@deriving quickcheck, eq, hash, sexp, compare]

  let assert_ b = b
  let contra b1 b2 =
    BExpr.equal b1 (BExpr.not_ b2) || BExpr.equal b2 (BExpr.not_ b2)
  let to_smtlib b =
    Printf.sprintf "assert %s" (BExpr.to_smtlib b)
  let name _ = Printf.sprintf "assert"
  let count_asserts (_:t) = 1
  let size (b : t) = BExpr.size b
  let subst x e (b:t) : t = BExpr.subst x e b
  let wp (b:t) (phi : BExpr.t) : BExpr.t = BExpr.and_ b phi
  let normalize_names : t -> t = BExpr.normalize_names
  let comparisons = BExpr.comparisons
  let is_table (_:t) = false
  let vars b = BExpr.vars b |> Tuple2.uncurry (@)

  let const_prop facts b : t * Expr.t Var.Map.t =
    let b = BExpr.fun_subst (substitution_of facts) b |> BExpr.simplify in
    (assert_ b, facts)

  let dead_code_elim reads b =
    let read_by_b = Var.Set.of_list (Util.concat (BExpr.vars b)) in
    let b = BExpr.simplify b in
    Some (Var.Set.union reads read_by_b, assert_ b)

  let explode b = [[b]]

end

module Assume = struct
  type t = BExpr.t
  [@@deriving quickcheck, eq, hash, sexp, compare]

  let assume b = b
  let contra _ _ = false
  let to_smtlib b =
    Printf.sprintf "assume %s" (BExpr.to_smtlib b)
  let name _ = Printf.sprintf "assume"
  let count_asserts (_:t) = 0
  let size (b : t) = BExpr.size b
  let subst x e (b:t) : t = BExpr.subst x e b
  let wp (b:t) (phi : BExpr.t) : BExpr.t = BExpr.imp_ b phi
  let normalize_names : t -> t = BExpr.normalize_names
  let comparisons = BExpr.comparisons
  let is_table (_:t) = false

  let const_prop f b = Assert.const_prop f b
  let dead_code_elim reads b = Assert.dead_code_elim reads b

  let explode b = [[b]]
  let vars b = BExpr.vars b |> Tuple2.uncurry (@)

end

module Passive = struct
  type t =
    | Assume of BExpr.t
    | Assert of Assert.t
  [@@deriving quickcheck, eq, hash, sexp, compare]

  let assume b = Assume b
  let assert_ a = Assert a

  let contra c1 c2 =
    match c1, c2 with
    | Assert b1, Assert b2 -> Assert.contra b1 b2
    | _, _ -> false

  let to_smtlib = function
    | Assume b ->
      Printf.sprintf "assume %s%!" (BExpr.to_smtlib b)
    | Assert b -> Assert.to_smtlib b

  let name = function
    | Assume _ -> "assume"
    | Assert b ->
      Assert.name b

  let count_asserts = function
    | Assume _ -> 0
    | Assert _ -> 1

  let size = function
    | Assume b -> 1 + BExpr.size b
    | Assert b -> 1 + Assert.size b

  let subst x e = function
    | Assume b -> assume (BExpr.subst x e b)
    | Assert b -> assert_ (Assert.subst x e b)

  let wp t phi = match t with
    | Assume b -> BExpr.imp_ b phi
    | Assert b -> Assert.wp b phi

  let normalize_names = function
    | Assume b -> assume (BExpr.normalize_names b)
    | Assert b -> assert_ (Assert.normalize_names b)

  let comparisons = function
    | Assume b -> BExpr.comparisons b
    | Assert _ -> None

  let is_node (_:t) = true

  let is_table = function
    | Assume _ -> false
    | Assert a -> Assert.is_table a

  let const_prop f : t -> (t * Expr.t Var.Map.t) = function
    | Assert a ->
      let a, f = Assert.const_prop f a in
      (assert_ a, f)
    | Assume b ->
      let b, f = Assume.const_prop f b in
      (assume b, f)

  let dead_code_elim c reads =
    match c with
    | Assert b ->
      let%map reads, b = Assert.dead_code_elim reads b in
      (reads, assert_ b)
    | Assume b ->
      let%map reads, b = Assume.dead_code_elim reads b in
      (reads, assume b)

  let explode = function
    | Assert b -> Assert.explode b |> Util.mapmap ~f:assert_
    | Assume b -> Assume.explode b |> Util.mapmap ~f:assume

  let vars = function
    | Assert b -> Assert.vars b
    | Assume b -> Assume.vars b

end

module Assign = struct
  type t = Var.t * Expr.t
  [@@deriving quickcheck, eq, sexp, compare, hash]

  let to_smtlib (x,e) = Printf.sprintf "%s:=%s" (Var.str x) (Expr.to_smtlib e)

  let name _ = "assign"

  let assign x e = (x,e)

  let count_asserts (_ : t) = 0

  let size (_,e) = 1 + Expr.size e

  let subst x e ((y,e') : t) =
    if Var.(x = y) then
      failwithf "tried to substitute an lvalue %s with %s" (Var.str x) (Expr.to_smtlib e) ()
    else
      assign y (Expr.subst x e e')

  let wp (x,e) phi =  BExpr.subst x e phi

  let normalize_names (x,e) = assign (Var.normalize_name x) (Expr.normalize_names e)

  let is_table (_:t) = false

  let const_prop (facts : Expr.t Var.Map.t) (x,e) =
    let e = Expr.fun_subst (substitution_of facts) e in
    let vars = Expr.vars e |> Tuple2.uncurry (@) in
    if List.exists vars ~f:(Var.(=) x) then
      (assign x e, facts)
    else
      let facts = Var.Map.set facts ~key:x ~data:e in
      (assign x e, facts)

  let dead_code_elim (x,e) (reads : Var.Set.t) =
    if Var.Set.exists reads ~f:(Var.(=) x) then
      let read_by_e = Var.Set.of_list (Util.concat (Expr.vars e)) in
      let reads_minus_x = Var.Set.remove reads x in
      let reads = Var.Set.union read_by_e reads_minus_x in
      Some (reads, assign x e)
    else
      (* let () = Log.compiler "Eliminating %s because it's dead" @@ lazy (to_smtlib (x,e)) in *)
      None

  let explode assign = [[assign]]

  let vars (x,e) =
    Expr.vars e
    |> Tuple2.uncurry (@)
    |> List.cons x

end

module Active = struct
  type t =
    | Passive of Passive.t
    | Assign of Assign.t
  [@@deriving quickcheck, eq, hash, sexp, compare]

  let passive p = Passive p
  let assume b = Passive (Passive.assume b)
  let assert_ b = Passive (Passive.assert_ b)
  let assign_ a = Assign a
  let assign x e = assign_ (Assign.assign x e)
  let contra a1 a2 =
    match a1, a2 with
    | Passive p1, Passive p2 -> Passive.contra p1 p2
    | _, _ -> false

  let to_smtlib = function
    | Passive p -> Passive.to_smtlib p
    | Assign a -> Assign.to_smtlib a

  let count_asserts = function
    | Passive p -> Passive.count_asserts p
    | Assign a -> Assign.count_asserts a

  let size = function
    | Passive p -> Passive.size p
    | Assign a -> Assign.size a

  (* let vars = function *)
  (*   | Passive p -> Passive.vars p *)
  (*   | Active a -> Assign.vars a *)

  let subst x e = function
    | Passive p -> Passive (Passive.subst x e p)
    | Assign a -> Assign (Assign.subst x e a)

  let wp active phi = match active with
    | Passive p -> Passive.wp p phi
    | Assign p -> Assign.wp p phi

  let normalize_names = function
    | Passive p -> Passive (Passive.normalize_names p)
    | Assign a -> Assign (Assign.normalize_names a)

  let comparisons = function
    | Passive p -> Passive.comparisons p
    | Assign _ -> None

  let name = function
    | Passive p -> Passive.name p
    | Assign a -> Assign.name a

  let is_node (_:t) = true

  (* let of_action = function *)
  (*   | Action.Assign (x,e) -> assign x e *)
  (*   | Action.Assert b -> assert_ b *)

  let is_table = function
    | Passive p -> Passive.is_table p
    | Assign a -> Assign.is_table a

  let const_prop f = function
    | Passive p ->
      let p, f = Passive.const_prop f p in
      (Passive p, f)
    | Assign a ->
      let a, f = Assign.const_prop f a in
      (Assign a, f)

  let dead_code_elim c reads =
    match c with
    | Passive p ->
      let%map reads, p = Passive.dead_code_elim p reads in
      (reads, passive p)
    | Assign a ->
      let%map reads, a = Assign.dead_code_elim a reads in
      (reads, assign_ a)

  let explode = function
    | Passive p ->  Passive.explode p |> Util.mapmap ~f:passive
    | Assign a -> List.map ~f:(List.map ~f:assign_) (Assign.explode a)

  let vars = function
    | Passive p -> Passive.vars p
    | Assign a -> Assign.vars a
end


module Action = struct
  include Active

  let explode action = [[action]]

  let cp_action name act_size = Var.make (Printf.sprintf "_symb$%s$action" name) act_size
  let cp_data name act_idx param =
     Var.make (Printf.sprintf  "_symb$%s$%d$%s" name act_idx (Var.str param)) (Var.size param)

  let symbolize (name : string)
      ~num_actions
      ~act_size
      ~idx
      ((params : Var.t list), (body : t list)) : (BExpr.t * t list) =
    let act_choice =
      let c = if idx >= num_actions - 1 then BExpr.uge_ else BExpr.eq_ in
      if String.(name = "classifier") then
        Log.debug "[symbolize] classifier action_size = %d" @@ lazy act_size;
      c (cp_action name act_size |> Expr.var ) (Expr.bvi idx act_size)
    in
    let symb param = Expr.var (cp_data name idx param) in
    let symbolize body param = subst param (symb param) body in
    let f body = List.fold params ~init:body ~f:symbolize in
    (act_choice, List.map body ~f)

end

module Table = struct
  type t = {name : string;
            keys : Var.t list;
            actions : (Var.t list * Action.t list) list;
           }
  [@@deriving quickcheck, hash, eq, sexp, compare]


  let make name keys actions = {name; keys; actions}

  let to_smtlib tbl = Printf.sprintf "%s.apply(){%s}" tbl.name @@
    List.fold tbl.actions ~init:"" ~f:(fun acc (params, commands) ->
        Printf.sprintf "%s\n\t\\%s -> {%s\t}" acc (Var.list_to_smtlib_quant params) @@
        List.fold commands ~init:"\n" ~f:(fun acc a ->
            Printf.sprintf "%s\t\t%s\n" acc (Action.to_smtlib a)
          )
      )

  let name tbl = tbl.name

  let size (tbl : t) =
    1 + List.length tbl.keys +
    List.sum (module Int) tbl.actions ~f:(fun (_,prims) ->
        List.sum (module Int) prims ~f:(Action.size))

  let subst x e (tbl : t) =
    if List.exists tbl.keys ~f:(Var.equal x) then
      failwithf "Cannot substitute variable %s, its a key in table %s" (Var.str x) tbl.name ()
    else
      let open List.Let_syntax in
      let actions =
        let%map (args, body) = tbl.actions in
        if List.exists args ~f:(Var.equal x) then
          (args, body)
        else
          let body = List.map body ~f:(Action.subst x e) in
          (args, body)
      in
      {tbl with actions}

  let normalize_names (tbl : t) =
    let open List.Let_syntax in
    let keys = List.map tbl.keys ~f:(Var.normalize_name) in
    let actions =
      let%map (args, body) = tbl.actions in
      (List.map ~f:Var.normalize_name args,
       List.map ~f:Action.normalize_names body )
    in
    {tbl with keys; actions}

  let is_table (_:t) = true

  let const_prop f0 t =
    (* WARNING: keys are not used *)
    let (actions, f) =
      List.fold t.actions  ~init:([], None)
      ~f:(fun (acts, f) (vars, action) ->
          let rev_action, f1 =
            List.fold action ~init:([], f0) ~f:(fun (action, f) a ->
                let (a, f) = Action.const_prop f a in
                (a::action, f))
          in
          let action = List.rev rev_action in
          match f with
          | None -> ([(vars, action)], Some f1)
          | Some f ->
            let facts =
              Var.Map.merge f f1
                ~f:(fun ~key:_ -> function
                    | `Left _ | `Right _ ->
                      None
                    | `Both (a,b) ->
                      Option.some_if (Expr.equal a b) a
                  )
            in
            (acts@[vars, action], Some facts)
        )
    in
    ({t with actions}, Option.value_exn f)

  let dead_code_elim (t : t) (reads : Var.Set.t) : (Var.Set.t * t) option =
    let dead_code_elim_action (body : Action.t list) (reads : Var.Set.t) =
      List.fold (List.rev body)
        ~init:(reads, [])
        ~f:(fun (reads, acts) act_stmt ->
            match Action.dead_code_elim act_stmt reads with
            | None ->
              (reads, acts)
            | Some (reads, a) ->
              (reads, a::acts)
          )
    in
    let (reads, actions) =
      List.fold t.actions ~init:None ~f:(fun acc_opt (params, body) ->
          let (reads, body) = dead_code_elim_action body reads in
          let reads = Var.Set.diff reads (Var.Set.of_list params) in
          match acc_opt with
          | None -> Some (reads, [(params, body)])
          | Some (reads_acc, acts_acc) ->
            Some (Var.Set.union reads_acc reads, acts_acc @ [(params, body)]))
      |> Option.value_exn ~message:"Table had no actions"
    in
    Some (reads, {t with actions})

  let act_size tbl =
    if List.length tbl.actions <= 0 then failwithf "Table %s has 0 actions" tbl.name ();
    List.length tbl.actions
    |> Util.bits_to_encode_n_things

  let explode _ = failwith "Ironically tables themselves cannot be exploded"

  let vars t =
    t.keys @
    List.bind t.actions ~f:(fun (params, commands) ->
        params @ List.bind commands ~f:(Action.vars))
    |> Var.dedup

  let symbolic_interface tbl : Var.t list =
    if String.(tbl.name = "classifier") then
      Log.debug "[symbolic_interface] classifier action_size = %d" @@ lazy (act_size tbl);
    Action.cp_action tbl.name (act_size tbl)
    :: List.bind tbl.keys ~f:(fun k -> [k; Var.make (Var.str k ^ "$DONT_CARE") 1])
    @ List.bind ~f:fst tbl.actions

end

module Pipeline = struct
  module P = struct
    type t =
      | Active of Active.t
      | Table of Table.t
    [@@deriving quickcheck, eq, hash, sexp, compare]

    let active a = Active a
    let assign x e = active @@ Active.assign x e

    let action (a : Action.t) = Active a

    let table name keys actions =
      Table (Table.make name keys actions)

    let to_smtlib = function
      | Active a -> Active.to_smtlib a
      | Table t -> Table.to_smtlib t

    let name = function
      | Active a -> Active.name a
      | Table t -> Table.name t

    let count_asserts = function
      | Active a -> Active.count_asserts a
      | Table _ -> 0

    let size = function
      | Active a -> Active.size a
      | Table t -> Table.size t

    let subst x e = function
      | Active a -> Active (Active.subst x e a)
      | Table t -> Table (Table.subst x e t)

    let normalize_names = function
      | Active a -> Active (Active.normalize_names a)
      | Table t -> Table (Table.normalize_names t)

    let contra c1 c2 = match c1, c2 with
      | Active a1, Active a2 ->
        Active.contra a1 a2
      | _, _ -> false

    let comparisons = function
      | Table _ -> None
      | Active a -> Active.comparisons a
    let assume b = Active (Active.assume b)
    let assert_ b = Active (Active.assert_ b)
    let is_node (_:t) = true

    let is_table = function
      | Active a -> Active.is_table a
      | Table t -> Table.is_table t

    let const_prop f = function
      | Active a ->
        let a, f = Active.const_prop f a in
        (Active a, f)
      | Table t ->
        let t, f = Table.const_prop f t in
        (Table t, f)

    let dead_code_elim c reads =
      match c with
      | Active a ->
        let%map reads, a = Active.dead_code_elim a reads in
        (reads, Active a)
      | Table t ->
        let%map reads, t = Table.dead_code_elim t reads in
        (reads, Table t)

    let explode : t -> t list list = function
      | Active a ->
        Active.explode a
        |> Util.mapmap ~f:(fun a -> Active a)
      | Table tbl ->
        (* let cp_key idx  = Printf.sprintf "_symb$%s$match_%d" name idx in *)
        (* let phi_keys = List.mapi keys ~f:(fun idx k -> *)
        (*     let symb_k = Var.make (cp_key idx) (Var.size k) in *)
        (*     BExpr.eq_ (Expr.var symb_k) (Expr.var k)) in *)
        let act_size = Table.act_size tbl in
        let of_action_list = List.map ~f:active in
        let num_actions = List.length tbl.actions in
        let f idx action =
          let (phi, acts) = Action.symbolize tbl.name ~num_actions ~act_size ~idx action in
          assume phi :: of_action_list acts
        in
        List.mapi (List.rev tbl.actions) ~f

    let to_active_exn = function
      | Active a -> a
      | Table tbl -> failwithf "cannot convert table %s to action" tbl.name ()


    let vars = function
      | Active  a -> Active.vars a
      | Table tbl -> Table.vars tbl

  end

  module Map = Map.Make (P)
  module Set = Set.Make (P)
  include P
end
