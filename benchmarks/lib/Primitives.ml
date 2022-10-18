open Core
open Option.Let_syntax

module type Primitive = sig
  type t [@@deriving quickcheck, eq, hash, sexp, compare]
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val contra : t -> t -> bool
  val to_smtlib : t -> string
  val count_asserts : t -> int
  val size : t -> int
  val subst : Var.t -> Expr.t -> t -> t
  val normalize_names : t -> t
  val comparisons : t -> (Var.t * Expr.t) list option
  val is_node : t -> bool
  val name : t -> string
  val is_table : t -> bool
  val const_prop : Facts.t -> t -> (Facts.t * t)
  val dead_code_elim : Var.Set.t -> t -> (Var.Set.t * t) option
end


module Assert = struct
  type t = BExpr.t
  [@@deriving quickcheck, eq, hash, sexp, compare]

  let assert_ b = b
  let contra b1 b2 = BExpr.equal b1 (BExpr.not_ b2) || BExpr.equal b2 (BExpr.not_ b2)
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

  let const_prop f b =
    let b = BExpr.fun_subst (Facts.lookup f) b |> BExpr.simplify in
    let f =
      match BExpr.get_equality b with
      | Some (x, e) -> Facts.update f x e
      | None -> f
    in
    (f, assert_ b)

  let dead_code_elim reads b =
    let read_by_b = Var.Set.of_list (Util.concat (BExpr.vars b)) in
    let b = BExpr.simplify b in
    Some (Var.Set.union reads read_by_b, assert_ b)

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

  let const_prop f : t -> (Facts.t * t)= function
    | Assert a ->
      let f, a = Assert.const_prop f a in
      (f, assert_ a)
    | Assume b ->
      let f, b = Assume.const_prop f b in
      (f, assume b)

  let dead_code_elim reads = function
    | Assert b ->
      let%map reads, b = Assert.dead_code_elim reads b in
      (reads, assert_ b)
    | Assume b ->
      let%map reads, b = Assume.dead_code_elim reads b in
      (reads, assume b)

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

  let const_prop (f : Facts.t) (x,e) =
    let e = Expr.fun_subst (Facts.lookup f) e in
    let f = Facts.update f x e in
    (f, assign x e)

  let dead_code_elim (reads : Var.Set.t) (x,e) =
    if Var.Set.exists reads ~f:(Var.(=) x) then
      let read_by_e = Var.Set.of_list (Util.concat (Expr.vars e)) in
      let reads_minus_x = Var.Set.remove reads x in
      let reads = Var.Set.union read_by_e reads_minus_x in
      Some (reads, assign x e)
    else
      None



end


module Action = struct
  type t =
    | Assign of Assign.t
    | Assert of Assert.t
  [@@deriving quickcheck, hash, eq, sexp, compare]

  let assign x e = Assign (Assign.assign x e)
  let assert_ b = Assert (Assert.assert_ b)
  let assume _ = failwith "assumes are not allowed in actions"
  let contra c1 c2 = match c1,c2 with
    | Assert b1, Assert b2 -> Assert.contra b1 b2
    | _ -> false

  let to_smtlib = function
    | Assign a -> Assign.to_smtlib a
    | Assert b -> Assert.to_smtlib b

  let name = function
    | Assign a -> Assign.name a
    | Assert b -> Assert.name b

  let size = function
    | Assign a -> Assign.size a
    | Assert b -> Assert.size b

  let subst x e = function
    | Assign a -> Assign (Assign.subst x e a)
    | Assert b -> Assert (Assert.subst x e b)

  let normalize_names = function
    | Assign a -> Assign (Assign.normalize_names a)
    | Assert b -> Assert (Assert.normalize_names b)

  let count_asserts = function
    | Assign a -> Assign.count_asserts a
    | Assert b -> Assert.count_asserts b

  let comparisons = function
    | Assign _ -> None
    | Assert b -> Assert.comparisons b

  let is_node (_ : t) = true
  let is_table (_:t) = false

  let const_prop f = function
    | Assign a ->
      let (f, a) = Assign.const_prop f a in
      (f, Assign a)
    | Assert a ->
      let (f, a) = Assert.const_prop f a in
      (f, Assert a)

  let dead_code_elim reads = function
    | Assign a ->
      let%map (reads, (x,e)) = Assign.dead_code_elim reads a in
      (reads, assign x e)
    | Assert a ->
      let%map (reads, a) = Assert.dead_code_elim reads a in
      (reads, assert_ a)

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

  let of_action = function
    | Action.Assign (x,e) -> assign x e
    | Action.Assert b -> assert_ b

  let is_table = function
    | Passive p -> Passive.is_table p
    | Assign a -> Assign.is_table a

  let const_prop f = function
    | Passive p ->
      let f, p = Passive.const_prop f p in
      (f, Passive p)
    | Assign a ->
      let f , a = Assign.const_prop f a in
      (f, Assign a)

  let dead_code_elim reads = function
    | Passive p ->
      let%map reads, p = Passive.dead_code_elim reads p in
      (reads, passive p)
    | Assign a ->
      let%map reads, a = Assign.dead_code_elim reads a in
      (reads, assign_ a)
end

module Table = struct
  type t = {name : string;
            keys : Var.t list;
            actions : (Var.t list * Action.t list) list }
  [@@deriving quickcheck, hash, eq, sexp, compare]

  let to_smtlib tbl = Printf.sprintf "%s.apply()" tbl.name

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
    let (f, actions) = List.fold t.actions  ~init:(None, [])
      ~f:(fun (f, acts) (vars, action) ->
          let f1, rev_action =
            List.fold action ~init:(f0, []) ~f:(fun (f, action) a ->
                let (f, a) = Action.const_prop f a in
                (f, a::action)
              ) in
          let action = List.rev rev_action in
          match f with
          | None -> (Some f1, [(vars, action)])
          | Some f ->
            (Some (Facts.merge f f1), acts@[vars, action])
        )
    in
    (Option.value_exn f, {t with actions})

  let dead_code_elim reads t : (Var.Set.t * t) option =
    let dead_code_elim_action reads body =
      List.fold (List.rev body)
        ~init:(reads, [])
        ~f:(fun (reads, acts) act_stmt ->
            match Action.dead_code_elim reads act_stmt with
            | None ->
              (reads, acts)
            | Some (reads, a) ->
              (reads, a::acts)
          )
    in
    let (reads, actions) =
      List.fold t.actions ~init:None ~f:(fun acc_opt (params, body) ->
          let (reads, body) = dead_code_elim_action reads body in
          let reads = Var.Set.diff reads (Var.Set.of_list params) in
          match acc_opt with
          | None -> Some (reads, [(params, body)])
          | Some (reads_acc, acts_acc) ->
            Some (Var.Set.union reads_acc reads, acts_acc @ [(params, body)]))
      |> Option.value_exn ~message:"Table had no actions"
    in
    Some (reads, {t with actions})
end

module Pipeline = struct
  module P = struct
    type t =
      | Active of Active.t
      | Table of Table.t
    [@@deriving quickcheck, eq, hash, sexp, compare]

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
        let f, a = Active.const_prop f a in
        (f, Active a)
      | Table t ->
        let f, t= Table.const_prop f t in
        (f, Table t)

    let dead_code_elim reads = function
      | Active a ->
        let%map reads, a = Active.dead_code_elim reads a in
        (reads, Active a)
      | Table t ->
        let%map reads, t = Table.dead_code_elim reads t in
        (reads, Table t)

  end

  module Map = Map.Make (P)
  module Set = Set.Make (P)
  include P
end