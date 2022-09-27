open Core

module VarSet = Set.Make (Var)
module VarMap = Map.Make (Var)


module type Primitive = sig
  type t [@@deriving quickcheck, eq, sexp, compare]
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val contra : t -> t -> bool
  val to_smtlib : t -> string
  val count_asserts : t -> int
  val size : t -> int
  val subst : Var.t -> Expr.t -> t -> t
  val normalize_names : t -> t
  val comparisons : t -> (Var.t * Expr.t) list option
end

module Passive = struct
  type t =
    | Assume of BExpr.t
    | Assert of BExpr.t
  [@@deriving quickcheck, eq, sexp, compare]

  let assume b = Assume b
  let assert_ b = Assert b

  let contra c1 c2 =
    match c1, c2 with
    | Assert b1, Assert b2 ->
      BExpr.equal b1 (BExpr.not_ b2)
      || BExpr.equal b2 (BExpr.not_ b1)
    | _, _ ->
      false

  let to_smtlib = function
    | Assume b ->
      Printf.sprintf "assume %s\n%!" (BExpr.to_smtlib b)
    | Assert b ->
      Printf.sprintf "assert %s\n%!" (BExpr.to_smtlib b)

  let count_asserts = function
    | Assume _ -> 0
    | Assert _ -> 1

  let size = function
    | Assume b
    | Assert b ->
      1 + BExpr.size b

  let subst x e = function
    | Assume b -> assume (BExpr.subst x e b)
    | Assert b -> assert_ (BExpr.subst x e b)

  let wp t phi = match t with
    | Assume b -> BExpr.imp_ b phi
    | Assert b -> BExpr.and_ b phi

  let normalize_names = function
    | Assert b ->
      assert_ (BExpr.normalize_names b)
    | Assume b ->
      Assume (BExpr.normalize_names b)

  let comparisons = function
    | Assume b -> Some (BExpr.comparisons b)
    | Assert _ -> None

end

module Assign = struct
  type t = Assign of Var.t * Expr.t
  [@@deriving quickcheck, eq, sexp, compare ]
  let to_smtlib = function
    | Assign (x, e) -> Printf.sprintf "%s:=%s" (Var.str x) (Expr.to_smtlib e)

  let assign x e = Assign (x,e)

  let count_asserts (_ : t) = 0

  let size = function
    | Assign (_, e) -> 1 + Expr.size e

  let subst x e = function
    | Assign (y, e') ->
      if Var.(x = y) then
        failwith "tried to substitute an lvalue"
      else
        assign y (Expr.subst x e e')

  let wp a phi = match a with
    | Assign (x,e) -> BExpr.subst x e phi

  let normalize_names = function
    | Assign (x,e) -> assign (Var.normalize_name x) (Expr.normalize_names e)

end

module Active = struct
  type t =
    | Passive of Passive.t
    | Active of Assign.t
  [@@deriving quickcheck, eq, sexp, compare]

  let assume b = Passive (Passive.assume b)
  let assert_ b = Passive (Passive.assert_ b)
  let assign x e = Active (Assign.assign x e)
  let contra a1 a2 =
    match a1, a2 with
    | Passive p1, Passive p2 -> Passive.contra p1 p2
    | _, _ -> false

  let to_smtlib = function
    | Passive p -> Passive.to_smtlib p
    | Active a -> Assign.to_smtlib a

  let count_asserts = function
    | Passive p -> Passive.count_asserts p
    | Active a -> Assign.count_asserts a

  let size = function
    | Passive p -> Passive.size p
    | Active a -> Assign.size a

  (* let vars = function *)
  (*   | Passive p -> Passive.vars p *)
  (*   | Active a -> Assign.vars a *)

  let subst x e = function
    | Passive p -> Passive (Passive.subst x e p)
    | Active a -> Active (Assign.subst x e a)

  let wp active phi = match active with
    | Passive p -> Passive.wp p phi
    | Active p -> Assign.wp p phi

  let normalize_names = function
    | Passive p -> Passive (Passive.normalize_names p)
    | Active a -> Active (Assign.normalize_names a)

  let comparisons = function
    | Passive p -> Passive.comparisons p
    | Active _ -> None

  
end

module Table = struct
  type t =
    | Active of Active.t
    | Table of {name: string; keys: Var.t list; actions: (Var.t list * Assign.t list) list }
  [@@deriving quickcheck, eq, sexp, compare]

  let to_smtlib = function
    | Active a -> Active.to_smtlib a
    | Table t -> Printf.sprintf "%s.apply()" t.name

  let count_asserts = function
    | Active a -> Active.count_asserts a
    | Table _ -> 0


  let size = function
    | Active a -> Active.size a
    | Table t ->
      1 + List.length t.keys +
      List.sum (module Int) t.actions ~f:(fun (_, prims) ->
         List.sum (module Int) prims ~f:(fun p -> Assign.size p))

  let subst x e = function
    | Active a -> Active (Active.subst x e a)
    | Table t ->
      if List.exists t.keys ~f:(Var.equal x) then
        failwithf "Cannot substitute variable %s, its a key in table %s" (Var.str x) t.name ()
      else
        let open List.Let_syntax in
        let actions =
          let%map (args, body) = t.actions in
          if List.exists args ~f:(Var.equal x) then
            (args, body)
          else
            let body = List.map body ~f:(Assign.subst x e) in
            (args, body)
        in
        Table {t with actions}

  let normalize_names = function
    | Active a -> Active (Active.normalize_names a)
    | Table t ->
      let open List.Let_syntax in
      let actions =
        let%map (args, body) = t.actions in
        (List.map ~f:Var.normalize_name args,
         List.map ~f:Assign.normalize_names body )
      in
      let keys = List.map t.keys ~f:(Var.normalize_name)in
      Table {t with keys; actions }

  let contra c1 c2 = match c1, c2 with
    | Active a1, Active a2 ->
      Active.contra a1 a2
    | _, _ -> false

  let comparisons = function
    | Table _ -> None
    | Active a -> Active.comparisons a
  let assume b = Active (Active.assume b)
  let assert_ b = Active (Active.assert_ b )
end

module Make (P : Primitive) = struct

  type t =
    | Prim of P.t
    | Seq of t list
    | Choice of t list
  [@@deriving quickcheck, eq, sexp, compare]

  let assume phi = Prim (P.assume phi)
  let assert_ phi = Prim (P.assert_ phi)
  let skip = Prim (P.assume BExpr.true_)
  let pass = Prim (P.assert_ BExpr.true_)
  let dead = Prim (P.assume BExpr.false_)
  let abort = Prim (P.assert_ BExpr.false_)

  let is_mult_unit p = equal skip p || equal pass p
  let is_mult_annihil p = equal dead p || equal abort p

  let is_add_unit p = equal dead p
  let is_add_annihil p = equal abort p

  
  let contra c1 c2 = match c1, c2 with
    | Prim p1, Prim p2 -> P.contra p1 p2
    | _, _ -> false

  let rec to_string_aux indent (c : t) : string =
    let open Printf in
    let space = Util.space indent in
    match c with
    | Prim p ->
      sprintf "%s %s" space (P.to_smtlib p)
    | Seq cs ->
      List.map cs ~f:(to_string_aux indent)
      |> String.concat ~sep:(sprintf ";\n")
    | Choice cs ->
      List.map cs
        ~f:(fun c ->
            sprintf "{\n%s\n%s}" (to_string_aux (indent+2) c) space)
      |> String.concat ~sep:(sprintf " [] ")
      |> Printf.sprintf "%s%s" space

  let to_string = to_string_aux 0

  let rec count_asserts_aux c n =
    match c with
    | Prim p ->
      n + P.count_asserts p
    | Seq cs
    | Choice cs ->
      List.fold cs ~init:n ~f:(fun n c ->
          count_asserts_aux c n
        )

  let count_asserts c = count_asserts_aux c 0

  let rec size = function
    | Prim p -> P.size p
    | Seq cs
    | Choice cs ->
      List.fold cs ~init:(List.length cs - 1)
        ~f:(fun n c -> n + size c)


  let sequence cs =
    let cs = List.filter cs ~f:(Fn.non is_mult_unit) in
    let cs = List.remove_consecutive_duplicates cs ~which_to_keep:`First ~equal in
    match List.find cs ~f:is_mult_annihil with
    | Some p -> p
    | None ->
      if List.exists2_exn cs cs ~f:(contra) then
        abort
      else
        match cs with
        | [] -> skip
        | [c] -> c
        | _ -> Seq cs

  let seq c1 c2 =
    match c1, c2 with
    | Seq c1s, Seq c2s ->
      c2s
      |> List.rev_append @@ List.rev c1s
      |> sequence
    | Seq c1s, _ ->
      List.rev c1s
      |> List.cons c2
      |> List.rev
      |> sequence
    | _, Seq c2s ->
      c1 :: c2s
      |> sequence
    | _, _ ->
      sequence [c1; c2]

  let rec trivial_branch_comparisons cs (comps : Expr.t list VarMap.t) =
    let open Option.Let_syntax in
    match cs with
    | [] -> Some comps
    | Prim p::cs ->
      let%bind comps' = P.comparisons p in
      List.fold comps' ~init:comps
        ~f:(fun acc (key,data) -> VarMap.add_multi acc ~key ~data)
      |> trivial_branch_comparisons cs
    | _ ->
      None

  let can_collapse_total_trivial_branch cs =
    match trivial_branch_comparisons cs VarMap.empty with
    | None -> false
    | Some comps ->
      List.length (VarMap.keys comps) = 1
      && VarMap.for_alli comps ~f:(fun ~key ~data ->
          String.is_suffix (Var.str key) ~suffix:"$action"
          && List.for_all data ~f:(fun e -> Option.is_some (Expr.get_const e)))

  let choices cs : t =
    if List.is_empty cs then
      failwith "[Cmd.choices] cannot construct 0-ary choice"
    else
      let cs = List.filter cs ~f:(Fn.non is_add_unit) in
      if List.is_empty cs then
        (* all paths are dead *)
        dead
      else if List.exists cs ~f:(is_add_annihil) then
        abort
      else if can_collapse_total_trivial_branch cs then
        skip
      else
        begin
          match List.dedup_and_sort cs ~compare with
          | [c] -> c
          | cs -> Choice cs
        end

  let choice c1 c2 =
    match c1, c2 with
    | Choice c1s, Choice c2s ->
      choices (List.rev_append c1s c2s)
    | Choice c1s, _ ->
      choices (c1s @ [c2])
    | _, Choice c2s ->
      choices (c1 :: c2s)
    | _, _ ->
      choices [c1;c2]

  (* let negate = function *)
  (*   | Assume t -> assume (BExpr.not_ t) *)
  (*   | Assert t -> assert_ (BExpr.not_ t) *)
  (*   | _ -> failwith "Can only negate an assumption or assertion" *)

  let choice_seq cs1 cs2 = choice (sequence cs1) (sequence cs2)

  let choice_seqs cs = List.map cs ~f:sequence |> choices

  (**/ END Smart Constructors*)

  let is_primitive (c : t) =
    match c with
    | Prim _ -> true
    | _ -> false

  (* PRE: x is not an lvalue in c *)
  let rec subst x e c =
    match c with
    | Prim p -> Prim (P.subst x e p)
    | Seq cs ->
      List.map cs ~f:(subst x e) |> sequence
    | Choice cs ->
      List.map cs ~f:(subst x e) |> choices

  (* let match_key (id : string) k = *)
  (*   let open BExpr in *)
  (*   let open Expr in *)
  (*   let v = Var.make_symbRow_str id k in *)
  (*   eq_ (var v) (var k) *)

  (* let matchrow (id : string) ks = *)
  (*   let open BExpr in *)
  (*   List.fold ks ~init:true_ *)
  (*     ~f:(fun acc k -> match_key id k |> and_ acc) *)

  (* let assign_key (id : string) k = *)
  (*   let open Expr in *)
  (*   let v = Var.make_symbRow_str id k in *)
  (*   assign k (var v) *)

  (* let assignrow id ks = *)
  (*   List.map ks ~f:(assign_key id) *)
  (*   |> sequence *)

  (* let row_action (tid : string) act_id n = *)
  (*   let open Expr in *)
  (*   let v = Var.make_symbRow_str tid (Var.make "action" n) in *)
  (*   BExpr.eq_ (var v) (bv (Bigint.of_int act_id) n) *)

  (* let action_subst (tid : string) (x_opt, c) = *)
  (*   match x_opt with *)
  (*   | None -> *)
  (*     c *)
  (*   | Some x -> *)
  (*     let r_data = Var.make_symbRow_str tid x in *)
  (*     subst x (Expr.var r_data) c *)

  (* (\** [mint_keyvar t i w] is a Var.t of width [w] corresponding to the [i]th key *)
  (*     in table [t]*\) *)
  (* let mint_keyvar t i w = *)
  (*   let name = Printf.sprintf "_%s_key_$%d" t i in *)
  (*   Var.make name w *)

  (* let rec mint_key_names_aux idx assignments varkeys tbl_name ks = *)
  (*   match ks with *)
  (*   | [] -> (assignments, varkeys) *)
  (*   | (kwidth, kexpr)::ks' -> *)
  (*     (\* mint key *\) *)
  (*     let v = mint_keyvar tbl_name idx kwidth in *)
  (*     (\* update recursive state *\) *)
  (*     let idx' = idx + 1 in *)
  (*     let assignments' = assign v kexpr :: assignments in *)
  (*     let varkeys' = v :: varkeys in *)
  (*     (\* make recusive call with updated state *\) *)
  (*     mint_key_names_aux idx' assignments' varkeys' tbl_name ks' *)

  (* (\** [mint_key_names tbl_name keys] is a pair of lists [(as,vs)] where [vs] is the set of variable keys and [as] is the list of assignments copying [keys] to [vs] *\) *)
  (* let mint_key_names = mint_key_names_aux 0 [] [] *)

  (* (\* a lightweight table encoding scheme used for benchmarking *\) *)
  (* let table (id_int : int) (ks : Var.t list) (acts : (Var.t option * t) list) : t = *)
  (*   let id = Printf.sprintf "%d" id_int in *)
  (*   let read_keys = matchrow id ks in *)
  (*   let assign_keys = assignrow id ks in *)
  (*   let hit act_id act = *)
  (*     [Assume (row_action id act_id (List.length acts)); *)
  (*      action_subst id act ] *)
  (*   in *)
  (*   let actions = List.foldi acts ~init:[] ~f:(fun i acc act -> (hit i act)::acc) in *)
  (*   [Assume read_keys; *)
  (*    if false then assign_keys else skip; *)
  (*    choice_seqs actions] *)
  (*   |> sequence *)

  (* (\* a full table encoding scheme for interfacing with p4*\) *)
  (* let full_table (tbl_name : string) (ks : (int * Expr.t) list) (acts : (string * t) list) : t = *)
  (*   let (asgns, varkeys) = mint_key_names tbl_name ks in *)
  (*   let read_keys = matchrow tbl_name varkeys in *)
  (*   let hit act_id act = *)
  (*     [assume (row_action tbl_name act_id (List.length acts)); *)
  (*      act ] *)
  (*   in *)
  (*   let actions = List.foldi acts ~init:[] ~f:(fun i acc (_,act) -> (hit i act)::acc) in *)
  (*   let table = [Assume read_keys; choice_seqs actions] in *)
  (*   (\* TODO optimization. Rather than sequencing asgns, do the substitution! *\) *)
  (*   sequence (asgns @ table) *)

  let rec normalize_names (c : t) : t =
    match c with
    | Prim p -> Prim (P.normalize_names p)
    | Seq cs ->
      List.map cs ~f:normalize_names |> sequence
    | Choice cs ->
      List.map cs ~f:normalize_names
      |> choices

  let dnf (c : t) : t =
    Log.print @@ lazy "DNFing cmd";
    let rec loop c : t =
      match c with
      | Prim p -> Prim p
      | Choice chxs ->
        List.fold chxs ~init:dead ~f:(fun acc c -> choice acc (loop c))
      | Seq [] -> skip
      | Seq (s::sqs) -> begin
          match loop s, loop (sequence sqs) with
          | Choice chxs, Choice chxs_rec ->
            List.cartesian_product chxs chxs_rec
            |> List.map ~f:(Util.uncurry seq)
            |> choices
          | Choice chxs, c_rec ->
            List.map chxs ~f:(fun chx -> seq chx c_rec)
            |> choices
          | c, Choice chxs_rec ->
            List.map chxs_rec ~f:(fun chx_rec -> seq c chx_rec)
            |> choices
          | c, c_rec ->
            seq c c_rec
        end
    in
    loop c

  let rec count_paths c : Bigint.t =
    match c with
    | Prim _ ->
      Bigint.one
    | Seq cs ->
      List.fold cs ~init:Bigint.one
        ~f:(fun paths_so_far c -> Bigint.(paths_so_far * count_paths c))
    | Choice cs ->
      List.map cs ~f:(count_paths)
      |> List.reduce_exn ~f:(Bigint.(+))

  let paths (c : t) : t Sequence.t =
    Log.print @@ lazy (Printf.sprintf "building the squence of %s paths" (count_paths c |> Bigint.to_string));
    let rec loop (c : t) : t Sequence.t =
      let open Sequence in
      match c with
      | Prim _ ->
        return c
      | Seq cs ->
        of_list cs
        |> fold ~init:(Sequence.singleton skip)
          ~f:(fun sequence_of_paths c ->
              loop c
              |> cartesian_product sequence_of_paths
              |> map ~f:(fun (s1,s2) -> seq s1 s2))
      | Choice cs ->
        of_list cs
        |> map ~f:loop
        |> concat
    in
    loop c

end

module GPL = Make (Table)
module GCL = struct
  include Make (Active)

  let assign x e = Prim (Active.assign x e)

  let rec wp c phi =
    let open BExpr in
    match c with
    | Prim a -> Active.wp a phi
    | Seq cs -> List.fold_right cs ~init:phi ~f:wp
    | Choice cs -> ands_ (List.map cs ~f:(fun c -> wp c phi))

  let rec const_prop_aux (f : Facts.t) (c : t) =
    match c with
    | Prim (Active (Assign (x,e))) ->
      let e = Expr.fun_subst (Facts.lookup f) e in
      let f = Facts.update f x e in
      (* Log.print @@ lazy (Printf.sprintf "assignment %s produced: %s\n" (to_string c) (Facts.to_string f));      *)
      (f, assign x e)
    | Prim (Passive (Assert b)) ->
      (* Log.print @@ lazy (Printf.sprintf "substitute %s using: %s\n" (to_string c) (Facts.to_string f)); *)
      let b = BExpr.fun_subst (Facts.lookup f) b |> BExpr.simplify in
      let f =
        match BExpr.get_equality b with
        | Some (x, e) -> Facts.update f x e
        | None -> f
      in
      (* Log.print @@ lazy (Printf.sprintf "Got assert(%s)\n" (BExpr.to_smtlib b)); *)
      (f, assert_ b)
    | Prim (Passive (Assume b)) ->
      (* Log.print @@ lazy (Printf.sprintf "substitute %s using: %s\n" (to_string c) (Facts.to_string f));      *)
      let b = BExpr.fun_subst (Facts.lookup f) b |> BExpr.simplify in
      (* Log.print @@ lazy (Printf.sprintf "Got assume(%s)\n" (BExpr.to_smtlib b)); *)
      let f =
        match BExpr.get_equality b with
        | Some (x, e) -> Facts.update f x e
        | None -> f
      in
      (f, assume b)

    | Seq cs ->
      let fs, cs =
        List.fold cs ~init:(f, [])
          ~f:(fun (f, cs) c ->
              let f, c = const_prop_aux f c in
              (f, cs @ [c])) in
      (fs, sequence cs)
    | Choice [] ->
      failwith "Choice of no alternatives"
    | Choice (c::cs) ->
      List.fold cs
        ~init:(const_prop_aux f c)
        ~f:(fun (fs, cs) c1 ->
            let f1, c1 = const_prop_aux f c1 in
            let fs = Facts.merge fs f1 in
            (fs , choice c1 cs))

  let const_prop c = snd (const_prop_aux Facts.empty c)

  let rec dead_code_elim_bwd c (reads : VarSet.t) : (t * VarSet.t) =
    let open VarSet in
    let concat (x,y) = x @ y in
    match c with
    | Prim (Active (Assign (x, e))) ->
      if exists reads ~f:(Var.(=) x) then
        let read_by_e = of_list (concat (Expr.vars e)) in
        let reads_minus_x = remove reads x in
        let reads = union read_by_e reads_minus_x in
        (assign x e, reads)
      else
        (skip, reads)
    | Prim (Passive (Assert b)) ->
      let read_by_b = of_list (concat (BExpr.vars b)) in
      let simpl_b = BExpr.simplify b in
      (assert_ simpl_b, union reads read_by_b)
    | Prim (Passive (Assume b)) ->
      let read_by_b = of_list (concat (BExpr.vars b)) in
      let simpl_b = BExpr.simplify b in
      (assume simpl_b, union reads read_by_b)
    | Choice [] ->
      failwith "cannot have 0-ary choice"
    | Choice (c::cs) ->
      List.fold cs
        ~init:(dead_code_elim_bwd c reads)
        ~f:(fun (cs, read_by_cs) c ->
            let c, read_by_c = dead_code_elim_bwd c reads in
            (choice cs c, union read_by_cs read_by_c))
    | Seq cs ->
      let cs, reads =
        List.fold (List.rev cs) ~init:([], reads)
          ~f:(fun (cs, reads) c ->
              let c, reads = dead_code_elim_bwd c reads in
              (c::cs, reads)) in
      sequence cs, reads

  let rec dead_code_elim_fwd c (used : VarSet.t) : (t * VarSet.t) =
    let open VarSet in
    let concat (x,y) = x @ y in
    let setify f e = f e |> concat |> of_list in
    match c with
    | (Prim (Active (Assign (x,e)))) ->
      let vars_of_e = setify Expr.vars e in
      (assign x e, union (add used x) vars_of_e)
    | (Prim (Passive (Assert b))) -> (assert_ b, union used (setify BExpr.vars b))
    | (Prim (Passive (Assume b))) ->
      let bs_vars = setify BExpr.vars b in
      if is_empty (inter bs_vars used)
      && VarSet.for_all bs_vars ~f:(Fn.non Var.is_symbRow) then
        (skip, used)
      else
        (assume b, union bs_vars used)
    | Choice [] ->
      failwith "cannot have 0-ary choice"
    | Choice (c::cs) ->
      List.fold cs
        ~init:(dead_code_elim_fwd c used)
        ~f:(fun (cs, used_by_cs) c ->
            let c, used_by_c = dead_code_elim_fwd c used in
            (choice cs c, union used_by_cs used_by_c))
    | Seq cs ->
      let rcs, used =
        List.fold cs ~init:([], used)
          ~f:(fun (cs, used) c ->
              let c, used = dead_code_elim_fwd c used in
              (c::cs, used))
      in
      (List.rev rcs |> sequence, used)

  let dead_code_elim_inner c =
    let c, _ = dead_code_elim_bwd c VarSet.empty in
    let c, _ = dead_code_elim_fwd c VarSet.empty in
    c

  let rec fix f x =
    let x' = f x in
    if equal x' x then
      x
    else
      fix f x'

  let dead_code_elim = fix dead_code_elim_inner

  let optimize c =
    let o c = dead_code_elim (const_prop (dead_code_elim (const_prop c))) in
    fix o c

  let vc (c : t) : BExpr.t =
    let o = optimize c in
    wp o BExpr.true_
end
module PassiveGCL = struct
  include Make (Passive)

  let rec normal (c : t) : BExpr.t =
    let open BExpr in
    match c with
    | Prim (Assert b) -> b
    | Prim (Assume b) -> b
    | Seq cs ->
      List.map cs ~f:normal |> ands_
    | Choice cs ->
      List.map cs ~f:normal |> ors_

  let rec wrong (c : t) : BExpr.t =
    let open BExpr in
    match c with
    | Prim (Assert b) -> not_ b
    | Prim (Assume _) -> false_
    | Seq [] -> false_
    | Seq (c1::cs) ->
      let c2 = sequence cs in
      let w1 = wrong c1 in
      let w2 = and_ (normal c1) (wrong c2) in
      or_ w1 w2
    | Choice cs ->
      List.map cs ~f:wrong |> ors_

  let rec update_resid x curr tgt resid =
    if curr >= tgt then
      resid
    else
      let x_ i = Expr.var (Var.index x i) in
      BExpr.(and_ resid (eq_ (x_ curr) (x_ (curr+1))))
      |> update_resid x (curr + 1) tgt

  let passify (c : GCL.t) : t =
    Log.print @@ lazy "Passifying";
    let rec loop (ctx : Context.t) (c : GCL.t) : Context.t * t =
      match c with
      | Prim (Active (Assign (x,e))) ->
        let ctx = Context.increment ctx x in
        let x' = Context.label ctx x in
        let e' = Expr.label ctx e in
        (ctx, assume (BExpr.eq_ (Expr.var x') e'))
      | Prim (Passive (Assert b)) ->
        (ctx, assert_ (BExpr.label ctx b))
      | Prim (Passive (Assume b)) ->
        (ctx, assume (BExpr.label ctx b))
      | Seq cs ->
        List.fold cs ~init:(ctx, skip)
          ~f:(fun (ctx, c_acc) c ->
              let ctx, c = loop ctx c in
              (ctx, seq c_acc c))
      | Choice ([]) ->
        failwith "[passify] 0-ary choice undefined"
      | Choice (c::cs) ->
        List.fold cs ~init:(loop ctx c)
          ~f:(fun (ctx_acc, c_acc) c ->
              let ctx, c = loop ctx c in
              let ctx, resid_acc, resid =
                Context.merge ctx_acc ctx ~init:(BExpr.true_) ~update:update_resid
              in
              let rc_acc = seq c_acc (assume resid_acc) in
              let rc = seq c (assume resid) in
              (ctx, choice rc_acc rc))
    in
    snd (loop Context.empty c)

  let assume_disjunct ?(threshold=1000) cs =
    let c = choices cs in
    if List.exists cs ~f:(fun x -> size x >= threshold) then
      c
    else
      assume (normal c)

  let assume_disjuncts c =
    Log.print @@ lazy "assuming disjuncts";
    let rec loop c =
      match c with
      | Prim (Assume phi) -> assume phi
      | Prim (Assert phi) -> assert_ phi
      | Seq cs ->    List.map cs ~f:loop |> sequence
      | Choice cs -> List.map cs ~f:loop |> assume_disjunct
    in
    loop c

  let vc (c : t) : BExpr.t =
    wrong c
    |> BExpr.not_
    |> BExpr.simplify

end

let vc (c : GCL.t) : BExpr.t =
  let open PassiveGCL in
  vc (passify c)
