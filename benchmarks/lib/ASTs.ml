open Core
open Primitives

module GCL = struct
  module Pack = struct
    include Cmd.Make (Active)

    let assign x e = prim (Active.assign x e)

    let table (tbl_name, keys, (actions : (Var.t list * Action.t list) list)) =
      let table =
        Pipeline.table tbl_name keys actions
        |> Pipeline.explode
        |> Util.mapmap ~f:(fun a -> prim (Pipeline.to_active_exn a))
        |> choice_seqs
      in
      table

    let ite b c1 c2 =
      choice
        (seq (assume b) c1)
        (seq (assume (BExpr.not_ b)) c2)

    let rec wp cmd phi =
      match cmd with
      | Prim (Passive (Assume psi)) ->
        BExpr.imp_ psi phi
      | Prim (Passive (Assert psi)) ->
        BExpr.and_ psi phi
      | Prim (Assign (x,e)) ->
        BExpr.subst x e phi
      | Seq cs ->
        List.fold_right cs
          ~init:phi
          ~f:wp
      | Choice cs ->
        List.map cs ~f:(fun cmd -> wp cmd phi)
        |> BExpr.ands_
  end

  module CP = Transform.ConstProp (struct
      module P = Active
      include Pack
      let prim_const_prop m p =
        Log.debug "\tSTART:%s" @@ lazy (Active.to_smtlib p);
        let p,m = Active.const_prop m p in
        Log.debug "\t  END:%s" @@ lazy (Active.to_smtlib p);
        p,m
    end)
  let const_prop = CP.propagate_exn
  
  module O = Transform.Optimizer (struct
      module P = Active
      include Pack
      let prim_dead_code_elim p reads =
        let open Option.Let_syntax in
        Log.compiler "\tSTART:%s" @@ lazy (Active.to_smtlib p);
        let%map reads, p = Active.dead_code_elim p reads in
        Log.compiler "\t  END:%s" @@ lazy (Active.to_smtlib p);
        reads, p

      let prim_const_prop m p =
        Log.debug "\tSTART:%s" @@ lazy (Active.to_smtlib p);
        let p,m = Active.const_prop m p in
        Log.debug "\t  END:%s" @@ lazy (Active.to_smtlib p);
        Active.const_prop m p
    end
    )

  module N = Transform.Normalize ( struct
      module P = Active
      include Pack
      let normalize_prim = P.normalize_names
    end)

  let optimize = O.optimize
  let normalize_names = N.normalize

  include Pack

end

module Psv = struct
  include Cmd.Make (Passive)

  let rec normal (c : t) : BExpr.t =
    let open Passive in
    match c with
    | Prim (Assert phi)
    | Prim (Assume phi) ->
      phi
    | Seq cs ->
      List.map cs ~f:normal
      |> BExpr.ands_
    | Choice cs ->
      List.map cs ~f:normal
      |> BExpr.ands_


  let rec wrong (c : t) : BExpr.t =
    let open Passive in
    let open BExpr in
    match c with
    | Prim (Assert b) -> not_ b
    | Prim (Assume _) -> false_
    | Seq cs ->
      List.fold_right cs ~init:false_
        ~f:(fun c acc ->
            let w1 = wrong c in
            let w2 = and_ (normal c) acc in
            or_ w1 w2
        )
    | Choice cs ->
      List.map cs ~f:(wrong) |> ors_

  let rec update_resid x curr tgt resid =
    if curr >= tgt then
      resid
    else
      let x_ i = Expr.var (Var.index x i) in
      BExpr.(and_ resid (eq_ (x_ curr) (x_ Int.(curr+1))))
      |> update_resid x Int.(curr + 1) tgt

  let passify (c : GCL.t) : Context.t * t =
    let rec passify_rec ctx c =
    match c with
    | GCL.Prim (Assign (x,e)) ->
      let e' = Expr.label ctx e in
      let ctx = Context.increment ctx x in
      let x' = Context.label ctx x in
      (ctx, assume (BExpr.eq_ (Expr.var x') e'))

    | GCL.Prim (Passive (Assert b)) ->
      (ctx, assert_ (BExpr.label ctx b))
    | GCL.Prim (Passive (Assume b)) ->
      (ctx, assume (BExpr.label ctx b))
    | Seq cs ->
      List.fold cs ~init:(ctx, skip)
        ~f:(fun (ctx, prec) cmd ->
            let ctx, psv = passify_rec ctx cmd in
            (ctx, seq prec psv)
          )
    | Choice cs ->
      List.map cs ~f:(passify_rec ctx)
      |> Util.fold_right1
        ~init:Fn.id
        ~f:(fun (ctx_acc, c_acc) (ctx, c) ->
            let ctx, resid_acc, resid =
              Context.merge ctx_acc ctx ~init:(BExpr.true_) ~update:update_resid
            in
            let rc_acc = seq c_acc (assume resid_acc) in
            let rc = seq c (assume resid) in
            (ctx, choice rc_acc rc))
    in
    passify_rec Context.empty c

  let vc (c : t) : BExpr.t =
    let phi = wrong c in
    Log.debug "wrong_execs: %s" @@ lazy (BExpr.to_smtlib phi);
    BExpr.not_ phi
    (* |> BExpr.simplify *)

  let rec remove_asserts (c : t) =
    match c with
    | Prim (Assert _) -> skip
    | Prim _ -> c
    | Seq cs ->
      List.map cs ~f:remove_asserts
      |> sequence
    | Choice cs ->
      List.map cs ~f:remove_asserts
      |> choices
end

 module GPL = struct
  module Pack = struct
    include Cmd.Make (Pipeline)
    let assign x e = prim (Active (Active.assign x e))
    let table name keys actions =
      prim (Table {name; keys; actions})

    let rec of_gcl (gcl : GCL.t) : t =
      match gcl with
      | GCL.Prim p -> prim (Active p)
      | GCL.Seq cs ->
        List.map cs ~f:of_gcl
        |> sequence
      | GCL.Choice cs ->
        List.map cs ~f:of_gcl
        |> choices

    let rec encode_tables (cmd : t) : GCL.t =
      match cmd with
      | Prim (Table {name;keys;actions}) ->
        GCL.table (name, keys, actions)
      | Prim (Active a) -> GCL.prim a
      | Seq cs -> List.map cs ~f:encode_tables |> GCL.sequence
      | Choice cs -> List.map cs ~f:encode_tables |> GCL.choices

    let wp cmd phi =
      let cmd = encode_tables cmd in
      GCL.wp cmd phi

    let symbolize (c : t) =
      let gcl = encode_tables c in
      let (ctx, psv) = Psv.passify gcl in
      let symbolic_parser = Psv.normal psv in
      let symbolic_parser = BExpr.erase_max_label ctx symbolic_parser in
      assume symbolic_parser

    let tables  (c : t) : Table.t list =
      let rec tables_raw c =
        match c with
        | Prim (Table tbl) -> [tbl]
        | Prim _ -> []
        | Seq cs | Choice cs ->
          List.bind cs ~f:tables_raw
      in
      tables_raw c
      |> List.dedup_and_sort ~compare:Table.compare
  end

  module N = Transform.Normalize (struct
      include Pack
      module P = Pipeline
      let normalize_prim = Pipeline.normalize_names
    end)
  let normalize_names = N.normalize

  module D = Transform.DeadCodeElim(struct
      include Pack
      module P = Pipeline
      let prim_dead_code_elim = Pipeline.dead_code_elim
    end)
  let dead_code_elim = D.elim_with_reads

  module C = Transform.ConstProp(struct
      include Pack
      module P = Pipeline
      let prim_const_prop = Pipeline.const_prop
    end)
  let const_prop = C.propagate_with_map

  module O = Transform.Optimizer (struct
      include Pack
      module P = Pipeline
      let prim_dead_code_elim = Pipeline.dead_code_elim
      let prim_const_prop m p =
        Log.debug "\t%s" @@ lazy (Pipeline.to_smtlib p);
        let p, m = Pipeline.const_prop m p in
        Log.debug "\t%s" @@ lazy (Pipeline.to_smtlib p);
        p, m
      end)
  let optimize = O.optimize
  let optimize_seq_pair = O.optimize_seq_pair
  include Pack
end

module TFG = struct
  module T = struct
    include Pipeline
    let is_node = function
      | Table _ -> true
      | _ -> false
  end
  include Cmd.Make(T)

  let rec project (gpl : GPL.t) : t =
    match gpl with
    | Prim (Pipeline.Active a) -> prim (T.Active a)
    | Prim (Pipeline.Table t) -> prim (T.Table t)
    | Seq cs ->
      List.map cs ~f:project |> sequence
    | Choice cs ->
      List.map cs ~f:project |> choices

  let rec inject (tfg : t) : GPL.t =
    match tfg with
    | Prim p -> GPL.prim p
    | Seq cs ->
      List.map cs ~f:inject |>  GPL.sequence
    | Choice cs ->
      List.map cs ~f:inject |> GPL.choices
end


module Concrete = struct
  open GCL

  let slice (model : Model.t) (cmd : t) : t option =
    let open Option.Let_syntax in
    let rec slice_aux model cmd : (Model.t * t) option =
    match cmd with
    | Prim p ->
      Log.debug "%s" @@ lazy (Active.to_smtlib p);
      begin match p with
      | Assign (x,e) ->
        let value = Expr.eval model e in
        let model = Model.update model x value in
        Some (model, Prim p)
      | (Passive (Assume phi)) when BExpr.eval model phi->
        Some (model, Prim p)
      | (Passive (Assume phi)) ->
        Log.debug "Assume failed %s" @@ lazy (BExpr.to_smtlib phi);
        None
      | Passive (Assert _) ->
        Some (model, Prim p)
      end
    | Seq cs ->
      List.fold cs ~init:(Some (model, skip))
        ~f:(fun acc_opt cmd ->
            let%bind (model, prefix) = acc_opt in
            let%map model, cmd = slice_aux model cmd in
            (model, seq prefix cmd)
          )
    | Choice cxs ->
      match List.filter_map cxs ~f:(slice_aux model) with
      | [cmd_opt] -> Some cmd_opt
      | [] ->
        failwith "Execution Error: impossible infeasible"
      | _ -> failwith "Execution Error: too many choices"
    in
    slice_aux model cmd
    |> Option.map ~f:snd
end

let passive_vc (c : GCL.t) : BExpr.t =
  Psv.passify c
  |> snd
  |> Psv.wrong
  |> BExpr.not_
