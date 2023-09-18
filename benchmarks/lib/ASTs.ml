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


  (* let path_simplify_assumes (gcl : t) : t = *)
  (*   let rec listify = function *)
  (*     | Prim p -> [p] *)
  (*     | Seq cs -> List.bind cs ~f:listify *)
  (*     | Choice _ -> failwith "[listify failed] got a choice => not a path" *)
  (*   in *)
    (* let rec heuristic_elim info_flow_state (prims : Active.t list) = *)
    (*   (\* info_flow_state maintains all variables that flow to the key *\) *)
    (*   match prims with *)
    (*   | (Assign(x,e))::prims -> *)
    (*     let evars = Expr.vars e |> Util.uncurry (@) in *)
    (*     let flow_to_x = *)
    (*       List.bind evars ~f:(fun y -> *)
    (*           Var.Map.find info_flow_state y *)
    (*           |> Option.value ~default:[]) *)
    (*     in *)
    (*     let info_flow_state = Var.Map.set info_flow_state ~key:x ~data:flow_to_x in *)
    (*     assign x e :: heuristic_elim info_flow_state prims *)
    (*   | (Passive (Assume phi)) :: prims -> *)
    (*     begin match BExpr.get_equality phi with *)
    (*     | Some (x, e) -> *)
    (*       let phi_vars = BExpr.vars phi in *)
    (*       (\* if everything that contributes to the value of e is a constant or a control var, keep it. *\) *)
    (*       (\* that doesnt quite work the way that I would like either *\) *)

    (*     end *)
    (*     | (Passive (Assert phi)) :: prims -> *)
    (*       assert_ phi :: heuristic_elim info_flow_state prims *)
    (* in *)
    (* listify gcl *)
    (* |> heuristic_elim Var.Map.empty *)

  let single_assert_nf c : t list =
    (* convert the program into single-assert normal form, that is, *)
    (* a list of programs where each program has exactly one assert, the last one *)
    let rec assumeize c =
      match c with
      | Prim (Passive (Assert phi)) ->
        assume phi
      | Prim _ -> c
      | Seq [] -> c
      | Seq (c::cs) ->
        seq (assumeize c) (assumeize (Seq cs))
      | Choice _ ->
        failwith "assumize requires paths only"
    in
    let conjoin = seq in
    let disjoin = (@) in
    let rec assertize c =
      match c with
      | Prim (Passive (Assert phi)) ->
        [assert_ phi]
      | Prim _ -> []
      | Seq [] -> [Seq []]
      | Seq (c::cs) ->
        let cs' =
          let open List.Let_syntax in
          let%map c' = assertize (Seq cs) in
          conjoin (assumeize c) c'
        in
        disjoin (assertize c) cs'
      | Choice _ ->
        failwith "assertize requires paths only"
    in
    assertize c


  let simplify_path (gcl : t) : t =
    let of_map ctx x =
      match Var.Map.find ctx x with
      | Some (v, sz) ->
        Expr.bv v sz
      | None ->
        Expr.var x
    in
    let rec dead_code_elim_inner (reads : Var.Set.t) gcl =
      match gcl with
      | Prim (Assign (x,e)) ->
        let vars = Expr.vars e |> Util.uncurry (@) in
        if Var.Set.mem reads x then
          let reads = Var.Set.remove reads x in
          let reads = Var.Set.(union reads (of_list vars)) in
          reads, gcl
        else
          reads, skip
      | Prim (Passive (Assert phi)) ->
        let vars = BExpr.vars phi |> Util.uncurry (@) in
        Var.Set.(union reads @@ of_list vars),
        assert_ phi
      | Prim (Passive (Assume phi)) ->
        let vars = BExpr.vars phi |> Util.uncurry (@) in
        Var.Set.(union reads @@ of_list vars),
        assume phi
      | Choice _ ->
        failwith "choices cannot occur in paths"
      | Seq cs ->
        match List.rev cs with
        | [] -> (reads, skip)
        | (last :: rest) ->
          let reads, last = dead_code_elim_inner reads last in
          let rest = List.rev rest in
          let reads, rest = dead_code_elim_inner reads @@ sequence rest in
          (reads, seq rest last)
    in
    let const_prop_form ctor ctx phi =
      let phi' = BExpr.fun_subst (of_map ctx) phi in
      match BExpr.get_equality phi' with
        | Some (x, e) ->
          begin match Expr.get_const e with
            | Some v->
              let sz = Var.size x in
              let ctx = Var.Map.set ctx ~key:x ~data:(v,sz) in
              (ctx, ctor phi')
            | None ->
              (ctx, ctor phi')
          end
        | None ->
          (ctx, ctor phi')
    in
    let rec const_prop_inner (ctx : (Bigint.t * int) Var.Map.t) gcl : (Bigint.t * int) Var.Map.t * t =
      match gcl with
      | Prim (Assign (x,e)) ->
        begin match Expr.eval (Model.of_map ctx) e with
          | Result.Error _ ->
            (ctx, assign x e)
          | Result.Ok (v,sz) ->
            let ctx = Var.Map.set ctx ~key:x ~data:(v,sz) in
            (ctx, assign x @@ Expr.bv v sz)
        end
      | Prim (Passive (Assert phi)) ->
        const_prop_form assert_ ctx phi
      | Prim (Passive (Assume phi)) ->
        const_prop_form assume ctx phi
      | Seq [] ->
        (ctx, skip)
      | Seq (c::cs) ->
        let ctx, c = const_prop_inner ctx c in
        let ctx, cs = const_prop_inner ctx @@ sequence cs in
        (ctx, seq c cs)
      | Choice _ ->
        failwith "choices disallowed in const prop"
    in
    let _, gcl' = const_prop_inner Var.Map.empty gcl in
    let _ , gcl'' = dead_code_elim_inner Var.Set.empty gcl' in
    gcl''
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
      |> BExpr.ors_


  let rec wrong (c : t) : BExpr.t =
    let open Passive in
    let open BExpr in
    match c with
    | Prim (Assert b) -> not_ b
    | Prim (Assume _) -> false_
    | Seq cs ->
      List.fold_right cs ~init:false_
        ~f:(fun a wrong_b ->
            let wrong_a = wrong a in
            ors_ [wrong_a; and_ (normal a) wrong_b])
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

    module type CanAssert = sig
      type t
      val assert_ : BExpr.t -> t
    end

    module Asserter(Prim : CanAssert) = struct
      open BExpr
      open Expr
      let from_vars (xs : Var.t list) : Prim.t list =
        List.bind xs ~f:(fun x ->
            match Var.header x with
            | Some (hdr, _) ->
              [Prim.assert_ @@ eq_ (bvi 1 1) @@ var @@ Var.isValid hdr ]
            | None -> []
          )
    end

    let assert_valids_action (data, act_cmds) : (Var.t list * Action.t list) =
      let module AAsserter = Asserter(Action) in
      let asserts a = Action.vars a
                      |> List.filter ~f:(fun x -> not (List.exists data ~f:(Var.equal x)))
                      |> AAsserter.from_vars in
      (data, List.bind act_cmds ~f:(fun a -> asserts a @ [a]))

    let rec assert_valids (cmd:t) : t =
      let module PAsserter = Asserter(Pipeline) in
      match cmd with
      | Prim (Table table) ->
        let key_asserts =
          PAsserter.from_vars table.keys
          |> List.map ~f:prim
          |> sequence
        in
        let actions = List.map ~f:assert_valids_action table.actions in
        seq key_asserts (Prim (Table {table with actions}))
      | Prim (Active a) ->
        let asserts =
          PAsserter.from_vars @@ Active.vars a
          |> List.map ~f:prim
          |> sequence
        in
        seq asserts cmd
      | Seq cs ->
        List.map cs ~f:assert_valids |> sequence
      | Choice cxs ->
        List.map cxs ~f:assert_valids |> choices

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
        let value = Expr.eval model e |> Result.ok_or_failwith in
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
  let _, passive_form = Psv.passify c in
  Log.debug "Passive form -----\n%s\n----------" @@ lazy (Psv.to_string passive_form);
  Psv.vc passive_form
