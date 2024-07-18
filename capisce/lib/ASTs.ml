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
      | Seq cs ->
        List.fold_right cs
          ~init:phi
          ~f:wp
      | Choice cs ->
        List.map cs ~f:(fun cmd -> wp cmd phi)
        |> BExpr.ands_
      | Prim p ->
        match p.data with
        | Passive (Assume psi) ->
          BExpr.imp_ psi phi
        | Passive (Assert psi) ->
          BExpr.and_ psi phi
        | Assign (x,e) ->
          BExpr.subst x e phi

    let rec all_paths = function 
    | Prim p -> [prim p]
    | Choice cs -> 
      List.bind ~f:all_paths cs
    | Seq cs -> 
      List.fold cs ~init:[skip] ~f:(fun paths c ->
        let open List.Let_syntax in 
        let%bind c_path = all_paths c in 
        let%map acc_path = paths in 
        seq acc_path c_path
      )

  let single_assert_nf c : t list =
    let rec assumeize c =
      match c with
      | Prim {data = Passive (Assert phi); alt = _} ->
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
      | Prim {data = (Passive (Assert phi));_} ->
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
      | Prim {data = Assign (x,e); _} ->
        let vars = Expr.vars e |> Util.uncurry (@) in
        if Var.Set.mem reads x then
          let reads = Var.Set.remove reads x in
          let reads = Var.Set.(union reads (of_list vars)) in
          reads, gcl
        else
          reads, skip
      | Prim {data = Passive (Assert phi); _} ->
        let vars = BExpr.vars phi |> Util.uncurry (@) in
        Var.Set.(union reads @@ of_list vars),
        assert_ phi
      | Prim {data = Passive (Assume phi); _ } ->
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
              if BExpr.(phi = false_) then
                Log.rewrites "[WARNING] got a false assumption %s" @@ lazy BExpr.(to_smtlib phi);
              (ctx, ctor phi')
            | None ->
              (ctx, ctor phi')
          end
        | None ->
          (ctx, ctor phi')
    in
    let rec const_prop_inner (ctx : (Bigint.t * int) Var.Map.t) gcl : (Bigint.t * int) Var.Map.t * t =
      match gcl with
      | Prim {data = Assign (x,e); _} ->
        begin match Expr.eval (Model.of_map ctx) e with
          | Result.Error _ ->
            (Var.Map.remove ctx x, assign x e)
          | Result.Ok (v,sz) ->
            let ctx = Var.Map.set ctx ~key:x ~data:(v,sz) in
            (ctx, assign x @@ Expr.bv v sz)
        end
      | Prim {data = Passive (Assert phi);_} ->
        const_prop_form assert_ ctx phi
      | Prim {data = Passive (Assume phi);_} ->
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
    Log.irs "Before optimization: %s\n%!" @@ lazy (to_string gcl);
    let _, gcl' = const_prop_inner Var.Map.empty gcl in
    Log.irs "After constant propagation: %s\n%!" @@ lazy (to_string gcl');
    let _ , gcl'' = dead_code_elim_inner Var.Set.empty gcl' in
    gcl''
  end

  module CP = Transform.ConstProp (struct
      module P = Active
      include Pack
      let prim_const_prop m p =
        Log.irs "\tSTART:%s" @@ lazy (Active.to_smtlib p);
        let p,m = Active.const_prop m p in
        Log.irs "\t  END:%s" @@ lazy (Active.to_smtlib p);
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
        Log.irs "\tSTART:%s" @@ lazy (Active.to_smtlib p);
        let p,m = Active.const_prop m p in
        Log.irs "\t  END:%s" @@ lazy (Active.to_smtlib p);
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
    | GCL.Prim {data = Assign (x,e);_} ->
      let e' = Expr.label ctx e in
      let ctx = Context.increment ctx x in
      let x' = Context.label ctx x in
      (ctx, assume (BExpr.eq_ (Expr.var x') e'))

    | GCL.Prim {data = Passive (Assert b);_} ->
      (ctx, assert_ (BExpr.label ctx b))
    | GCL.Prim {data = Passive (Assume b);_} ->
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
    Log.smt "wrong_execs: %s" @@ lazy (BExpr.to_smtlib phi);
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
    
    let raw_table name keys actions =
      prim (Table {name; keys; actions})

    let table name (real_keys : (Var.t * Table.kind) list) actions =
      let open BExpr in
      let open Expr in
      let new_keys =
        List.mapi real_keys ~f:(fun i (key, kind) ->
          let new_key = Var.rename key (Printf.sprintf "_symb$%s$match_%d" name i) in
          (new_key, kind)
        )
      in
      let key_assumes =
        List.mapi real_keys ~f:(fun i (key, kind) ->
            match kind with
            | MaskableDegen | Exact ->
              let symb_key = Var.rename key (Printf.sprintf "_symb$%s$match_%d" name i) in
              assume @@ eq_ (var symb_key) (var key)
            | Maskable ->
              let symb_key = Var.rename key (Printf.sprintf "_symb$%s$match_%d" name i) in
              let symb_key_dc = Var.make (Printf.sprintf "_symb$%s$match_%d$DONT_CARE" name i) 1 in
              choice_seqs [
                [assume @@ eq_ (bvi 1 1) (var symb_key_dc)];
                [assume @@ not_ @@ eq_ (bvi 1 1) (var symb_key_dc);
                  assume @@ eq_ (var symb_key) (var key)]
                ]
          )
        |> sequence
      in
      seq
        key_assumes
        @@ raw_table name new_keys actions

    let rec of_gcl (gcl : GCL.t) : t =
      match gcl with
      | GCL.Prim p -> prim (Active p)
      | GCL.Seq cs ->
        List.map cs ~f:of_gcl
        |> sequence
      | GCL.Choice cs ->
        List.map cs ~f:of_gcl
        |> choices
        
    let rec count_paths c =
      match c with 
      | Seq cs ->
        List.fold cs ~init:Bigint.one
        ~f:(fun running_product command ->
          count_paths command
          |> Bigint.( * ) running_product
          )
      | Choice cs ->
        List.fold cs ~init:Bigint.zero 
        ~f:(fun running_sum command ->
            count_paths command
            |> Bigint.(+) running_sum
          )
      | Prim (Active _) ->
        Bigint.one
      | Prim (Table {actions;_}) ->
        List.length actions |> Bigint.of_int

    let rec encode_tables (cmd : t) : GCL.t =
      match cmd with
      | Choice cs -> List.map cs ~f:encode_tables |> GCL.choices
      | Seq cs -> List.map cs ~f:encode_tables |> GCL.sequence
      | Prim p ->
        match p with
        | Table {name;keys;actions} ->
          GCL.table (name, keys, actions)
        | Active a -> GCL.prim a

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
      let asserts a = Action.reads a
                      |> List.filter ~f:(fun x -> not (List.exists data ~f:(Var.equal x)))
                      |> AAsserter.from_vars in
      (data, List.bind act_cmds ~f:(fun a -> asserts a @ [a]))

    let rec assert_valids (cmd:t) : t =
      let module PAsserter = Asserter(Pipeline) in
      match cmd with
      | Seq cs ->
        List.map cs ~f:assert_valids |> sequence
      | Choice cxs ->
        List.map cxs ~f:assert_valids |> choices
      | Prim p ->
        match p with
        | Table table ->
          let key_asserts =
            table.keys
            |> List.map ~f:fst
            |> PAsserter.from_vars
            |> List.map ~f:prim
            |> sequence
          in
          let actions = List.map ~f:assert_valids_action table.actions in
          seq key_asserts (prim (Table {table with actions}))
        | Active a ->
          let asserts =
            PAsserter.from_vars @@ Active.reads a
            |> List.map ~f:prim
            |> sequence
          in
          seq asserts cmd

    let track_assigns x (cmd : t) : t =
      let did_assign = Var.make (Printf.sprintf "%s$set" (Var.str x)) 1 in 
      let track_assigns_active = 
        let open Active in function
        | Passive p -> 
          [passive p]
        | Assign (y,e) ->
          if Var.equal y x then 
            [ 
              assign y e;
              assign did_assign @@ Expr.bvi 1 1;
            ]
          else 
            [assign y e]
      in
      let rec loop cmd = 
        match cmd with 
        | Seq cs ->
          sequence_map cs ~f:loop
        | Choice cxs ->
          choices_map cxs ~f:loop
        | Prim p -> 
          match p with 
          | Table {name;keys; actions} -> 
            let actions = 
              List.map actions ~f:(fun (keys,actions) -> 
                keys, 
                List.bind actions ~f:(fun act_prim -> 
                  track_assigns_active act_prim.data
                )
              )
            in
            prim (Table {name; keys; actions})
          | Active a -> 
            track_assigns_active a.data
            |> sequence_map ~f:(fun x -> prim (Active x))
      in
      let open BExpr in 
      let open Expr in 
      sequence [
        assign did_assign @@ Expr.bvi 0 1;
        loop cmd;
        assert_ @@ eq_ (var did_assign) @@ bvi 1 1;
      ]

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

  include Pack
end

module Concrete = struct
  open GCL

  let slice (model : Model.t) (cmd : t) : t option =
    let open Option.Let_syntax in
    let rec slice_aux model cmd : (Model.t * t) option =
    match cmd with
    | Prim p ->
      begin match p.data with
      | Assign (x,e) ->
        let value = Expr.eval model e |> Result.ok_or_failwith in
        let model = Model.update model x value in
        Some (model, Prim p)
      | (Passive (Assume phi)) when BExpr.eval model phi->
        Some (model, Prim p)
      | (Passive (Assume _)) ->
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
  Psv.vc passive_form
