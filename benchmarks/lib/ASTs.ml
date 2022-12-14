open Core
open Primitives

module GCL = struct
  module Pack = struct
    include Cmd.Make (Active)

    let assign x e = prim (Active.assign x e)

    let table (tbl_name, keys, (actions : (Var.t list * Action.t list) list)) =
      let open Pipeline in
      let table =
        table tbl_name keys actions
        |> explode
        |> Util.mapmap ~f:(fun a -> prim (to_active_exn a))
        |> choice_seqs
      in
      if String.(tbl_name = "acl") then
        Log.debug "ACL:\n%s\n---------" @@ lazy (to_string table);
      table
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

  let normal (c : t) : BExpr.t =
    let open Passive in
    bottom_up c
      ~sequence:BExpr.ands_
      ~choices:BExpr.ors_
      ~prim:(function
          | Assert b -> b
          | Assume b -> b
        )

  let wrong (c : t) : BExpr.t =
    let open Passive in
    let open BExpr in
    top_down c
      ~init:(false_) (* should never be used *)
      ~prim:(fun _ -> function
          | Assert b -> not_ b
          | Assume _ -> false_
        )
      ~choices:(fun _ cs wrong -> List.map cs ~f:(wrong false_) |> ors_)
      ~sequence:(fun _ cs wrong ->
          List.fold_right cs ~init:false_
            ~f:(fun c acc ->
                let w1 = wrong false_ c in
                let w2 = and_ (normal c) acc in
                or_ w1 w2
              )

        )

  let rec update_resid x curr tgt resid =
    if curr >= tgt then
      resid
    else
      let x_ i = Expr.var (Var.index x i) in
      BExpr.(and_ resid (eq_ (x_ curr) (x_ Int.(curr+1))))
      |> update_resid x Int.(curr + 1) tgt

  let passify (c : GCL.t) : Context.t * t =
    GCL.forward c
      ~init:(Context.empty, skip)
      ~prim:(fun (ctx, acc) p ->
          match p with
          | Active.Assign (x,e) ->
            let e' = Expr.label ctx e in
            let ctx = Context.increment ctx x in
            let x' = Context.label ctx x in
            (ctx, seq acc @@ assume (BExpr.eq_ (Expr.var x') e'))
          | Active.Passive (Assert b) ->
            (ctx, seq acc @@ assert_ (BExpr.label ctx b))
          | Active.Passive (Assume b) ->
            (ctx, seq acc @@ assume (BExpr.label ctx b))
        )
      ~choices:(
          Util.fold_right1
            ~init:Fn.id
            ~f:(fun (ctx_acc, c_acc) (ctx, c) ->
              let ctx, resid_acc, resid =
                Context.merge ctx_acc ctx ~init:(BExpr.true_) ~update:update_resid
              in
              let rc_acc = seq c_acc (assume resid_acc) in
              let rc = seq c (assume resid) in
              (ctx, choice rc_acc rc))
            )
  let vc (c : t) : BExpr.t =
    let phi = wrong c in
    Log.debug "wrong_execs: %s" @@ lazy (BExpr.to_smtlib phi);
    BExpr.not_ phi
    (* |> BExpr.simplify *)

  let remove_asserts (c : t) =
    bottom_up c ~choices ~sequence
      ~prim:(function
          | Assert _ -> skip
          | Assume phi -> assume phi
        )

end

 module GPL = struct
  module Pack = struct
    include Cmd.Make (Pipeline)
    let assign x e = prim (Active (Active.assign x e))
    let table name keys actions = prim (Table {name; keys; actions})

    let encode_tables: t -> GCL.t =
      bottom_up
        ~sequence:GCL.sequence
        ~choices:GCL.choices
        ~prim:(function
            | Table {name;keys;actions} ->
              GCL.table (name, keys, actions)
            | Active a -> GCL.prim a
          )

    let symbolize (c : t) =
      let gcl = encode_tables c in
      let (ctx, psv) = Psv.passify gcl in
      let symbolic_parser = Psv.normal psv in
      let symbolic_parser = BExpr.erase_max_label ctx symbolic_parser in
      assume symbolic_parser

    let tables (c : t) : Table.t list =
      bottom_up c
        ~sequence:List.concat
        ~choices:List.concat
        ~prim:(function
            | Table tbl -> [tbl]
            | _ -> []
          ) |> List.dedup_and_sort ~compare:Table.compare
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

  let project (gpl : GPL.t) : t =
    GPL.bottom_up gpl ~choices ~sequence ~prim:(fun p ->
        let p = match p with
          | Pipeline.Active a -> T.Active a
          | Pipeline.Table t -> T.Table t
        in
        prim p
      )

  let inject (tfg : t) : GPL.t =
    bottom_up
      tfg
      ~choices:GPL.choices
      ~sequence:GPL.sequence
      ~prim:GPL.prim

  (* let of_gpl_graph_no_collapse : GPL.G.t -> G.t  = *)
  (*   let module OfGPL = Graph.Gmap.Edge (GPL.G) (struct *)
  (*       include G *)
  (*       let empty () = empty *)
  (*     end) in *)
  (*   OfGPL.map Fn.id *)

  (* let auto_encode_tables (c : t) : t = *)
  (*   (\** Here `auto` is as in -morphism not -matic *\) *)
  (*   c *)
  (*   |> inject *)
  (*   |> GPL.encode_tables *)
  (*   |> GCL.maps ~choices ~sequence ~prim:(fun a -> prim (Pipeline.active a)) *)

  (* let pick_random_explodable gpl_graph = *)
  (*   let filter_explodable vtx = *)
  (*     if V.is_explodable vtx then List.cons vtx else Fn.id *)
  (*   in *)
  (*   G.fold_vertex filter_explodable gpl_graph [] *)
  (*   |> Util.choose *)

  (* let negativize_indices : G.t -> G.t = *)
  (*   (\* we compute -(idx + 1) to avoid generating 0*\) *)
  (*   let negativize idx = Int.(neg (succ idx)) in *)
  (*   let negativize_idx (p,idx) = (p, negativize idx) in *)
  (*   G.map_vertex negativize_idx *)


  (* let renormalize_indices tfg = *)
  (*   let module Topo = Graph.Topological.Make (G) in *)
  (*   let acc_rewrites (_, old_idx) (new_idx, rewriter) = *)
  (*     let rewriter (p, idx) = *)
  (*       if idx = old_idx then (p, new_idx) else rewriter (p, idx) *)
  (*     in *)
  (*     (Int.succ new_idx, rewriter ) *)
  (*   in *)

  (*   let missingno (_,idx) = failwithf "couldnt find index %d" idx () in *)
  (*   let _, topo_rewriter = Topo.fold acc_rewrites tfg (0, missingno) in *)
  (*   G.map_vertex topo_rewriter tfg *)

  (* let create_explosion_graph (p, _) = *)
  (*   Pipeline.explode p *)
  (*   |> Util.mapmap ~f:GPL.prim *)
  (*   |> GPL.choice_seqs *)
  (*   |> GPL.construct_graph *)


  (* let stitch_into graph node subgraph = *)
  (*   let src = find_source subgraph in *)
  (*   let snk = find_sink subgraph in *)
  (*   let preds = G.pred graph node in *)
  (*   let succs = G.succ graph node in *)
  (*   let replaced = G.remove_vertex graph node *)
  (*                  |> O.union subgraph in *)
  (*   let add_pred x graph pred = G.add_edge graph pred x    in *)
  (*   let add_succ x graph succ = G.add_edge graph x    succ in *)
  (*   let with_preds = List.fold preds ~init:replaced   ~f:(add_pred src) in *)
  (*   let with_succs = List.fold succs ~init:with_preds ~f:(add_succ snk) in *)
  (*   with_succs *)


  (* let explode (node : V.t) (g : G.t) = *)
  (*   create_explosion_graph node *)
  (*   |> of_gpl_graph_no_collapse *)
  (*   |> negativize_indices *)
  (*   |> stitch_into g node *)
  (*   |> renormalize_indices *)

  (* let explode_random c = *)
  (*   let open Option.Let_syntax in *)
  (*   let graph = construct_graph c in *)
  (*   let%map node_to_explode = pick_random_explodable graph in *)
  (*   explode node_to_explode graph *)

  (* let cast_to_gpl_graph : G.t -> GPL.G.t = *)
  (*   let module ToGPL = Graph.Gmap.Edge (G) (struct *)
  (*       include GPL.G *)
  (*       let empty () = empty *)
  (*     end) in *)
  (*   ToGPL.map Fn.id *)

end

(* let induce_gpl_from_tfg_path (g : GPL.G.t) : TFG.V.t list -> GPL.G.t = GPL.induce g *)


module Concrete = struct
  open GCL

  let slice (model : Model.t) (cmd : t) : t option =
    let open Option.Let_syntax in
    Option.map ~f:fst @@
    forward cmd
      ~init:(Some (skip, model))
      ~prim:(fun opt_acc p ->
          let%bind (cmd, model) = opt_acc in
          let k p = seq cmd (prim p) in
          match p with
          | Assign (x,e) ->
            let v = Expr.eval model e in
            Some (k p, Model.update model x v)
          | (Passive (Assume phi)) ->
            Option.some_if
              (BExpr.eval model phi)
              (k p, model)
          | Passive (Assert _) ->
            Some (k p, model)
        )
      ~choices:(fun cxs ->
          match List.filter_map cxs ~f:Fn.id with
          | [cmd_opt] -> Some cmd_opt
          | [] -> failwith "Execution Error: impossible infeasible"
          | _ -> failwith "Execution Error: too many choices"
        )

      (* let rec loop model psv : (t * Model.t) option = *)
    (*   match psv with *)
    (*   | Prim (Assign (x,e)) as p -> *)
    (*     Log.debug "Evaluating %s" @@ lazy (to_string p); *)
    (*     let v = *)
    (*       Expr.eval model e *)
    (*       |> Option.value_exn ~message:(msg (Expr.to_smtlib e)) *)
    (*     in *)
    (*     Some (p, Model.update model x v) *)
    (*   | Prim (Passive (Assume phi)) as p -> *)
    (*     (\* Log.debug "model:\n %s" @@ lazy (Model.to_string model); *\) *)
    (*     let reachable = *)
    (*       BExpr.eval model phi *)
    (*       |> Option.value_exn ~message:(msg (BExpr.to_smtlib phi)) *)
    (*       (\* |> Option.value ~default:true *\) *)
    (*     in *)
    (*     if reachable then *)
    (*       Some (p, model) *)
    (*     else begin *)
    (*       Log.debug "dead node %s" @@ lazy (to_string p); *)
    (*       None *)
    (*     end *)
    (*   | Prim _ as p ->  Some (p, model) *)
    (*   | Choice cs -> *)
    (*     begin match List.filter_map cs ~f:(loop model) with *)
    (*       | [cm_opt] -> *)
    (*         Some cm_opt *)
    (*       | [] -> *)
    (*         Log.error "%s" @@ lazy (Model.to_string model); *)
    (*         List.iter cs ~f:(fun c -> *)
    (*             Log.error "%s\n-------------[]------------\n" @@ *)
    (*               lazy (to_string c) *)
    (*           ); *)
    (*         failwith "Couldn't find choice that satisfied model, path is impossibly infeasible" *)
    (*       | choices -> *)
    (*         List.iter choices ~f:(fun (c,_) -> *)
    (*             Log.error "%s\n-------------[]------------\n" @@ *)
    (*             lazy (to_string c) *)
    (*           ); *)
    (*         failwithf "Got %d choices, expected 1"  (List.length choices) () *)
    (*         (\* Util.choose_exn choices |> Option.some *\) *)
    (*     end *)
    (*   | Seq cs -> *)
    (*     List.fold cs ~init:(Some (skip, model)) *)
    (*       ~f:(fun acc c -> *)
    (*           let open Option.Let_syntax in *)
    (*           let%bind cs, model = acc in *)
    (*           let%map (c', model') = loop model c in *)
    (*           (seq cs c', model') *)
    (*       ) *)
    (* in *)
    (* loop model psv *)
    (* |> Option.map ~f:fst *)

end

module Exploder = struct
  module H = Hashtbl.Make (String)
  type t = (int * (Var.t list * Action.t list)) Stack.t H.t

  let create () : t = H.create ()

  let arm (exploder : t) (table : Table.t) =
    match H.find exploder table.name with
    | Some _ -> failwithf "Tried to arm table %s twice" table.name ()
    | None ->
      let stack = Stack.create () in
      H.set exploder ~key:table.name ~data:stack;
      List.iteri table.actions ~f:(fun i action ->
          Stack.push stack (i, action)
        )

  let pop (exploder : t) gpl : GPL.t option =
    let open GPL in
    bottom_up gpl
      ~choices:choices_opt
      ~sequence:sequence_opt
      ~prim:(fun p ->
          match p with
          | Pipeline.Active _ -> Some (prim p)
          | Pipeline.Table tbl ->
            match H.find exploder tbl.name with
            | None -> Some (prim p)
            | Some stack ->
              match Stack.pop stack with
              | None -> None
              | Some (idx, act) ->
                let phi, acts = Action.symbolize tbl.name ~num_actions:(List.length tbl.actions) ~act_size:(Table.act_size tbl) ~idx act in
                let gpl_act =
                  List.map acts ~f:(fun a -> prim (Pipeline.action a))
                  |> List.cons (assume phi)
                  |> sequence
                in
                Some gpl_act

         )
end


let passive_vc (c : GCL.t) : BExpr.t =
  Psv.passify c
  |> snd
  |> Psv.wrong
  |> BExpr.not_
