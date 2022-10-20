open Core
open Primitives

module type CMD = sig
  type t [@@deriving quickcheck, eq, sexp, compare]
  module G : sig type t end
  module Vertex : sig type t end
  module Edge : sig type t end
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val skip : t
  val pass : t
  val dead : t
  val abort : t
  val zero : t
  val one : t
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
  val is_mult_unit : t -> bool
  val is_mult_annihil : t -> bool
  val is_add_unit : t -> bool
  val is_add_annihil : t -> bool
  val contra : t -> t -> bool
  val to_string_aux : int -> t -> string
  val to_string : t -> string
  val count_asserts_aux : t -> int -> int
  val count_asserts : t -> int
  val size : t -> int
  val sequence : t list -> t
  val seq : t -> t -> t
  val choices : t list -> t
  val choice : t -> t -> t
  val choice_seq : t list -> t list -> t
  val choice_seqs : t list list -> t
  val is_primitive : t -> bool
  val subst : Var.t -> Expr.t -> t -> t
  val normalize_names : t -> t
  val dnf : t -> t
  val count_paths : t -> Bigint.t
  val paths : t -> t Sequence.t
  val construct_graph : t -> G.t
  val print_graph : G.t -> string option -> unit
  val count_cfg_paths : G.t -> Bigint.t
  val optimize : t -> t
  val optimize_seq_pair : (t * t) -> (t * t)
end

module Make (P : Primitive) = struct

  module Cmd = struct
    type t =
      | Prim of P.t
      | Seq of t list
      | Choice of t list
    [@@deriving quickcheck, eq, sexp, compare]


    module PSet = Set.Make (P)
    module PMap = Map.Make (P)
    module PHash_set = Hash_set.Make (P)
    module PHashtbl = Hashtbl.Make (P)

    
    let assume phi = Prim (P.assume phi)
    let assert_ phi = Prim (P.assert_ phi)
    let skip = Prim (P.assume BExpr.true_)
    let pass = Prim (P.assert_ BExpr.true_)
    let dead = Prim (P.assume BExpr.false_)
    let abort = Prim (P.assert_ BExpr.false_)

    let prim p = Prim p

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

    let rec trivial_branch_comparisons cs (comps : Expr.t list Var.Map.t) =
      let open Option.Let_syntax in
      match cs with
      | [] -> Some comps
      | Prim p::cs ->
        let%bind comps' = P.comparisons p in
        List.fold comps' ~init:comps
          ~f:(fun acc (key,data) -> Var.Map.add_multi acc ~key ~data)
        |> trivial_branch_comparisons cs
      | _ ->
        None

    let can_collapse_total_trivial_branch cs =
      match trivial_branch_comparisons cs Var.Map.empty with
      | None -> false
      | Some comps ->
        List.length (Var.Map.keys comps) = 1
        && Var.Map.for_alli comps ~f:(fun ~key ~data ->
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

    let rec normalize_names (c : t) : t =
      match c with
      | Prim p -> Prim (P.normalize_names p)
      | Seq cs ->
        List.map cs ~f:normalize_names |> sequence
      | Choice cs ->
        List.map cs ~f:normalize_names
        |> choices

    let dnf (c : t) : t =
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
      Log.path_gen "building the squence of %s paths" @@ lazy (count_paths c |> Bigint.to_string);
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

    let rec const_prop_inner f c : Facts.t * t =
      match c with
      | Prim p ->
        let (f, p) = P.const_prop f p in
        (f, Prim p)
      | Seq cs ->
        let fs, cs =
          List.fold cs ~init:(f, [])
            ~f:(fun (f, cs) c ->
                let f, c = const_prop_inner f c in
                (f, cs @ [c])) in
        (fs, sequence cs)
      | Choice [] ->
        failwith "Choice of no alternatives"
      | Choice (c::cs) ->
        List.fold cs
          ~init:(const_prop_inner f c)
          ~f:(fun (fs, cs) c1 ->
              let f1, c1 = const_prop_inner f c1 in
              let fs = Facts.merge fs f1 in
              (fs , choice c1 cs))

    let const_prop c : t =
      Log.compiler_s "constant propagation";
      const_prop_inner Facts.empty c |> snd

    let rec dead_code_elim_inner reads c : (Var.Set.t * t) =
      match c with
      | Prim (p) ->
        begin match P.dead_code_elim reads p with
          | None ->
            (reads, skip)
          | Some (reads, p) ->
            (reads, prim p)
        end
      | Choice [] -> failwith "cannot have 0-ary choice"
      | Choice (c::cs) ->
        List.fold cs
          ~init:(dead_code_elim_inner reads c)
          ~f:(fun (read_by_cs, cs) c ->
              let read_by_c, c = dead_code_elim_inner reads c in
              (Var.Set.union read_by_cs read_by_c, choice cs c))
      | Seq cs ->
        let (reads, cs) =
          List.fold (List.rev cs) ~init:(reads, [])
            ~f:(fun (reads, cs) c ->
                let reads, c = dead_code_elim_inner reads c in
                (reads, c::cs)) in
        (reads, sequence cs)

    let dead_code_elim c =
      Log.compiler_s "dead code elim";
      Util.fix ~equal
        (fun c -> snd (dead_code_elim_inner Var.Set.empty c))
        c

    let optimize c =
      Log.compiler_s "optimizing...";
      let o c = dead_code_elim (const_prop c) in
      Util.fix ~equal o c

    let optimize_seq_pair (c1,c2) =
      Log.compiler_s "optimizing pair";
      let dce (c1,c2) =
        let (reads, c2) = dead_code_elim_inner Var.Set.empty c2 in
        let (_, c1) = dead_code_elim_inner reads c1 in
        (c1, c2)
      in
      let cp (c1, c2)=
        let (facts, c1) = const_prop_inner Facts.empty c1 in
        let (_    , c2) = const_prop_inner facts       c2 in
        (c1, c2)
      in
      let equal (c1,c2) (c1',c2') = equal c1 c1' && equal c2 c2' in
      let o (c1,c2) = dce (cp (c1,c2)) in
      Util.fix ~equal o (c1,c2)

    module Vertex = struct
      type t = P.t * int
      [@@deriving compare, hash, equal]
    end

    module Edge = struct
      include String
      (* let default = "" *)
    end

    module G = Graph.Persistent.Digraph.ConcreteBidirectional(Vertex) (* (Edge)*)
    module O = Graph.Oper.P (G)
    module VMap = Graph.Gmap.Vertex (G) (struct include G let empty () = empty end)

    let construct_graph t =
      let src = (P.assume BExpr.true_, 0) in
      let g = G.(add_vertex empty src) in
      let dedup = List.dedup_and_sort ~compare:(fun (_,idx) (_, idx') -> Int.compare idx idx') in
      let rec loop idx g ns t =
        let extend_graph g idx ns p =
            let n' = G.V.create (p, idx) in
            let g = G.add_vertex g n' in
            let ns = dedup ns in
            let g = List.fold ns ~init:g ~f:(fun g n -> G.add_edge g n n') in
            (g, idx + 1, [n'])
        in
        match t with
        | Prim p ->
          if P.is_node p then
            extend_graph g idx ns p
          else begin
            (g, idx + 1, ns)
          end
        | Choice ts ->
          let g, idx, ns = List.fold ts ~init:(g, idx, [])
              ~f:(fun (g, idx, ns') t ->
                  let g, idx, ns'' = loop idx g ns t in
                  (g, idx, ns' @ ns'')
                ) in
          (* Create a join point *)
          extend_graph g idx ns (P.assume BExpr.true_)
        | Seq ts ->
          List.fold ts ~init:(g, idx, ns)
            ~f:(fun (g, idx, ns) t -> loop idx g ns t)
      in
      let g, idx, ns = loop 1 g [src] t in
      (*Create a sink node, and add edges to it*)
      let snk = G.V.create (P.assume BExpr.true_, idx) in
      let g = List.fold ns ~init:g ~f:(fun g n -> G.add_edge g n snk) in
      g

    module Dot = Graph.Graphviz.Dot (struct
        include G
        let edge_attributes (_, _) = [`Color 4711]
        let default_edge_attributes _ = []
        let get_subgraph _ = None
        let vertex_attributes ((p, _) : vertex) : Graph.Graphviz.DotAttributes.vertex list =
          if P.is_table p then [`Shape `Oval ; `Color 255 ] else [`Shape `Box]
        let vertex_name ((p,idx) : vertex) = Printf.sprintf "\"%s %d\"" (P.name p) idx
        let default_vertex_attributes _ = []
        let graph_attributes _ = []
      end)


    let print_graph g f =
      let file = match f with
        | Some filename -> Out_channel.create filename
        | None -> Out_channel.stdout in
      Dot.output_graph file g;
      Out_channel.close file

    let print_key g =
      G.fold_vertex (fun (vtx, idx) ->
          Printf.sprintf "%s@%d %s\n\n%s%!" (P.name vtx) idx (P.to_smtlib vtx);
        ) g ""

    let find_source g =
      let f v = function
        | Some found_source -> Some found_source
        | None ->
          if List.is_empty (G.pred g v) then
            Some v
          else
            None
      in
      match G.fold_vertex f g None with
      | None ->
        print_graph g (Some "error_graph.dot");
        Log.error "there are %d nodes" @@ lazy (G.nb_vertex g);
        Log.error "there are %d edges" @@ lazy (G.nb_edges g);
        failwith "Could not find 0-indegree vertex in graph; logged at error_graph.dot"
      | Some source -> source

    module VTbl = Hashtbl.Make (struct
        type t = (P.t * int) [@@deriving sexp, compare, hash]
      end)

    let count_cfg_paths g =
      let dt = VTbl.create () in
      let src = find_source g in
      let rec loop (curr : G.V.t) =
        match VTbl.find dt curr with
        | Some num_paths -> num_paths
        | None ->
          let succs = G.succ g curr in
          let num_paths =
            if List.is_empty succs then
              Bigint.one
            else
              List.sum (module Bigint) succs ~f:loop
          in
          VTbl.set dt ~key:curr ~data:num_paths;
          num_paths
      in
      loop src


    module Path = struct
      type t = G.V.t * G.V.t list
      [@@deriving equal]
      (* list but it can never be empty *)
      (* The path is reversed! i.e. LIFO-style *)
      let singleton vtx : t = (vtx, [])
      let add new_head ((head, pi) : t) : t = (new_head, head::pi)
      let peek ((head, _) : t) = head
      (* let pop (head, pi) : G.V.t * t option = *)
      (*   match pi with *)
      (*   | [] -> head, None *)
      (*   | head'::pi' -> (head, Some (head', pi')) *)
      let contains vtx ((head, rst) : t) =
        G.V.equal vtx head
        || List.exists rst ~f:(G.V.equal vtx)
    end

    let feasible_edge (e : G.edge) g =
      G.mem_vertex g (G.E.src e)
      && G.mem_vertex g (G.E.dst e)

    let induce_graph_between g (src : G.V.t) (snk : G.V.t) =
      let is_good_node p =
        not (P.is_table p) || P.equal p (fst src) || P.equal p (fst snk)
      in
      let vertex_graph = VMap.filter_map (fun vtx ->
          Option.some_if
            (is_good_node (fst vtx) && (snd vtx) >= (snd src) && (snd vtx) <= (snd snk))
            vtx
        ) g
      in
      let edges_graph =
        G.fold_edges_e (fun e g ->
          if feasible_edge e g then
            G.add_edge_e g e
          else
            g
        ) g vertex_graph
      in
      edges_graph

    module PathsTable = Hashtbl.Make (struct
        type t = (P.t * int) * (P.t * int)
        [@@deriving compare, hash, sexp]
      end)

    (* let get_nodes es = *)
    (*   let pair_to_list (v1,v2) = [v1;v2] in *)
    (*   List.bind es ~f:pair_to_list *)
    (*   |> List.dedup_and_sort ~compare:Vertex.compare *)

    let edges_to_graph es =
      List.fold es ~init:G.empty ~f:(fun g (v1, v2) ->
          let g = G.add_vertex g v1 in
          let g = G.add_vertex g v2 in
          let g = G.add_edge g v1 v2 in
          g
        )

    let reachable_graph_between g src snk =
      let module WEdge = struct
        include G
        include Int
        let weight (_: G.edge) : t = zero
        let add = (+)
      end in
      let module P = Graph.Prim.Make (G) (WEdge) in
      Log.path_gen_dot (print_graph g) "graph.dot";
      let fwd = induce_graph_between g src snk in
      Log.path_gen_dot (print_graph fwd) "fwd_graph.dot";
      let bwd = O.mirror fwd in
      Log.path_gen_dot (print_graph bwd) "bwd_graph.dot";
      let fwd_span_edges = P.spanningtree_from fwd src in
      let fwd_span = edges_to_graph fwd_span_edges in
      Log.path_gen_dot (print_graph fwd_span) "fwd_span.dot";
      let bwd_span_edges = P.spanningtree_from bwd snk in
      let bwd_span = O.mirror (edges_to_graph bwd_span_edges) in
      Log.path_gen_dot (print_graph bwd_span) "bwd_span.dot";
      let slice_graph = O.intersect fwd_span bwd_span in
      Log.path_gen_dot (print_graph slice_graph) "slice_graph.dot";
      slice_graph


    let add_paths_between g =
      fun src snk acc_graph ->
      reachable_graph_between g src snk
      |> O.union acc_graph

    let induce (g : G.t) =
      let g_paths_between = add_paths_between g in
      fun (pi : G.V.t list) : G.t ->
      (*outer pi is in reverese order*)
      let rec induce_path pi result_graph : G.t =
        (* inner pi is in forward order *)
        match pi with
        | [] -> failwith "Shouldn't end with nothing in the pipeline"
        | [_] -> result_graph
        | src::tgt::pi ->
          assert ((snd src) < (snd tgt));
          result_graph
          |> g_paths_between src tgt
          |> induce_path (tgt::pi)
      in
      (* let src = find_source g in *)
      (* let tgt = find_sink g in *)
      (*add src & tgt to pi and make sure pi is in the correct order*)
      (* let pi = List.(rev pi |> cons src) in *)
      let pi = List.rev pi in
      Log.path_gen "The induced path:\n%s%!" @@
      lazy (String.concat ~sep:"\n" (List.map pi ~f:(fun vtx ->
          Printf.sprintf "\tNode %d\n%!" (snd vtx)
        )));
      induce_path pi G.empty

    let find_first_join_point g =
      let memo_table = VTbl.create () in
      fun src ->
        let rec loop worklist =
        match worklist with
        | [] -> failwith "could not find a join point"
        | pi::worklist ->
          let vtx = Path.peek pi in
          if List.for_all worklist ~f:(Path.contains vtx) then
            vtx
          else
            List.rev worklist
            |> G.fold_succ (fun vtx -> List.cons (Path.add vtx pi)) g vtx
            |> List.rev
            |> loop
      in
      match VTbl.find memo_table src with
      | None ->
        let jp = loop (List.map (G.succ g src) ~f:Path.singleton)in
        (* Log.print @@ lazy (Printf.sprintf "Found %d" (snd jp)); *)
        VTbl.set memo_table ~key:src ~data:jp;
        jp
      | Some jp ->
        (* Log.print @@ lazy (Printf.sprintf "Found Cached %d" (snd jp)); *)
        jp


    let of_graph (g : G.t) : t =
      let g_join_point_finder = find_first_join_point g in
      let rec loop join_point_opt (curr : G.V.t) =
        match join_point_opt with
        | Some join_point when (snd curr) = (snd join_point) ->
          skip
        | Some join_point when (snd curr) > (snd join_point) ->
          failwith "passed the predetermined join point"
        | _ ->
          let succs = G.succ g curr in
          if List.is_empty succs then
            prim (fst curr)
          else
            let join_point = g_join_point_finder curr in
            let branches = List.map succs ~f:(loop (Some join_point)) in
            sequence [prim (fst curr);
                      choices branches;
                      loop None join_point
                    ]
      in
      let source = find_source g in
      loop None source

    (* Monoids *)
    let zero = dead
    let ( + ) = choice
    let one = skip
    let ( * ) = seq
  end

  include Cmd

end

module GCL = struct
  include Make (Active)

  let assign x e = prim (Active.assign x e)

  let table (name, keys, (actions : (Var.t list * Action.t list) list)) =
    let cp_key idx  = Printf.sprintf "_symb$%s$match_%d" name idx in
    let act_size = Int.of_float Float.(log (of_int (List.length actions)) + 1.0) in
    let cp_action = Var.make (Printf.sprintf "_symb$%s$action" name) act_size in
    let cp_data idx param = (Var.make (Printf.sprintf  "_symb$%s$%d$%s" name idx (Var.str param)) (Var.size param)) in
    let phi_keys = List.mapi keys ~f:(fun idx k ->
        let symb_k = Var.make (cp_key idx) (Var.size k) in
        BExpr.eq_ (Expr.var symb_k) (Expr.var k)) in
    let encode_action idx (params, (body : Action.t list)) =
      let act_choice = assume (BExpr.eq_ (Expr.var cp_action) (Expr.bvi idx act_size)) in
      let symb param = Expr.var (cp_data idx param) in
      let symbolize body param = Action.subst param (symb param) body in
      let f acc body = prim (Active.of_action (List.fold params ~init:body ~f:symbolize)) |> seq acc in
      let body = List.fold body ~init:skip ~f in
      seq act_choice body in
    let encoded_actions = List.mapi actions ~f:encode_action in
    sequence [
      assume (BExpr.ands_ phi_keys);
      choices encoded_actions
    ]

  let rec wp c phi =
    let open BExpr in
    match c with
    | Prim a -> Active.wp a phi
    | Seq cs -> List.fold_right cs ~init:phi ~f:wp
    | Choice cs -> ands_ (List.map cs ~f:(fun c -> wp c phi))

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
      BExpr.(and_ resid (eq_ (x_ curr) (x_ Int.(curr+1))))
      |> update_resid x Int.(curr + 1) tgt

  let passify (c : GCL.t) : Context.t * t =
    let rec loop (ctx : Context.t) (c : GCL.t) : Context.t * t =
      match c with
      | Prim (Assign (x,e)) ->
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
    loop Context.empty c

  let assume_disjunct ?(threshold=1000) cs =
    let c = choices cs in
    if List.exists cs ~f:(fun x -> size x >= threshold) then
      c
    else
      assume (normal c)

  let assume_disjuncts c =
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
  vc (snd (passify c))

module GPL = struct
  include Make (Pipeline)
  let assign x e = Prim (Active (Active.assign x e))
  let table name keys actions = Prim (Table {name; keys; actions})

  let encode_tables (c : t) : GCL.t =
    let rec loop c =
      match c with
      | Prim (Table tbl) ->
        GCL.table (tbl.name, tbl.keys, tbl.actions)
      | Prim (Active a) ->
        GCL.prim a
      | Choice cs ->
        List.sum (module GCL) cs ~f:loop
      | Seq cs ->
        List.fold cs ~init:(GCL.skip)
          ~f:(fun gcl gpl -> GCL.seq gcl (loop gpl))
    in
    let gcl = loop c in
    gcl

  let symbolize (c : t) =
    let gcl = encode_tables c in
    let (ctx, psv) = PassiveGCL.passify gcl in
    let symbolic_parser = PassiveGCL.normal psv in
    let symbolic_parser = BExpr.erase_max_label ctx symbolic_parser in
    assume symbolic_parser

end

module TFG = struct
  module T = struct
    include Pipeline
    let is_node = function
      | Table _ -> true
      | _ -> false
  end
  include Make(T)

  let rec project (gpl : GPL.t) : t =
    match gpl with
    | GPL.Choice cs ->
      choices (List.map cs ~f:project)
    | GPL.Seq cs ->
      sequence (List.map cs ~f:project)
    | GPL.Prim p ->
      let p = match p with
        | Pipeline.Active a -> T.Active a
        | Pipeline.Table t -> T.Table t
      in
      Prim p

  let rec inject (tfg : t) : GPL.t =
    match tfg with
    | Choice cs ->
      GPL.choices (List.map cs ~f:inject)
    | Seq cs ->
      GPL.sequence (List.map cs ~f:inject)
    | Prim p ->
      let p = match p with
        | Pipeline.Active a -> T.Active a
        | Pipeline.Table t -> T.Table t
      in
      GPL.prim p

end

module Generator = struct

  (* module W = Stack *)
  module W = RandomBag.Make (struct
      type t = (Pipeline.t * int) list * (Pipeline.t * int) list
      [@@deriving sexp, compare]
    end)
  (* the elements of the workist are pairs (p,c) where p is the path to the
     current node, and c is the to-be-explored children of the final node of
     p. Note that the path is expressed as a reverse order list, so the last
     element in the path is the first element in the list. That is, c are the
     children of hd p. *)

  let graph = ref None
  let worklist = W.create ()

  let create c =
    let g = TFG.construct_graph c in
    (* let g = TFG.break_random_nodes g  in *)
    Log.path_gen "TFG made with %s paths" @@ lazy (Bigint.to_string @@ TFG.count_cfg_paths g);
    Log.path_gen_dot (TFG.print_graph g) "tfg.dot";
    graph := Some g;
    let src = TFG.find_source g in
    W.push worklist ([src], TFG.G.succ g src);
    TFG.count_cfg_paths g

  let rec get_next () =
    let g = Option.value_exn !graph ~message:"[Generator.get_next] uninitialized graph" in
    match W.pop worklist with
    | None -> None
    | Some ([], []) ->
      failwith "path was empty"
    | Some (vertex::_ as pi, []) ->
      if List.is_empty (TFG.G.succ g vertex) then
        (* vertex is a leaf node *)
        Some pi
      else
        (* keep searching! *)
        get_next ()
    | Some (pi, c::children) ->
      W.push worklist (pi, children);
      W.push worklist (c::pi, TFG.G.succ g c);
      get_next()
end
