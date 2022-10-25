open Core
open Primitives

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

    let sequence_opt cs =
      Util.commute cs
      |> Option.map ~f:sequence

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

    (* let rec trivial_branch_comparisons cs (comps : Expr.t list Var.Map.t) = *)
    (*   let open Option.Let_syntax in *)
    (*   match cs with *)
    (*   | [] -> Some comps *)
    (*   | Prim p::cs -> *)
    (*     let%bind comps' = P.comparisons p in *)
    (*     List.fold comps' ~init:comps *)
    (*       ~f:(fun acc (key,data) -> Var.Map.add_multi acc ~key ~data) *)
    (*     |> trivial_branch_comparisons cs *)
    (*   | _ -> *)
    (*     None *)

    (* let can_collapse_total_trivial_branch cs = *)
    (*   match trivial_branch_comparisons cs Var.Map.empty with *)
    (*   | None -> false *)
    (*   | Some comps -> *)
    (*     List.length (Var.Map.keys comps) = 1 *)
    (*     && Var.Map.for_alli comps ~f:(fun ~key ~data -> *)
    (*         String.is_suffix (Var.str key) ~suffix:"$action" *)
    (*         && List.for_all data ~f:(fun e -> Option.is_some (Expr.get_const e))) *)

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
        else
        (* if can_collapse_total_trivial_branch cs then *)
        (*   skip *)
        (* else *)
          begin
            match List.dedup_and_sort cs ~compare with
            | [c] -> c
            | cs -> Choice cs
          end

    let choices_opt cs : t option =
      Util.commute cs
      |> Option.map ~f:choices


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

    module V = struct
      type t = P.t * int
      [@@deriving sexp, compare, hash, equal]
      let get_id (_, id) = id
      let to_string ((p, idx) : t) =
        Printf.sprintf "%s@%d" (P.to_smtlib p) idx

      let is_explodable (p, _) = P.is_table p

      let explode (_,_) = failwith "Cannot synthesize explosion vertices with no context"
    end

    let vertex_to_cmd (p,_) = prim p

    module E = struct
      include String
      (* let default = "" *)
    end

    module G = Graph.Persistent.Digraph.ConcreteBidirectional(V) (* (Edge)*)
    module O = Graph.Oper.P (G)
    module VMap = Graph.Gmap.Vertex (G) (struct include G let empty () = empty end)

    let construct_graph t =
      let src = (P.assume BExpr.true_, 0) in
      let g = G.(add_vertex empty src) in
      let dedup = List.dedup_and_sort ~compare:(fun (_,idx) (_, idx') -> Int.compare idx idx') in
      let rec loop idx g ns t =
        let extend_graph g idx (ns : G.V.t list) p =
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
        let vertex_name ((p,idx) : vertex) =
            Printf.sprintf "\"%s %d\"" (P.name p) idx
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
          Printf.sprintf "%s@%d %s\n\n%s%!"
            (P.name vtx) idx
            (P.to_smtlib vtx);
        ) g ""

    let find_source g : V.t =
      let f v =
        if List.is_empty (G.pred g v) then
          List.cons v
        else
          Fn.id
      in
      match G.fold_vertex f g [] with
      | [source] -> source
      | [] ->
        print_graph g (Some "error_graph");
        Log.error "there are %d nodes" @@ lazy (G.nb_vertex g);
        Log.error "there are %d edges" @@ lazy (G.nb_edges g);
        failwith "Could not find 0-indegree vertex in graph; logged at error_graph.dot"
      | sources ->
        print_graph g (Some "error_graph");
        Log.error "there are %d nodes" @@ lazy (G.nb_vertex g);
        Log.error "there are %d edges" @@ lazy (G.nb_edges g);
        failwithf "Found %d sources!!!!! logged at error_graph.dot" (List.length sources) ()

    let find_sink g : V.t =
      let f v =
          if List.is_empty (G.succ g v) then
            List.cons v
          else
            Fn.id
      in
      match G.fold_vertex f g [] with
      | [sink] -> sink
      | [] ->
        print_graph g (Some "error_graph");
        Log.error "there are %d nodes" @@ lazy (G.nb_vertex g);
        Log.error "there are %d edges" @@ lazy (G.nb_edges g);
        failwith "Could not find 0-indegree vertex in graph; logged at error_graph.dot"
      | sinks ->
        print_graph g (Some "error_graph");
        Log.error "there are %d nodes" @@ lazy (G.nb_vertex g);
        Log.error "there are %d edges" @@ lazy (G.nb_edges g);
        failwithf "Found %d sinks!!!!! logged at error_graph.dot" (List.length sinks) ()



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

      let to_string (pi : t) : string =
        let rec loop (head, rst) =
          match rst with
          | [] ->
            Printf.sprintf "%d%!" (V.get_id head)
          | x::rst ->
            loop (x, rst)
            |> Printf.sprintf "%d,%s" (V.get_id head)
        in
        Printf.sprintf "%s" (loop pi)
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
            (is_good_node (fst vtx)
             && (snd vtx) >=  (snd src)
             && (snd vtx) <= (snd snk))
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
        type t = V.t * V.t
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
      let str = lazy (Printf.sprintf "%d and %d" (snd src) (snd snk)) in
      (* Log.debug "generating path between %s" @@ str; *)
      Log.tree_s "the full graph";
      Log.tree_dot (print_graph g) "graph";
      assert (G.mem_vertex g snk);
      let fwd = induce_graph_between g src snk in
      assert (G.mem_vertex fwd snk);
      Log.tree "forward graph between %s" str;
      Log.tree_dot (print_graph fwd) "fwd_graph";
      let bwd = O.mirror fwd in
      Log.tree "backward graph between %s" str;
      Log.tree_dot (print_graph bwd) "bwd_graph";
      let fwd_span_edges = P.spanningtree_from fwd src in
      let fwd_span = edges_to_graph fwd_span_edges in
      Log.tree "forward spanning tree between %s" str;
      Log.tree_dot (print_graph fwd_span) "fwd_span";
      assert (G.mem_vertex bwd snk);
      let bwd_span_edges = P.spanningtree_from bwd snk in
      let bwd_span = O.mirror (edges_to_graph bwd_span_edges) in
      Log.tree "backward spanning tree between %s" str;
      Log.tree_dot (print_graph bwd_span) "bwd_span";
      let spans = O.intersect fwd_span bwd_span in
      Log.tree "Span graph between %s" str;
      Log.tree_dot (print_graph spans) "spans";
      let slice_graph =
        G.fold_edges (fun src dst slice_graph ->
            if G.mem_vertex slice_graph src && G.mem_vertex slice_graph dst then
              G.add_edge slice_graph src dst
            else
              slice_graph
          ) g spans
      in
      (* Log.path_gen "Slice graph between %s" str; *)
      (* Log.path_gen_dot (print_graph slice_graph) "slice_graph"; *)
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
          assert (G.mem_vertex g src);
          assert (G.mem_vertex g tgt);
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
          Printf.sprintf "\tNode %s%!" (V.to_string vtx)
        )));
      induce_path pi G.empty

    let find_first_join_point g =
      let memo_table = VTbl.create () in
      fun src ->
        let rec loop worklist =
          Log.graph "\tWORKLIST from : %s" @@ lazy (V.to_string src);
          List.iter worklist ~f:(fun path ->
              Log.graph "\t\t%s" @@ lazy (Path.to_string path)
            );
          match worklist with
          | [] -> failwith "could not find a join point"
          | pi::worklist ->
            let vtx = Path.peek pi in
            if List.for_all worklist ~f:(Path.contains vtx) then begin
              Log.graph "---------%s is in all worklist elements" @@ lazy (V.to_string vtx);
              vtx
            end else begin
              let succs = G.succ g vtx in
              let new_worklist =
                if List.is_empty succs then begin
                  Log.graph "\t no successors for path %s" @@ lazy (Path.to_string pi);
                  worklist @ [pi]
                end else
                  List.rev worklist
                  |> G.fold_succ (fun vtx ->
                      Log.graph "\tadding vertex %d" @@ lazy (V.get_id vtx);
                      Log.graph "\t   to path %s" @@ lazy (Path.to_string pi);
                      List.cons (Path.add vtx pi)) g vtx
                  |> List.rev
              in
              Log.graph "\tUPDATED WORKLIST from : %s" @@ lazy (V.to_string src);
              List.iter new_worklist ~f:(fun path ->
                  Log.graph "\t\t%s" @@ lazy (Path.to_string path)
                );
              loop new_worklist
            end
        in
        match VTbl.find memo_table src with
        | None ->
          Log.graph_s @@ List.to_string (G.succ g src) ~f:V.to_string;
          let jp = loop (List.map (G.succ g src) ~f:Path.singleton) in
          (* Log.print @@ lazy (Printf.sprintf "Found %d" (snd jp)); *)
          VTbl.set memo_table ~key:src ~data:jp;
          jp
        | Some jp ->
          Log.graph "----------Found Cached JP %d" @@ lazy (snd jp);
          jp


    let of_graph (g : G.t) : t =
      let g_join_point_finder = find_first_join_point g in
      let rec loop join_point_opt (curr : G.V.t) =
        match join_point_opt with
        | Some join_point when (snd curr) = (snd join_point) ->
          skip
        | Some join_point when (snd curr) > (snd join_point) ->
          failwithf "[ERROR] %s is past the predetermined join point %s" (V.to_string curr) (V.to_string join_point) ()
        | _ ->
          match G.succ g curr with
          | [] -> prim (fst curr)
          | [next] ->
            loop join_point_opt next
            |> seq (prim (fst curr))
          | succs ->
            Log.graph "searching for join point from %s" @@ lazy (V.to_string curr);
            let join_point = g_join_point_finder curr in
            Log.graph "Found join point %s" @@ lazy (V.to_string join_point);
            let branches = List.map succs ~f:(loop (Some join_point)) in
            sequence [prim (fst curr);
                      choices branches;
                      loop None join_point
                    ]
      in
      let source = find_source g in
      loop None source

    let rec maps ~prim ~sequence ~choices (c : t) =
      let f = maps ~prim ~sequence ~choices in
      match c with
      | Prim p -> prim p
      | Seq cs -> sequence @@ List.map cs ~f
      | Choice cs -> choices @@ List.map cs ~f

    let vars c =
      let sorted_concat xss =
        List.concat xss
        |> Var.sort
      in
      maps c
        ~prim:(Fn.compose Var.sort P.vars)
        ~sequence:sorted_concat
        ~choices:sorted_concat

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
        let e' = Expr.label ctx e in
        let ctx = Context.increment ctx x in
        let x' = Context.label ctx x in
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

  let remove_asserts (c : t) =
    maps c ~choices ~sequence
      ~prim:(function
          | Assert _ -> skip
          | Assume phi -> assume phi
        )

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

  let tables c : Table.t list =
    maps c ~sequence:List.concat ~choices:List.concat
      ~prim:(function | Table tbl -> [tbl]
                      | _ -> [])
    |> List.dedup_and_sort ~compare:Table.compare


end

module TFG = struct
  module T = struct
    include Pipeline
    let is_node = function
      | Table _ -> true
      | _ -> false
  end
  include Make(T)

  let project (gpl : GPL.t) : t =
    GPL.maps gpl ~choices ~sequence ~prim:(fun p ->
        let p = match p with
          | Pipeline.Active a -> T.Active a
          | Pipeline.Table t -> T.Table t
        in
        prim p
      )

  let inject (tfg : t) : GPL.t =
    let maps_ = maps in
    let open GPL in
    maps_ tfg ~choices ~sequence ~prim:(fun p ->
      let p = match p with
        | T.Active a -> Pipeline.Active a
        | T.Table t -> Pipeline.Table t
      in
      prim p
      )

  let of_gpl_graph_no_collapse : GPL.G.t -> G.t  =
    let module OfGPL = Graph.Gmap.Edge (GPL.G) (struct
        include G
        let empty () = empty
      end) in
    OfGPL.map Fn.id

  (* let auto_encode_tables (c : t) : t = *)
  (*   (\** Here `auto` is as in -morphism not -matic *\) *)
  (*   c *)
  (*   |> inject *)
  (*   |> GPL.encode_tables *)
  (*   |> GCL.maps ~choices ~sequence ~prim:(fun a -> prim (Pipeline.active a)) *)

  let pick_random_explodable gpl_graph =
    let filter_explodable vtx =
      if V.is_explodable vtx then List.cons vtx else Fn.id
    in
    G.fold_vertex filter_explodable gpl_graph []
    |> Util.choose

  let negativize_indices : G.t -> G.t =
    (* we compute -(idx + 1) to avoid generating 0*)
    let negativize idx = Int.(neg (succ idx)) in
    let negativize_idx (p,idx) = (p, negativize idx) in
    G.map_vertex negativize_idx

  
  let renormalize_indices tfg =
    let module Topo = Graph.Topological.Make (G) in
    let acc_rewrites (_, old_idx) (new_idx, rewriter) =
      let rewriter (p, idx) =
        if idx = old_idx then (p, new_idx) else rewriter (p, idx)
      in
      (Int.succ new_idx, rewriter )
    in

    let missingno (_,idx) = failwithf "couldnt find index %d" idx () in
    let _, topo_rewriter = Topo.fold acc_rewrites tfg (0, missingno) in
    G.map_vertex topo_rewriter tfg

  let create_explosion_graph (p, _) =
    Pipeline.explode p
    |> Util.mapmap ~f:GPL.prim
    |> GPL.choice_seqs
    |> GPL.construct_graph


  let stitch_into graph node subgraph =
    let src = find_source subgraph in
    let snk = find_sink subgraph in
    let preds = G.pred graph node in
    let succs = G.succ graph node in
    let replaced = G.remove_vertex graph node
                   |> O.union subgraph in
    let add_pred x graph pred = G.add_edge graph pred x    in
    let add_succ x graph succ = G.add_edge graph x    succ in
    let with_preds = List.fold preds ~init:replaced   ~f:(add_pred src) in
    let with_succs = List.fold succs ~init:with_preds ~f:(add_succ snk) in
    with_succs

  
  let explode (node : V.t) (g : G.t) =
    create_explosion_graph node
    |> of_gpl_graph_no_collapse
    |> negativize_indices
    |> stitch_into g node
    |> renormalize_indices

  let explode_random c =
    let open Option.Let_syntax in
    let graph = construct_graph c in
    let%map node_to_explode = pick_random_explodable graph in
    explode node_to_explode graph

  let cast_to_gpl_graph : G.t -> GPL.G.t =
    let module ToGPL = Graph.Gmap.Edge (G) (struct
        include GPL.G
        let empty () = empty
      end) in
    ToGPL.map Fn.id

end

let induce_gpl_from_tfg_path (g : GPL.G.t) : TFG.V.t list -> GPL.G.t = GPL.induce g


module Concrete = struct
  open GCL

  let slice (model : Model.t) (psv : t) : t option =
    (* Log.path_gen "slicing the following program:\n %s" @@ lazy (to_string gcl); *)
    let msg = Printf.sprintf "Couldn't evaluate: %s" in
    let rec loop model psv : (t * Model.t) option =
      match psv with
      | Prim (Assign (x,e)) as p ->
        Log.debug "Evaluating %s" @@ lazy (to_string p);
        let v =
          Expr.eval model e
          |> Option.value_exn ~message:(msg (Expr.to_smtlib e))
        in
        Some (p, Model.update model x v)
      | Prim (Passive (Assume phi)) as p ->
        (* Log.debug "model:\n %s" @@ lazy (Model.to_string model); *)
        let reachable =
          BExpr.eval model phi
          |> Option.value_exn ~message:(msg (BExpr.to_smtlib phi))
          (* |> Option.value ~default:true *)
        in
        if reachable then
          Some (p, model)
        else begin
          Log.debug "dead node %s" @@ lazy (to_string p);
          None
        end
      | Prim _ as p ->  Some (p, model)
      | Choice cs ->
        begin match List.filter_map cs ~f:(loop model) with
          | [cm_opt] ->
            Some cm_opt
          | [] ->
            Log.error "%s" @@ lazy (Model.to_string model);
            List.iter cs ~f:(fun c ->
                Log.error "%s\n-------------[]------------\n" @@
                  lazy (to_string c)
              );
            failwith "Couldn't find choice that satisfied model, path is impossibly infeasible"
          | choices ->
            List.iter choices ~f:(fun (c,_) ->
                Log.error "%s\n-------------[]------------\n" @@
                lazy (to_string c)
              );
            failwithf "Got %d choices, expected 1"  (List.length choices) ()
            (* Util.choose_exn choices |> Option.some *)
        end
      | Seq cs ->
        List.fold cs ~init:(Some (skip, model))
          ~f:(fun acc c ->
              let open Option.Let_syntax in
              let%bind cs, model = acc in
              let%map (c', model') = loop model c in
              (seq cs c', model')
          )
    in
    loop model psv
    |> Option.map ~f:fst

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
    maps gpl
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
