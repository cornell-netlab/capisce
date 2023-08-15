open Core
module Make (KA : sig
    module Prim : sig
      type t [@@deriving sexp, compare, hash, equal]
      val name : t -> string
      val is_node : t -> bool
      val to_smtlib : t -> string
      val is_table : t -> bool
      val assume : BExpr.t -> t
    end
    module S : sig
      type t =
        | Prim of Prim.t
        | Seq of t list
        | Choice of t list
      val skip : t
      val prim : Prim.t -> t
      val sequence : t list -> t
      val choices : t list -> t

    end
  end) = struct

    module V = struct
      type t = KA.Prim.t * int
      [@@deriving sexp, compare, hash, equal]
      let get_id (_, id) = id
      let to_string ((p, idx) : t) =
        Printf.sprintf "%s@%d" (KA.Prim.to_smtlib p) idx
    end

    let vertex_to_cmd (p,_) = KA.S.prim p

    module G = Graph.Persistent.Digraph.ConcreteBidirectional(V)

    type t = G.t

    module O = Graph.Oper.P (G)
    module VMap = Graph.Gmap.Vertex (G) (struct include G let empty () = empty end)

    module VTbl = Hashtbl.Make (struct
        type t = V.t [@@deriving sexp, compare, hash]
      end)


    let succ = G.succ

    let construct_graph (ka : KA.S.t) =
      let src = (KA.Prim.assume BExpr.true_, 0) in
      let g = G.(add_vertex empty src) in
      let dedup = List.dedup_and_sort ~compare:(fun (_,idx) (_, idx') -> Int.compare idx idx') in
      let extend_graph g idx (ns : G.V.t list) p =
        let n' = G.V.create (p, idx) in
        let g = G.add_vertex g n' in
        let ns = dedup ns in
        let g = List.fold ns ~init:g ~f:(fun g n -> G.add_edge g n n') in
        (g, idx + 1, [n'])
      in
      let (g, idx, ns) =
        let rec loop (g, idx, ns) ka =
          match ka with
          | KA.S.Prim p ->
            if KA.Prim.is_node p then
              extend_graph g idx ns p
            else
              (g, idx + 1, ns)
          | KA.S.Choice cs ->
            let g, idx, ns = List.fold cs ~init:(g, idx, [])
                ~f:(fun (g, idx, ns') c ->
                    let g, idx, ns'' = loop (g, idx, ns) c in
                    (g, idx, ns' @ ns'')
                  ) in
            (* Create a join point *)
            extend_graph g idx ns (KA.Prim.assume BExpr.true_)
          | KA.S.Seq cs ->
              List.fold cs ~init:(g, idx, ns)
                ~f:(fun (g, idx, ns) c -> loop (g, idx, ns) c)
        in
        loop (g, 1, [src]) ka
      in
      let snk = G.V.create (KA.Prim.assume BExpr.true_, idx) in
      let g = List.fold ns ~init:g ~f:(fun g n -> G.add_edge g n snk) in
      g

    module Dot = Graph.Graphviz.Dot (struct
        include G
        let edge_attributes (_, _) = [`Color 4711]
        let default_edge_attributes _ = []
        let get_subgraph _ = None
        let vertex_attributes ((p, _) : vertex) : Graph.Graphviz.DotAttributes.vertex list =
          if KA.Prim.is_table p then [`Shape `Oval ; `Color 255 ] else [`Shape `Box]
        let vertex_name ((p,idx) : vertex) =
            Printf.sprintf "\"%s %d\"" (KA.Prim.name p) idx
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
            (KA.Prim.name vtx) idx
            (KA.Prim.to_smtlib vtx);
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
        not (KA.Prim.is_table p) || KA.Prim.equal p (fst src) || KA.Prim.equal p (fst snk)
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


    let to_prog (g : G.t) : KA.S.t =
      let g_join_point_finder = find_first_join_point g in
      let rec loop join_point_opt (curr : G.V.t) =
        match join_point_opt with
        | Some join_point when (snd curr) = (snd join_point) ->
          KA.S.skip
        | Some join_point when (snd curr) > (snd join_point) ->
          failwithf "[ERROR] %s is past the predetermined join point %s" (V.to_string curr) (V.to_string join_point) ()
        | _ ->
          match G.succ g curr with
          | [] -> KA.S.prim (fst curr)
          | [next] ->
            KA.S.sequence [
              KA.S.prim (fst curr);
              loop join_point_opt next]
          | succs ->
            Log.graph "searching for join point from %s" @@ lazy (V.to_string curr);
            let join_point = g_join_point_finder curr in
            Log.graph "Found join point %s" @@ lazy (V.to_string join_point);
            let branches = List.map succs ~f:(loop (Some join_point)) in
            KA.S.(sequence [prim (fst curr);
                            choices branches;
                            loop None join_point])
      in
      let source = find_source g in
      loop None source


end
