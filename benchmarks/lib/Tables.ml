open Core
(* Here we represent the table-path abstraction in P4 programs *)

type t =
  | Skip
  | Table of string
  | Choice of t * t
  | Seq of t * t


let skip = Skip
let table s = Table s
let choice t1 t2 = Choice (t1, t2)
let seq t1 t2 =
  match t1, t2 with
  | Skip, _ -> t2
  | _, Skip -> t1
  | _, _  -> Seq (t1, t2)


module Node = struct
  type t = string
  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

module Edge = struct
  type t = string
  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
  let default = ""
end

module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)

module Dot = Graph.Graphviz.Dot (struct
    include G
    let edge_attributes (_, e, _) = [`Label e; `Color 4711]
    let default_edge_attributes _ = []
    let get_subgraph _ = None
    let vertex_attributes _ = [`Shape `Box]
    let vertex_name v = v
    let default_vertex_attributes _ = []
    let graph_attributes _ = []
  end)

let construct_graph t =
  let g = G.empty in
  let rec loop g ns t =
    match t with
    | Skip -> (g,ns)
    | Table name ->
      let n' = G.V.create name in
      let g = G.add_vertex g n' in
      let g = List.fold ns ~init:g ~f:(fun g n -> G.add_edge g n n' ) in
      (g,[n'])
    | Choice (t1,t2) ->
      let g1,ns1 = loop g  ns t1 in
      let g2,ns2 = loop g1 ns t2 in
      (g2, ns1 @ ns2)
    | Seq (t1,t2) ->
      let g1, ns1 = loop g ns t1 in
      loop g1 ns1 t2
  in
  let g, _ = loop g [] t in
  g


let print_graph f g =
  let file = match f with
    | Some filename -> Out_channel.create filename
    | None -> Out_channel.stdout in
  Dot.output_graph file g

module DT = Hashtbl.Make(String)

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
  | None -> failwith "Could not find 0-degree vertex in graph"
  | Some source -> source

let count_paths g =
  let dt = DT.create () in
  let src = find_source g in
  let rec loop curr =
    match DT.find dt curr with
    | Some num_paths -> num_paths
    | None ->
      let succs = G.succ g curr in
      let num_paths =
        if List.is_empty succs then
          1
        else
          List.sum (module Int) succs ~f:loop
      in
      DT.set dt ~key:curr ~data:num_paths;
      num_paths
  in
  loop src
