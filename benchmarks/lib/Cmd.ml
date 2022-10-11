open Core

module VarSet = Set.Make (Var)
module VarMap = Map.Make (Var)


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

end

module Active = struct
  type t =
    | Passive of Passive.t
    | Assign of Assign.t
  [@@deriving quickcheck, eq, hash, sexp, compare]

  let assume b = Passive (Passive.assume b)
  let assert_ b = Passive (Passive.assert_ b)
  let assign x e = Assign (Assign.assign x e)
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
  end

  module Map = Map.Make (P)
  module Set = Set.Make (P)
  include P
end

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
  val print_graph : string option -> G.t -> unit
  val count_cfg_paths : G.t -> Bigint.t
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

    module Vertex = struct
      type t = P.t * int
      [@@deriving compare, hash, equal]
    end

    module Edge = struct
      include String
      let default = ""
    end

    module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Vertex)(Edge)

    let print_nodes msg ns =
      List.map ns ~f:(fun (_, idx) -> Int.to_string idx)
      |> String.concat ~sep:","
      |> Printf.printf "\t%s: [%s]\n%!" msg

    let construct_graph t =
      Printf.printf "Constructing Graph\n%!";
      let g = G.empty in
      let rec loop idx g ns t =
        match t with
        | Prim p ->
          if P.is_node p then
            let n' = G.V.create (p, idx) in
            let g = G.add_vertex g n' in
            let g = List.fold ns ~init:g ~f:(fun g n -> G.add_edge g n n') in
            print_nodes (Printf.sprintf "Creating node %d, adding edges from" idx) ns;
            (g, idx + 1, [n'])
          else begin
            print_nodes (Printf.sprintf "Skipping node %d, edges persist" idx) ns;
            (g, idx + 1, ns)
          end
        | Choice ts ->
          print_nodes "endpoints prior to choice" ns;
          List.fold ts ~init:(g, idx, [])
            ~f:(fun (g, idx, ns') t ->
                let g, idx, ns'' = loop idx g ns t in
                print_nodes "aggregate_endpoints:" ns;
                (g, idx, ns' @ ns'')
              )
        | Seq ts ->
          List.fold ts ~init:(g, idx, ns)
            ~f:(fun (g, idx, ns) t -> loop idx g ns t)
      in
      let g, idx, ns = loop 0 g [] t in
      (*Create a sink node, and add edges to it*)
      let snk = G.V.create (P.assume BExpr.true_, idx) in
      let g = List.fold ns ~init:g ~f:(fun g n -> G.add_edge g n snk) in
      Printf.printf "Done constructing Graph\n%!";
      g

    module Dot = Graph.Graphviz.Dot (struct
        include G
        let edge_attributes (_, e, _) = [`Label e; `Color 4711]
        let default_edge_attributes _ = []
        let get_subgraph _ = None
        let vertex_attributes _ = [`Shape `Box]
        let vertex_name ((p,idx) : vertex) = Printf.sprintf "\"%s %d\"" (P.name p) idx
        let default_vertex_attributes _ = []
        let graph_attributes _ = []
      end)


    let print_graph f g =
      let file = match f with
        | Some filename -> Out_channel.create filename
        | None -> Out_channel.stdout in
      Dot.output_graph file g

    let print_key g =
      G.fold_vertex (fun (vtx, idx) _ ->
          Printf.printf "%s@%d %s\n\n%!" (P.name vtx) idx (P.to_smtlib vtx);
        ) g ()

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
      | None -> failwith "Could not find 0-indegree vertex in graph"
      | Some source -> source

    (* let find_sink g = *)
    (*   let f v = function *)
    (*     | Some found_sink -> Some found_sink *)
    (*     | None -> *)
    (*       if List.is_empty (G.succ g v) then *)
    (*         Some v *)
    (*       else *)
    (*         None *)
    (*   in *)
    (*   match G.fold_vertex f g None with *)
    (*   | None -> failwith "Could not find 0-outdegree vertex in graph" *)
    (*   | Some sink -> sink *)

    module DT = Hashtbl.Make (struct
        type t = (P.t * int)
        [@@deriving sexp, hash, compare]
      end)

    let count_cfg_paths g =
      let dt = DT.create () in
      let src = find_source g in
      let rec loop (curr : G.V.t) =
        match DT.find dt curr with
        | Some num_paths -> num_paths
        | None ->
          let succs = G.succ g curr in
          let num_paths =
            if List.is_empty succs then
              Bigint.one
            else
              List.sum (module Bigint) succs ~f:loop
          in
          DT.set dt ~key:curr ~data:num_paths;
          num_paths
      in
      loop src


    module Path = struct
      type t = G.V.t * G.V.t list
      (* list but it can never be empty *)
      (* The path is reversed! i.e. LIFO-style *)
      let singleton vtx : t = (vtx, [])
      let add new_head ((head, pi) : t) : t = (new_head, head::pi)
      let peek ((head, _) : t) = head
      let pop (head, pi) : G.V.t * t option =
        match pi with
        | [] -> head, None
        | head'::pi' -> (head, Some (head', pi'))
    end

    module VTbl = Hashtbl.Make (struct
        type t = (P.t * int) [@@deriving sexp, compare, hash]
      end)

    let get_paths_between g (src : G.V.t) (snk : G.V.t) : Path.t list =
      Printf.printf "getting paths between %d and %d\n%!" (snd src) (snd snk);
      let rec loop paths worklist =
        match worklist with
        | [] -> paths
        | pi::worklist ->
          let curr_vtx = Path.peek pi in
          (* Log.print @@ lazy (Printf.sprintf "The current node is %s%!" (P.to_smtlib (fst curr_vtx))); *)
          if G.V.equal curr_vtx src then
            loop (pi::paths) worklist
          else begin
            let preds = G.pred g curr_vtx in
            List.fold preds ~init:worklist
              ~f:(fun worklist prev_vtx ->
                  Path.add prev_vtx pi :: worklist)
            |> loop paths
          end
      in
      loop [] [Path.singleton snk]

    let add_vertex_if_not_exists g vtx =
      if G.mem_vertex g vtx then
        g
      else
        G.add_vertex g vtx


    let add_edge_if_not_exists g src dst =
      if G.mem_edge g src dst then
        g
      else
        G.add_edge g src dst

    let add_paths_between g src snk acc_graph =
      let pis = get_paths_between g src snk in
      Log.print @@ lazy (Printf.sprintf "There are %d paths\n%!" (List.length pis));
      let rec add_path acc_graph pi =
        match Path.pop pi with
        | _, None -> acc_graph
        | (src, Some pi) ->
          (* Invariant: [src] is already in the graph *)
          let dst = Path.peek pi in
          let acc_graph = add_vertex_if_not_exists acc_graph dst in
          let acc_graph = add_edge_if_not_exists acc_graph src dst in
          add_path acc_graph pi
      in
      List.fold pis
        ~f:(add_path)
        ~init:(add_vertex_if_not_exists acc_graph snk)

    let induce (g : G.t) (pi : G.V.t list) : G.t =
      (*outer pi is in reverese order*)
      let rec induce_path result_graph pi : G.t =
        (* inner pi is in forward order *)
        match pi with
        | [] -> failwith "Shouldn't end with nothing in the pipeline"
        | [_] -> result_graph
        | src::tgt::pi ->
          assert ((snd src) < (snd tgt));
          let result_graph = add_paths_between g src tgt result_graph in
          induce_path result_graph (tgt::pi)
      in
      let src = find_source g in
      (* let tgt = find_sink g in *)
      (*add src & tgt to pi and make sure pi is in the correct order*)
      let pi = List.(rev pi |> cons src) in
      Printf.printf "The induced path:\n%!";
      List.iter pi ~f:(fun vtx ->
        Printf.printf "\tNode %d\n%!" (snd vtx)
      );
      induce_path G.empty pi

    let of_graph (g : G.t) : t =
      Log.print @@ lazy "Getting CMD of graph";
      let rec loop (curr : G.V.t) =
        Log.print @@ lazy (Printf.sprintf "Node %d" (snd curr));
        let succs = G.succ g curr in
        if List.is_empty succs then
          prim (fst curr)
        else
          List.map succs ~f:(loop)
          |> choices
          |> seq (prim (fst curr))
      in
      let source = find_source g in
      loop source

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
    let cp_key idx  = Printf.sprintf "_symb$%s$key_$%d" name idx in
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

  let rec const_prop_aux (f : Facts.t) (c : t) =
    match c with
    | Prim (Assign (x,e)) ->
      let e = Expr.fun_subst (Facts.lookup f) e in
      let f = Facts.update f x e in
       (f, assign x e)
    | Prim (Passive (Assert b)) ->
      let b = BExpr.fun_subst (Facts.lookup f) b |> BExpr.simplify in
      let f =
        match BExpr.get_equality b with
        | Some (x, e) -> Facts.update f x e
        | None -> f
      in
      (f, assert_ b)
    | Prim (Passive (Assume b)) ->
      let b = BExpr.fun_subst (Facts.lookup f) b |> BExpr.simplify in
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
    | Prim (Assign (x, e)) ->
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

  (* let rec dead_code_elim_fwd c (used : VarSet.t) : (t * VarSet.t) = *)
  (*   let open VarSet in *)
  (*   let concat (x,y) = x @ y in *)
  (*   let setify f e = f e |> concat |> of_list in *)
  (*   match c with *)
  (*   | (Prim (Assign (x,e))) -> *)
  (*     let vars_of_e = setify Expr.vars e in *)
  (*     (assign x e, union (add used x) vars_of_e) *)
  (*   | (Prim (Passive (Assert b))) -> (assert_ b, union used (setify BExpr.vars b)) *)
  (*   | (Prim (Passive (Assume b))) -> *)
  (*     let bs_vars = setify BExpr.vars b in *)
  (*     if is_empty (inter bs_vars used) *)
  (*     && VarSet.for_all bs_vars ~f:(Fn.non Var.is_symbRow) then *)
  (*       (skip, used) *)
  (*     else *)
  (*       (assume b, union bs_vars used) *)
  (*   | Choice [] -> *)
  (*     failwith "cannot have 0-ary choice" *)
  (*   | Choice (c::cs) -> *)
  (*     List.fold cs *)
  (*       ~init:(dead_code_elim_fwd c used) *)
  (*       ~f:(fun (cs, used_by_cs) c -> *)
  (*           let c, used_by_c = dead_code_elim_fwd c used in *)
  (*           (choice cs c, union used_by_cs used_by_c)) *)
  (*   | Seq cs -> *)
  (*     let rcs, used = *)
  (*       List.fold cs ~init:([], used) *)
  (*         ~f:(fun (cs, used) c -> *)
  (*             let c, used = dead_code_elim_fwd c used in *)
  (*             (c::cs, used)) *)
  (*     in *)
  (*     (List.rev rcs |> sequence, used) *)

  let dead_code_elim_inner c =
    let c, _ = dead_code_elim_bwd c VarSet.empty in
    (* let c, _ = dead_code_elim_fwd c VarSet.empty in *)
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
      BExpr.(and_ resid (eq_ (x_ curr) (x_ Int.(curr+1))))
      |> update_resid x Int.(curr + 1) tgt

  let passify (c : GCL.t) : Context.t * t =
    Log.print @@ lazy "Passifying";
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
  vc (snd (passify c))

module GPL = struct
  include Make (Pipeline)
  let assign x e = Prim (Active (Active.assign x e))
  let table name keys actions = Prim (Table {name;keys;actions})

  let encode_tables (c : t) : GCL.t =
    let rec loop c =
      match c with
      | Prim (Table tbl) ->
        Log.print @@ lazy (Printf.sprintf "encode_tables.loop:\n%s" (to_string c));
        GCL.table (tbl.name, tbl.keys, tbl.actions)
      | Prim (Active a) ->
        Log.print @@ lazy (Printf.sprintf "encode_tables.loop:\n%s" (to_string c));
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
    Log.print @@ lazy (Printf.sprintf "GCL: %s" (GCL.to_string gcl));
    let (ctx, psv) = PassiveGCL.passify gcl in
    Log.print @@ lazy (Printf.sprintf "PSV: %s" (PassiveGCL.to_string psv));
    let symbolic_parser = PassiveGCL.normal psv in
    let symbolic_parser = BExpr.erase_max_label ctx symbolic_parser in
    Log.print @@ lazy (Printf.sprintf "symbolic parser: %s" (BExpr.to_smtlib symbolic_parser));
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
  let graph = ref None
  let worklist =
    (* the elements of the workist are pairs (p,c) where p is the path to the
       current node, and c is the to-be-explored children of the final node of
       p. Note that the path is expressed as a reverse order list, so the last
       element in the path is the first element in the list. That is, c are the
       children of hd p. *)
    Log.print @@ lazy "Initializing generator";
    Stack.create ()

  let create c =
    let g = TFG.construct_graph c in
    if !Log.debug then TFG.print_graph (Some "tfg.dot") g;
    graph := Some g;
    let src = TFG.find_source g in
    Stack.push worklist ([src], TFG.G.succ g src)

  let rec get_next () =
    let g = Option.value_exn !graph ~message:"[Generator.get_next] uninitialized graph" in
    match Stack.pop worklist with
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
      Stack.push worklist (pi, children);
      Stack.push worklist (c::pi, TFG.G.succ g c);
      get_next()
end
