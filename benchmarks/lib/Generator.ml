open Core
module Make
    ( V : sig
        type t [@@deriving sexp, compare]
      end )
    (G : sig
       type t
       val find_source : t -> V.t
       val count_cfg_paths : t -> Bigint.t
       val succ : t -> V.t -> V.t list
     end) = struct

  module W = Stack
      (* RandomBag.Make (struct *)
      (*   type t = V.t list * V.t list *)
      (*   [@@deriving sexp, compare] *)
      (* end) *)
  (* the elements of the workist are pairs (p,c) where p is the path to the
     current node, and c is the to-be-explored children of the final node of
     p. Note that the path is expressed as a reverse order list, so the last
     element in the path is the first element in the list. That is, c are the
     children of hd p. *)

  let graph = ref None
  let worklist = W.create ()

  let create g =
    (* let g = TFG.construct_graph c in *)
    (* (\* let g = TFG.break_random_nodes g  in *\) *)
    (* Log.path_gen "TFG made with %s paths" @@ lazy (Bigint.to_string @@ TFG.count_cfg_paths g); *)
    (* Log.path_gen_dot (TFG.print_graph g) "tfg.dot"; *)
    graph := Some g;
    let src = G.find_source g in
    W.push worklist ([src], G.succ g src);
    G.count_cfg_paths g

  let rec get_next () =
    let g = Option.value_exn !graph ~message:"[Generator.get_next] uninitialized graph" in
    match W.pop worklist with
    | None -> None
    | Some ([], []) ->
      failwith "path was empty"
    | Some (vertex::_ as pi, []) ->
      if List.is_empty (G.succ g vertex) then
        (* vertex is a leaf node *)
        Some pi
      else
        (* keep searching! *)
        get_next ()
    | Some (pi, c::children) ->
      W.push worklist (pi, children);
      W.push worklist (c::pi, G.succ g c);
      get_next()
end
