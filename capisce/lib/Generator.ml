open Core
module Make
    ( WMake : functor (VV : sig type t [@@deriving sexp, compare] end) ->
          sig
            type t
            val create : unit -> t
            val push : t -> (VV.t list * VV.t list) -> unit
            val pop : t -> (VV.t list * VV.t list) option
          end )
    ( V : sig
        type t [@@deriving sexp, compare]
      end )
    (G : sig
       type t
       val find_source : t -> V.t
       val count_cfg_paths : t -> Bigint.t
       val succ : t -> V.t -> V.t list
     end) = struct

      (* RandomBag.Make (struct *)
      (*   type t = V.t list * V.t list *)
      (*   [@@deriving sexp, compare] *)
      (* end) *)
  (* the elements of the workist are pairs (p,c) where p is the path to the
     current node, and c is the to-be-explored children of the final node of
     p. Note that the path is expressed as a reverse order list, so the last
     element in the path is the first element in the list. That is, c are the
     children of hd p. *)

  module W = WMake(V)

  type t = {graph : G.t ref;
            worklist : W.t;
            total_paths : Bigint.t
           }

  let graph state = !(state.graph)

  let create g =
    (* let g = TFG.construct_graph c in *)
    (* (\* let g = TFG.break_random_nodes g  in *\) *)
    (* Log.path_gen "TFG made with %s paths" @@ lazy (Bigint.to_string @@ TFG.count_cfg_paths g); *)
    (* Log.path_gen_dot (TFG.print_graph g) "tfg.dot"; *)
    let state = {graph = ref g; worklist = W.create (); total_paths = G.count_cfg_paths g} in
    let src = G.find_source g in
    W.push state.worklist ([src], G.succ g src);
    state

  let total_paths (state : t) = state.total_paths


  let rec get_next_inner (state : t) =
    match W.pop state.worklist with
    | None -> None
    | Some ([], []) ->
      failwith "path was empty"
    | Some (vertex::_ as pi, []) ->
      if List.is_empty (G.succ (graph state) vertex) then
        (* vertex is a leaf node *)
        Some pi
      else
        (* keep searching! *)
        get_next_inner state
    | Some (pi, c::children) ->
      W.push state.worklist (pi, children);
      W.push state.worklist (c::pi, G.succ (graph state) c);
      get_next_inner state

  let get_next (state : t) =
    let next = get_next_inner state in
    next



  (* let explode_random pi : int = *)
  (*   let to_explode = List.filter pi ~f:V.is_explodable |> Util.choose_exn in *)
  (*   let rec explode pi : V.t list list = *)
  (*   let open List.Let_syntax in *)
  (*   match pi with *)
  (*   | [] -> [[]] *)
  (*   | vtx::pi -> *)
  (*     if V.compare vtx to_explode = 0 then *)
  (*       let%bind pi = explode pi in *)
  (*       let%map choice = V.explode vtx in *)
  (*       choice @ pi *)
  (*     else *)
  (*       let%map pi = explode pi in *)
  (*       vtx::pi *)
  (*   in *)
  (*   (\* explode it *\) *)
  (*   let new_paths = explode pi in *)
  (*   (\* push the new paths to the stack *\) *)
  (*   List.iter new_paths ~f:(fun new_pi -> *)
  (*       W.push worklist (new_pi, []) *)
  (*     ); *)
  (*   List.length new_paths *)
end
