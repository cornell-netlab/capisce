open Core

let check_state (tables : Model.t list String.Map.t) (phi : BExpr.t) : Model.t option =
  let bad_state model = not (BExpr.check phi model) in
  (* First compute the cross product of all the entries in the table*)
  String.Map.fold tables ~init:[Model.empty]
    ~f:(fun ~key:_ ~data acc -> List.map2_exn data acc ~f:Model.disjoint_union)
  |>
  (* Now find one that produces false *)
  List.find ~f:bad_state
