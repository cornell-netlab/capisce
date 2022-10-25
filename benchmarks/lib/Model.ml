open Core

type t = (Bigint.t * int) Var.Map.t

let to_string model =
  Var.Map.fold model ~init:"" ~f:(fun ~key ~data ->
      Printf.sprintf "  %s = (_ bv%s %d)\n%s"
        (Var.str key)
        (Bigint.to_string (fst data))
        (snd data)
    )
  |> Printf.sprintf "{\n%s}\n"

let empty : t = Var.Map.empty

let update m x v =
  Var.Map.set m ~key:x ~data:v

let lookup m x = Var.Map.find m x

let project_inputs (passive_model : t) : t =
  Log.debug "Projecting passive_model: \n%s" @@ lazy (to_string passive_model);
  let keys =
    passive_model
    |> Var.Map.keys
    |> List.filter_map ~f:Var.unindex
    |> List.map ~f:fst
    |> List.dedup_and_sort ~compare:Var.compare
  in
  List.fold keys ~init:empty
    ~f:(fun active_model k ->
        Log.debug "Finding value for %s" @@ lazy (Var.str k);
        let k0 = Var.index k 0 in
        Log.debug "\t by looking up %s" @@ lazy (Var.str k0);
        match lookup passive_model k0 with
        | None ->
          active_model
        | Some v ->
          Log.debug "\t found a value %s" @@ lazy (Bigint.to_string @@ fst v);
          update active_model k v
      )
