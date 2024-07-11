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

let disjoint_union m1 m2 =
  Var.Map.merge m1 m2
    ~f:(fun ~key:_ -> function
        | `Left x | `Right x ->
          Some x
        | `Both _ ->
          failwith "union not disjoint"
      )

let of_alist_exn alist = Var.Map.of_alist_exn alist

let of_map m = m

let project_inputs (passive_model : t) : t =
  let keys =
    passive_model
    |> Var.Map.keys
    |> List.filter_map ~f:Var.unindex
    |> List.map ~f:fst
    |> List.dedup_and_sort ~compare:Var.compare
  in
  List.fold keys ~init:empty
    ~f:(fun active_model k ->
        let k0 = Var.index k 0 in
        match lookup passive_model k0 with
        | None ->
          active_model
        | Some v ->
          update active_model k v
      )
