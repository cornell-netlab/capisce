open Core

module VarMap = Map.Make (String)

(* VarSet keeps the bitwidth of each int. negative bitwidth is  *)              
type t = int VarMap.t

let empty = VarMap.empty
       
let rem (x : Var.t) (m : t) =
  Var.str x
  |> VarMap.remove m

let set (x : Var.t) (m : t) =
  VarMap.set m ~key:(Var.str x) ~data:(Var.size x)

let get (x : Var.t) (m : t) =
  let open Option.Let_syntax in
  let%map sz = VarMap.find m (Var.str x) in
  Var.(make (str x) sz)
  
let singleton (x : Var.t) = set x VarMap.empty

let to_list =
  VarMap.fold
    ~init:[]
    ~f:(fun ~key ~data acc ->
      Var.make key data :: acc
    )

let of_list = List.fold ~init:empty ~f:(Fn.flip set)
    
