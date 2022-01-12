open Core
   
module VarMap = Map.Make (Var)

type t = int VarMap.t  

let empty : t = VarMap.empty
       
let set (x : Var.t) (i : int) (ctx : t) =
  VarMap.set ctx ~key:x ~data:i

let label (ctx : t) (x : Var.t)  =
  match VarMap.find ctx x with
  | None ->
     Var.index x 0
  | Some i ->
     Var.index x i

let increment ctx x =
  VarMap.update ctx x ~f:(function
      | None -> 1
      | Some i -> i + 1 
    )

let merge ctx1 ctx2 ~init ~update =
  VarMap.fold2 ctx1 ctx2 ~init:(empty, init, init)
    ~f:(fun ~key ~data (ctx, lresid, rresid) ->
      match data with
      | `Left i ->
         (set key i ctx, lresid, update key 0 i rresid)
      | `Right i ->
         (set key i ctx, update key 0 i lresid, rresid)
      | `Both (l, r) ->
         (set key (max l r) ctx,
          update key l r lresid,
          update key r l rresid)
    )
