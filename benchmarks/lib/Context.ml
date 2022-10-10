open Core
   
module VarMap = Map.Make (Var)

type t = int VarMap.t  

let empty : t = VarMap.empty
       
let set (x : Var.t) (i : int) (ctx : t) =
  VarMap.set ctx ~key:x ~data:i

let get (ctx : t) (x : Var.t) =
  match VarMap.find ctx x with
  | None -> 0
  | Some i -> i

let label (ctx : t) (x : Var.t)  =
  get ctx x
  |> Var.index x

let unlabel_if_max (ctx : t) (indexed : Var.t) =
  match Var.unindex indexed with
  | None ->
    failwithf "all variables should be indexed, but variable %s wasnt" (Var.str indexed) ()
  | Some (bare, chopped_idx) ->
    let max_idx = get ctx bare in
    if (chopped_idx = max_idx) then
      bare
    else
      indexed

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
