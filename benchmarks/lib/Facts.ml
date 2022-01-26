open Core
   
module VarMap = Map.Make (Var) 

type t = Expr.t VarMap.t

let to_string f =
  VarMap.fold f ~init:"" ~f:(fun ~key ~data ->
      Printf.sprintf "  %s = %s\n%s"
        (Var.str key)
        (Expr.to_smtlib data)
    )
  |> Printf.sprintf "[\n%s]\n" 
  
  
       
let empty : t = VarMap.empty
       
let remove = VarMap.remove

let update f x e =
  VarMap.set f ~key:x ~data:e
  |> VarMap.filter ~f:(fun e ->
         List.exists ~f:(Var.(=) x) (Expr.vars e |> Util.uncurry (@))
       )

let lookup f x =
  match VarMap.find f x with
  | None -> Expr.var x
  | Some e -> e

let merge (f1 : t) (f2 : t) : t =
  VarMap.fold2 f1 f2 ~init:empty
    ~f:(fun ~key ~data acc ->
      match data with
      | `Left _ | `Right _ -> acc
      | `Both (a,b) ->
         if Expr.equal a b then
           VarMap.set acc ~key ~data:a
         else
           acc
    )
  
    
