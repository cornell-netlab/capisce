open Core

type t =
  | Assume of Test.t
  | Assert of Test.t
  | Havoc of Var.t
  | Assign of Var.t * Expr.t
  | Seq of t * t
  | Choice of t * t

(* PRE: x is not an lvalue in c *)            
let rec subst x e c =
  match c with
  | Assume t -> Assume (Test.subst x e t)
  | Assert t -> Assume (Test.subst x e t)
  | Havoc y ->
     if Var.(x = y) then
       failwith "tried to substitute an lvalue"
     else
       c
  | Assign (y, e') ->
     if Var.(x = y) then
       failwith "tried to substitute an lvalue"
     else
       Assign (y, Expr.subst x e e')
  | Seq (c1, c2) ->
     Seq(subst x e c1, subst x e c2)
  | Choice (c1, c2) ->
     Choice (subst x e c1, subst x e c2)
            

let sequence cs =
  List.fold cs ~init:(Assume TTrue) ~f:(fun acc c -> Seq(acc,c))
            
let ghost = "gamma"
let ghost_var id k =
  let x = Printf.sprintf "%s_%d__%s" ghost id (Var.str k) in
  let w = Var.size k in
  Var.make x w
          
let ghost_copy id k =
  let open Test in
  TEq(Var(ghost_var id k),Var k)

let symbRow = "rho"

let symbRow_var id k =            
  let x = Printf.sprintf "%s_%d__%s" symbRow id (Var.str k)in
  let w = Var.size k in
  Var.make x w
            
let match_key id k =
  let open Test in
  let v = symbRow_var id k in
  let km = Var.(make (str k ^ "_match") (size k)) in
  let m = symbRow_var id km in
  TEq(BinOp(BAnd, Var v, Var m), BinOp(BAnd, Var k, Var m)) 

let matchrow id ks =
  let open Test in
  List.fold ks ~init:TTrue
    ~f:(fun acc k -> TBin(LAnd, acc, match_key id k))  

let ghost_hit id =
  let miss_var = Var.make "miss" 1 |> ghost_var id in
  Test.TEq(Var miss_var, Expr.BV(Bigint.one, 1))

let ghost_miss id =
  Test.TNot (ghost_hit id)

let row_action tid act_id n =
  let v = symbRow_var tid (Var.make "action" n) in
  Test.TEq(Var v, Expr.BV(Bigint.of_int act_id, n))

let row_id tid =  
  let g = ghost_var tid (Var.make "hitAction" 32) in
  let r = symbRow_var tid (Var.make "id" 32) in
  Test.TEq(Var g, Var r)

let action_subst tid (x, c) =
  let r_data = symbRow_var tid x in
  subst x (Var r_data) c
  
  
let table (id : int) (ks : Var.t list) (acts : (Var.t * t) list) (def : t) : t =
  let open Test in
  let gs = List.fold ks ~init:TTrue ~f:(fun acc k -> TBin(LAnd, acc, ghost_copy id k) ) in
  let hit act_id act =
    [Assume (matchrow id ks);
     Assume (ghost_hit id);
     Assume (row_action id act_id (List.length acts));
     Assume (row_id id);
     action_subst id act 
    ] |> sequence
  in
  let default = Seq(Assume (ghost_miss id), def) in
  let actions = List.foldi acts ~init:default ~f:(fun i acc act -> Choice(acc,hit i act)) in
  Seq(Assume gs, actions)
  
      
