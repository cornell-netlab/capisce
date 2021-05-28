type bop =
  | BAnd
  | BOr
  | BXor
  | UAdd
  | USub
  | UMul
   
   
type t =
  | BV of Bigint.t * int
  | Var of Var.t
  | BinOp of bop * t * t
  | Neg of t

let rec subst (x : Var.t) e0 e =
  match e with
  | BV _ -> e
  | Var y ->
     if Var.(y = x) then
       e0
     else
       Var y
  | BinOp (op, e1, e2) ->
     BinOp(op, subst x e0 e1, subst x e0 e2)
  | Neg e ->
     Neg (subst x e0 e)


let rec vars e =
  match e with
  | BV _ -> ([],[])
  | Var y ->
     if Var.is_ghost y || Var.is_symbRow y then
       ([],[y])
     else
       ([y],[])
  | BinOp (_, e1, e2) ->
     Util.pairs_app_dedup ~dedup:Var.dedup (vars e1) (vars e2)
  | Neg e ->
     vars e
     
