type bop =
  | BAnd
  | BOr
  | UAdd
  | UMul

let bop_to_smtlib = function
  | BAnd -> "bvand"
  | BOr -> "bvor"
  | UAdd -> "bvadd"
  | UMul -> "bvmul"
   
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
     

let rec to_smtlib = function
  | BV (n,w) ->
     Printf.sprintf "(_ bv%s %d)" (Bigint.to_string n) w
  | Var v ->
     Var.str v
  | BinOp (op, e1, e2) ->
     Printf.sprintf "(%s %s %s)"
       (bop_to_smtlib op)
       (to_smtlib e1)
       (to_smtlib e2)
  | Neg e ->
     Printf.sprintf "(bvnot %s)" (to_smtlib e)
