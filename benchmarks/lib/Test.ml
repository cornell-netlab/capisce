open Core
   
type bop =
  | LAnd
  | LOr
  | LArr

type t =
  | TFalse
  | TTrue
  | TNot of t
  | TBin of bop * t * t
  | TEq of Expr.t * Expr.t
  | Forall of Var.t list * t
  | Exists of Var.t list * t
         
                    
let rec subst x e t =
  match t with
  | TFalse | TTrue -> t
  | TNot t -> subst x e t
  | TBin (op, t1,t2) -> TBin(op, subst x e t1, subst x e t2)
  | TEq (e1,e2) ->
     TEq(Expr.subst x e e1, Expr.subst x e e2)
  | Forall (vs, t) ->
     if List.exists vs ~f:(Var.(=) x) then
       Forall (vs, t)
     else
       Forall(vs, subst x e t)
  | Exists (vs, t) ->
     if List.exists vs ~f:(Var.(=) x) then
       Exists (vs, t)
     else
       Exists (vs, subst x e t)         
    
let rec vars t =
  match t with
  | TFalse
    | TTrue -> ([],[])
  | TNot t -> vars t
  | TBin (_, t1, t2) ->
     Util.pairs_app_dedup ~dedup:Var.dedup (vars t1) (vars t2)
  | TEq (e1, e2) ->
     Util.pairs_app_dedup ~dedup:Var.dedup (Expr.vars e1) (Expr.vars e2)     
  | _ ->
     failwith "cannot compute vars from foralls/exists"
     
