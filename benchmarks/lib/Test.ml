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
                    
let rec subst x e t =
  match t with
  | TFalse | TTrue -> t
  | TNot t -> subst x e t
  | TBin (op, t1,t2) -> TBin(op, subst x e t1, subst x e t2)
  | TEq (e1,e2) ->
     TEq(Expr.subst x e e1, Expr.subst x e e2)
      
      
                      
