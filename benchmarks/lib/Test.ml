open Core
   
type bop =
  | LAnd
  | LOr
  | LArr
  [@@deriving eq]

let bop_to_smtlib = function
  | LAnd -> "and"
  | LOr -> "or"
  | LArr -> "=>"

type t =
  | TFalse
  | TTrue
  | TNot of t
  | TBin of bop * t * t
  | TEq of Expr.t * Expr.t
  | Forall of Var.t list * t
  | Exists of Var.t list * t
  [@@deriving eq]

let (=) = equal
            
let false_ = TFalse
let true_ = TTrue
let not_ b = TNot b
let and_ b1 b2 = TBin(LAnd, b1, b2)
let or_ b1 b2 = TBin(LOr, b1, b2)
let imp_ b1 b2 = TBin(LArr, b1, b2)
let eq_ e1 e2 = TEq(e1,e2)
let forall vs b = Forall(vs, b)
let exists vs b = Exists(vs, b)                                  
            
let rec to_smtlib = function
  | TFalse -> "false"
  | TTrue -> "true"
  | TNot t -> Printf.sprintf "(not %s)" (to_smtlib t)
  | TBin (b,t1,t2) ->
     Printf.sprintf "(%s %s %s)" (bop_to_smtlib b) (to_smtlib t1) (to_smtlib t2)
  | TEq (e1,e2) ->
     Printf.sprintf "(= %s %s)" (Expr.to_smtlib e1) (Expr.to_smtlib e2)
  | Forall (vs, t) ->
     Printf.sprintf "(forall (%s) %s)"
       (Var.list_to_smtlib_quant vs)
       (to_smtlib t)
  | Exists (vs, t) ->
     Printf.sprintf "(exists (%s) %s)"
       (Var.list_to_smtlib_quant vs)
       (to_smtlib t)
                    
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
     

let index_subst s_opt t : t =
  match s_opt with
  | None -> t    
  | Some s -> 
     Subst.to_vsub_list s
     |> List.fold ~init:t
          ~f:(fun t (x,x') -> subst x (Expr.var x') t)
