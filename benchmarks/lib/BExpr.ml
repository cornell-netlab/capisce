open Base_quickcheck
open Core
   
type bop =
  | LAnd
  | LOr
  | LArr
  [@@deriving eq, sexp, compare, quickcheck]

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
  [@@deriving eq, sexp, compare, quickcheck]

let (=) = equal
            
let false_ = TFalse
let true_ = TTrue
let not_ = function
  | TFalse -> true_
  | TTrue -> false_
  | TNot b -> b
  | b -> TNot b
let and_ b1 b2 = if b1 = true_ then b2 else if b2 = true_ then b1 else TBin(LAnd, b1, b2)
let or_ b1 b2 = if b1 = false_ then b2 else if b2 = false_ then b1 else TBin(LOr, b1, b2)
let imp_ b1 b2 =
  if b2 = true_ || b1 = false_ then
    true_
  else if b2 = false_ then
    not_ b1
  else if b1 = true_ then
    b2
  else
    TBin(LArr, b1, b2)
let eq_ e1 e2 =
  match Expr.static_eq e1 e2 with
  | None -> TEq(e1,e2)
  | Some true -> true_
  | Some false -> false_

let get_smart = function
  | LAnd -> and_
  | LOr -> or_
  | LArr -> imp_

let rec vars t : Var.t list * Var.t list =
  match t with
  | TFalse
    | TTrue -> ([],[])
  | TNot t -> vars t
  | TBin (_, t1, t2) ->
     Var.(Util.pairs_app_dedup ~dedup (vars t1) (vars t2))
  | TEq (e1, e2) ->
     Var.(Util.pairs_app_dedup ~dedup (Expr.vars e1) (Expr.vars e2))     
  | _ ->
     failwith "cannot compute vars from foralls/exists"

    
let rec forall vs b =
  if List.is_empty vs then
    b
  else    
    let bvs = Util.uncurry (@) (vars b) in
    let vs' = Var.(Util.linter ~equal vs bvs) in
    if List.is_empty vs' then
      b
    else
      match b with
      | TFalse -> false_
      | TTrue -> true_
      | TNot (TEq(e1,e2)) | TEq (e1, e2) when Expr.uelim vs' e1 e2 ->
         false_
      | TBin (op, b1, b2) ->
         begin match op with
         | LArr | LOr ->
            let open Util in
            let frees1 = vars b1 |> uncurry (@) in
            let frees2 = vars b2 |> uncurry (@) in
            (* vs_ni is the (v)ariable(s) in vs' that do (n)ot occur in bi  *)            
            let vs_n1 = Var.(ldiff ~equal vs' frees1) in
            let vs_n2 = Var.(ldiff ~equal vs' frees2) in
            (* vs'' is the variables that occur in both b1 and b2*)
            let vs'' = Var.(linter ~equal frees1 frees2) in
            (* vsi is the variables that occur only in vsi *)
            let vs2 = Var.(ldiff ~equal vs_n1 vs'') in
            let vs1 = Var.(ldiff ~equal vs_n2 vs'') in
            (* its the case that vs' = vs'' @ vs2 @ vs1 *)
            (* This is a simple sanity check *)
            assert(Int.(List.length vs' = List.length(vs'' @ vs2 @ vs1)));
            forall_simplify vs'' op (forall vs1 b1) (forall vs2 b2)
         | LAnd -> and_ (forall vs b1) (forall vs b2)
         end
      | Forall(vs'', b') -> forall (Var.dedup (vs' @ vs'')) b'
      | _ ->
         Forall(vs,b)
and forall_simplify vs op a b =
  forall vs @@
    match op with
    | LAnd -> and_ a b
    | LArr -> or_ (not_ a) b
    | LOr -> or_ a b
    
let exists vs b = Exists(vs, b)

let rec simplify = function
  | TFalse -> TFalse
  | TTrue -> TTrue
  | TNot b -> not_ (simplify b)
  | TBin (op, b1, b2) -> get_smart op (simplify b1) (simplify b2)
  | TEq (e1, e2) -> eq_ e1 e2
  | Forall (vs, b) -> forall vs b
  | Exists (vs, b) -> exists vs b
            
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
  | TNot t -> not_ (subst x e t)
  | TBin (op, t1,t2) -> (get_smart op) (subst x e t1) (subst x e t2)
  | TEq (e1,e2) ->
     eq_ (Expr.subst x e e1) (Expr.subst x e e2)
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
     

let index_subst s_opt t : t =
  match s_opt with
  | None -> t    
  | Some s -> 
     Subst.to_vsub_list s
     |> List.fold ~init:t
          ~f:(fun t (x,x') -> subst x (Expr.var x') t)

let quickcheck_generator : t Generator.t =
  let open Quickcheck.Generator in
  let open Let_syntax in
  recursive_union
    [
      singleton TFalse;
      singleton TTrue;
      (let%bind e1 = Expr.quickcheck_generator in
       let%map e2 = Expr.quickcheck_generator in
       TEq(e1,e2))
    ]
    ~f:(fun self ->
      [
        (let%map e = self in TNot e);

        (let%bind op = quickcheck_generator_bop in
         let%bind b1 = self in
         let%map b2 = self in
         Printf.printf "Generate LHS %s RHS %s\n%!" (to_smtlib b1) (to_smtlib b2);         
         TBin (op,b1,b2)
        );

        (let%bind v = Var.quickcheck_generator in
         let%map b = self in
         Forall ([v], b));

        (let%bind v = Var.quickcheck_generator in
         let%map b = self in
         Exists ([v], b)
        )
      ]
    )                                    
  

let rec well_formed b =
  match b with
  | TTrue | TFalse -> true
  | TEq (e1,e2) -> Expr.well_formed e1 && Expr.well_formed e2
  | TBin(_,b1,b2) -> well_formed b1 && well_formed b2
  | TNot b | Forall (_,b) | Exists(_,b) -> well_formed b 
  
