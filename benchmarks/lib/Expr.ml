open Core
open Base_quickcheck   
   
type bop =
  | BAnd
  | BOr
  | UAdd
  | UMul
  | USub
  [@@deriving eq, sexp, compare, quickcheck]

let bop_to_smtlib = function
  | BAnd -> "bvand"
  | BOr -> "bvor"
  | UAdd -> "bvadd"
  | UMul -> "bvmul"
  | USub -> "bvsub"
   
type t =
  | BV of Bigint.t * int
  | Var of Var.t
  | BinOp of bop * t * t
  | Neg of t
  [@@deriving eq, sexp, compare, quickcheck]

let bv n w = BV(n,w)
let bvi n w = bv (Bigint.of_int n) w
let var v = Var v
let band e1 e2 = BinOp(BAnd, e1, e2)
let bor e1 e2 = BinOp(BOr, e1, e2)
let badd e1 e2 = BinOp(UAdd, e1, e2)              
let bmul e1 e2 = BinOp(UMul, e1, e2)
let bsub e1 e2 = BinOp(USub, e1, e2)
let bneg e = Neg e

let uelim sign vs e1 e2 =
  let open Var in 
  match sign, e1, e2 with
  | _, BV _, Var v | _, Var v, BV _ ->
     Var.(Util.lmem ~equal v vs) 
  | _, Var v, Var v' ->
     not (Var.(v = v')) && (not @@ List.is_empty @@ Util.linter ~equal [v;v'] vs)
  | `Neq, (BinOp (BAnd,Var v1,Var vm)), (BinOp (BAnd, Var vk, Var vm')) ->
     let open Var in
     vm = vm'
     && is_symbRow vk
     && Util.lmem ~equal v1 vs  
  | _ ->
     false
               
let static_eq e1 e2 =
  match e1, e2 with
  | BV (v1,_), BV(v2,_) ->
     Some Bigint.(v1 = v2)
  | _, _ -> None
               
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


let rec vars e : (Var.t list * Var.t list) =
  match e with
  | BV _ -> ([],[])
  | Var y ->
     if Var.is_symbRow y then
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


let index_subst s_opt e =
  match s_opt with
  | None -> e    
  | Some s -> 
     Subst.to_vsub_list s
     |> List.fold ~init:e
          ~f:(fun e (x,x') -> subst x (var x') e)

let rec well_formed = function
  | BV (_,i) -> i > 0
  | Var v -> Var.well_formed v
  | BinOp (_, e1, e2) -> well_formed e1 && well_formed e2
  | Neg e -> well_formed e


let rec size = function
  | BV (_, _) | Var _ -> 1
  | BinOp (_, e1, e2) -> size e1 + 1 + size e2
  | Neg e -> 1 + size e 
           
let quickcheck_generator : t Generator.t =
  let open Quickcheck.Generator in
  let open Let_syntax in
  recursive_union
    [
      (let%map n = filter Bigint.quickcheck_generator ~f:(fun i -> Bigint.(i > zero && i < pow (of_int 2) (of_int 32))) in
       bv n 32);
      
      (let%map v = Var.quickcheck_generator in
       Printf.printf "Expr Generated %s\n%!" (Var.list_to_smtlib_quant [v]);
       Var v
      );
    ]
    ~f:(fun self ->
      let bin =
        let%bind e1 = self in
        let%bind e2 = self in
        let%map op = quickcheck_generator_bop in
        BinOp (op, e1, e2) 
      in
      let neg = map self ~f:bneg in
      [bin; neg]
    )

let quickcheck_shrinker : t Shrinker.t = Shrinker.atomic    
