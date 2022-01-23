open Core
open Base_quickcheck   
   
type bop =
  | BAnd
  | BOr
  | BAdd
  | BMul
  | BSub
  | BXor
  | BConcat
  | BShl
  | BAshr
  | BLshr
  [@@deriving eq, sexp, compare, quickcheck]

let bop_to_smtlib = function
  | BAnd -> "bvand"
  | BOr -> "bvor"
  | BXor -> "bvxor"
  | BAdd -> "bvadd"
  | BMul -> "bvmul"
  | BSub -> "bvsub"
  | BConcat -> "concat"
  | BShl -> "bvshl"
  | BAshr -> "bvashr"
  | BLshr -> "bvlshr"

type uop =
  | UNot
  | USlice of int * int (* lo, hi *)
  [@@deriving eq, sexp, compare, quickcheck]
            
let uop_to_smtlib = function
  | UNot ->
     "bvnot"
  | USlice (lo, hi) ->
     (* Intentionally swap the order here*)
     Printf.sprintf "(_ extract %d %d)" hi lo

type t =
  | BV of Bigint.t * int
  | Var of Var.t
  | BinOp of bop * t * t
  | UnOp of uop * t
  [@@deriving eq, sexp, compare, quickcheck]

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
  | UnOp (op,e) ->
     Printf.sprintf "(%s %s)" (uop_to_smtlib op) (to_smtlib e)
          
let rec get_width = function
  | BV (_,w) -> w
  | Var x -> Var.size x
  | BinOp(op, e1, e2) ->
     begin match op with
     | BConcat ->
        get_width e1 + get_width e2
     | _ ->
        get_width e1
     end
  | UnOp(op, e) ->
     match op with
     | UNot -> get_width e
     | USlice (lo,hi) -> hi - lo
          
let bv n w = BV(n,w)
let bvi n w = bv (Bigint.of_int n) w
let var v = Var v
let is_var = function
  | Var _ -> true
  | _ -> false
let get_var = function
  | Var x -> x
  | e -> failwith ("tried to get_var of a non-var expression " ^ to_smtlib e)
  
let band e1 e2 =
  match e1, e2 with
  | BV(i,w), _ | _, BV(i,w)->
     if Bigint.(i = zero) then
       bv i w
     else
       BinOp(BAnd, e1, e2)
  | _,_ ->
     BinOp(BAnd, e1, e2)
     
let bor e1 e2 = BinOp(BOr, e1, e2)
let badd e1 e2 = BinOp(BAdd, e1, e2)              
let bmul e1 e2 = BinOp(BMul, e1, e2)
let bsub e1 e2 = BinOp(BSub, e1, e2)
let bxor e1 e2 = BinOp(BXor, e1, e2)
let bconcat e1 e2 = BinOp (BConcat, e1, e2)
let shl_ e1 e2 = BinOp(BShl, e1, e2)
let ashr_ e1 e2 = BinOp(BAshr, e1, e2)
let lshr_ e1 e2 = BinOp(BLshr, e1, e2)             
                
let bnot e = UnOp(UNot, e)
let bslice lo hi e =  UnOp(USlice(lo, hi), e)           
let bcast width e =
  let ew = get_width e in
  if ew = width then
    e
  else if ew > width then
    bslice 0 (width - 1) e
  else
    bconcat (bvi 0 (width - ew)) e
  
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
  if equal e1 e2 then
    Some true
  else match e1, e2 with
       | BV (v1,_), BV(v2,_) ->
          Some Bigint.(v1 = v2)
       | _, _ -> None

let rec fun_subst f e =
  match e with
  | BV _ -> e
  | Var y -> f y
  | BinOp (op, e1, e2) ->
     BinOp (op, fun_subst f e1, fun_subst f e2)
  | UnOp (op, e) ->
     UnOp (op, fun_subst f e)

let subst (x : Var.t) e0 e =
  fun_subst (fun y -> if Var.(x = y) then e0 else var y) e

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
  | UnOp (_,e) ->
     vars e    

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
  | UnOp(_, e) -> well_formed e

let rec normalize_names (e : t) : t =
  match e with
  | BV _ ->
     e
  | Var x ->
     Var (Var.normalize_name x)
  | BinOp(op, e1, e2) ->
     let e1' = normalize_names e1 in
     let e2' = normalize_names e2 in
     BinOp(op, e1', e2')
  | UnOp (op, e) ->
     let e' = normalize_names e in
     UnOp (op, e')
                
let rec size = function
  | BV (_, _) | Var _ -> 1
  | BinOp (_, e1, e2) -> size e1 + 1 + size e2
  | UnOp(_,e) -> 1 + size e


let rec label (ctx : Context.t) (e : t) =
  match e with
  | BV _ -> e
  | Var x -> Var (Context.label ctx x)
  | BinOp (bop,e1,e2) ->
     BinOp (bop, label ctx e1, label ctx e2)
  | UnOp (uop, e) ->
     UnOp (uop, label ctx e)
               

let quickcheck_generator_uop : uop Generator.t =
  let open Quickcheck.Generator in
  let open Let_syntax in
  union [
      return UNot
      (* (let%bind lo = filter Int.quickcheck_generator ~f:(fun lo -> lo >= 0 && lo < 31) in
       *  let%map hi = filter Int.quickcheck_generator ~f:(fun hi -> hi > lo && hi <= 32) in
       *  USlice (lo, hi)) *)
    ]

let quickcheck_generator_bop : bop Generator.t =
  let open Quickcheck.Generator in
  let open Let_syntax in
  union [
      return BAnd;
      return BOr;
      return BAdd;
      return BMul;
      return BSub;
      return BXor;
      (* return BConcat; *)
      return BShl;
      return BAshr;
      return BLshr  
    ]
               
let quickcheck_generator : t Generator.t =
  let open Quickcheck.Generator in
  let open Let_syntax in
  recursive_union
    [
      (let%map n = filter Bigint.quickcheck_generator ~f:(fun i -> Bigint.(i > zero && i < pow (of_int 2) (of_int 32))) in
       bv n 32);
      
      (let%map v = Var.quickcheck_generator in
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
      let un =
        let%bind e = self in
        let%map op =quickcheck_generator_uop in
        UnOp(op,e)
      in
      [bin; un]
    )

let quickcheck_shrinker : t Shrinker.t = Shrinker.atomic    
