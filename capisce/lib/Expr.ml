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
  [@@deriving eq, sexp, hash, compare, quickcheck]

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

let bop_emit_p4 bop arg1 arg2 =
  let open Printf in 
  match bop with 
  | BAnd -> 
    sprintf "(%s & %s)" arg1 arg2
  | BOr ->
    sprintf "(%s | %s)" arg1 arg2
  | BXor -> 
    sprintf "(%s ^ %s)" arg1 arg2
  | BAdd -> 
    sprintf "(%s + %s)" arg1 arg2
  | BMul -> 
    sprintf "(%s * %s)" arg1 arg2
  | BSub -> 
    sprintf "(%s - %s)" arg1 arg2
  | BConcat -> 
    sprintf "(%s ++ %s)" arg1 arg2
  | BShl -> 
    sprintf "(%s << %s)" arg1 arg2
  | BAshr | BLshr -> 
    sprintf "(%s >> %s)" arg1 arg2


type uop =
  | UNot
  | UNeg
  | USlice of int * int (* lo, hi *)
  [@@deriving eq, sexp, hash, compare, quickcheck]

            
let uop_to_smtlib = function
  | UNot ->
    "bvnot"
  | UNeg -> 
    "bvneg"
  | USlice (lo, hi) ->
    (* Intentionally swap the order here*)
    Printf.sprintf "(_ extract %d %d)" hi lo    

let uop_emit_p4 uop arg =
  match uop with
  | UNot -> 
    "~" ^ arg
  | UNeg -> 
    "-" ^ arg
  | USlice (lo, hi) -> 
    Printf.sprintf "%s[%d:%d]" arg hi lo
    
type t =
  | BV of Bigint.t * int
  | Var of Var.t
  | BinOp of bop * t * t
  | UnOp of uop * t
  [@@deriving eq, sexp, hash, compare, quickcheck]

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

let rec emit_p4 = function
  | BV (n,w) -> Printf.sprintf "%dw%s" w (Bigint.to_string n)
  | Var v -> Var.str v
  | BinOp (op, e1, e2) -> 
    (bop_emit_p4 op)
      (emit_p4 e1)
      (emit_p4 e2)
  | UnOp (op, e) -> 
      (uop_emit_p4 op)
      (emit_p4 e)


let bv n w = BV (Bigint.(n % pow (succ one) (of_int w)), w)
let bvi n w = bv (Bigint.of_int n) w


let eval2 op e1 e2 =
  match e1, e2 with
  | BV(v1, w1), BV (v2, w2) ->
  begin match op with
      | BAnd ->
        bv Bigint.(v1 land v2) w1
      | BOr ->
        bv Bigint.(v1 lor v2) w1
      | BAdd ->
        bv Bigint.(v1 + v2) w1
      | BMul ->
        bv Bigint.(v1 * v2) w1
      | BSub ->
        bv Bigint.(v1 - v2) w1
      | BXor ->
        bv Bigint.(v1 lxor v2) w1
      | BConcat ->
        bv Bigint.((shift_left v1 w2) + v2) (w1 + w2)
      | BShl ->
        bv Bigint.(shift_left v1 (to_int_exn v2)) w1
      | BAshr ->
        bv Bigint.(v1 asr (to_int_exn v2)) w1
      | BLshr ->
        (* WARNING -- is this the right shift?*)
        bv Bigint.(shift_right v1 (to_int_exn v2)) w1
  end
  | _ -> BinOp(op, e1, e2)

let eval1 op e1 =
  match e1 with
  | BV(v1, w1) ->
      begin match op with
      | UNot ->
        bv Bigint.(lnot v1) w1
      | UNeg -> 
        bv (Bigint.(zero - (v1 % ((of_int 2 ** of_int w1) - one)))) w1
      | USlice (lo,hi) ->
        (* make [hi] exclusive for easier math *)
        let hi = hi + 1 in
        let width = hi - lo in
        let ones = Bigint.(((of_int 2) ** of_int width) - one) in
        bv Bigint.((shift_right v1 lo) land ones) (hi - lo)
      end
  | _ -> UnOp(op, e1)

let get_value = function
  | BV (v, w) -> Result.return (v,w)
  | e ->
    Printf.sprintf "Couldnt get value from non-BV expression: %s" (to_smtlib e)
    |> Result.fail

let eval (model : Model.t) expr : ((Bigint.t * int), string) Result.t =
  let open Result.Let_syntax in
  let rec loop e =
    match e with
    | BV (v,w) -> return (v,w)
    | Var x ->
      begin match Model.lookup model x with
        | None ->
          Printf.sprintf "Model is missing %s:\n%s"
            (Var.str x) (Model.to_string model)
          |> Result.fail
        | Some v ->
          return v
      end
    | UnOp (op, e) ->
      let%bind v,w = loop e in
      eval1 op (bv v w)
      |> get_value
    | BinOp (op, e1, e2) ->
      let%bind v1,w1 = loop e1 in
      let%bind v2,w2 = loop e2 in
      eval2 op (bv v1 w1) (bv v2 w2)
      |> get_value
  in
  loop expr

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
     | UNot | UNeg -> get_width e
     | USlice (lo,hi) -> hi - lo
          
let var v = Var v
let is_var = function
  | Var _ -> true
  | _ -> false

let get_const = function
  | BV (v,_) -> Some v
  | _ -> None

let is_one = function
  | BV (v,_) -> Bigint.(v = one)
  | _ -> false
let is_zero = function
  | BV (v,_) -> Bigint.(v = zero)
  | _ -> false
       
let get_var = function
  | Var x -> x
  | e -> failwith ("tried to get_var of a non-var expression " ^ to_smtlib e)

let rec fold_consts_opt e =
  let open Option.Let_syntax in
  match e with
  | BV _ -> Some e
  | Var _ -> None
  | BinOp (bop, e1, e2) ->
     begin match fold_consts_opt e1, fold_consts_opt e2 with
     | None, None -> None
     | Some e1, None -> Some (BinOp(bop, e1, e2))
     | None, Some e2 -> Some (BinOp(bop, e1, e2))
     | Some e1, Some e2 ->
        Some (eval2 bop e1 e2)
     end
  | UnOp (uop, e) ->
     let%map e = fold_consts_opt e in
     eval1 uop e
    
let fold_consts_default e =
  match fold_consts_opt e with
  | None -> e
  | Some e' ->
     (* Log.print @@ lazy( Printf.sprintf "[constant_folding] started with %s, got %s"
      *                      (to_smtlib e) (to_smtlib e'));  *)
     e'


let band e1 e2 =
  match e1, e2 with
  | BV(i,w), _ | _, BV(i,w)->
     if Bigint.(i = zero) then
       bv i w
     else
       BinOp(BAnd, e1, e2) |> fold_consts_default
  | _,_ ->
     BinOp(BAnd, e1, e2) |> fold_consts_default
     
let bor e1 e2 = BinOp(BOr, e1, e2) |> fold_consts_default
let badd e1 e2 = BinOp(BAdd, e1, e2) |> fold_consts_default
let bmul e1 e2 = BinOp(BMul, e1, e2) |> fold_consts_default
let bsub e1 e2 = BinOp(BSub, e1, e2) |> fold_consts_default
let bxor e1 e2 = BinOp(BXor, e1, e2) |> fold_consts_default
let bconcat e1 e2 = BinOp (BConcat, e1, e2) (*|> fold_consts_default*)

let rec nary op : t list -> t = function
  | [] -> failwith "cannot bvor 0 bvs, need at least one"
  | [e] -> e
  | e::es -> op e (nary op es)
 
let shl_ e1 e2 = BinOp(BShl, e1, e2) |> fold_consts_default
let ashr_ e1 e2 = BinOp(BAshr, e1, e2)|> fold_consts_default
let lshr_ e1 e2 = BinOp(BLshr, e1, e2)|> fold_consts_default             
                
let bnot e = UnOp(UNot, e)|> fold_consts_default
let bneg e = UnOp(UNeg, e) |> fold_consts_default
let bslice lo hi e =  UnOp(USlice(lo, hi), e) |> fold_consts_default        
let bcast width e =
  let ew = get_width e in
  if ew = width then
    e
  else if ew > width then
    bslice 0 (width - 1) e
  else
    bconcat (bvi 0 (width - ew)) e

let get_smart1 op =
  match op with
  | UNot -> bnot 
  | UNeg -> bneg
  | USlice(lo,hi) -> bslice lo hi

let get_smart2 op =
    match op with
    | BAnd -> band
    | BOr -> bor
    | BAdd -> badd
    | BMul -> bmul
    | BSub -> bsub
    | BXor -> bxor
    | BConcat -> bconcat
    | BShl -> shl_
    | BAshr -> ashr_
    | BLshr -> lshr_
  
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
 
let rec reassociate_bors_aux x e =
  match e with
  | Var x' when Var.(x' = x) ->
     (Some x, [])
  | Var y ->
     (None, [var y])
  | BinOp (BOr, e1, e2) ->
     let (found1, bors1) = reassociate_bors_aux x e1 in
     let (found2, bors2) = reassociate_bors_aux x e2 in
     let bors = (bors1 @ bors2) |> List.dedup_and_sort ~compare in 
     begin match found1, found2 with
     | None, None -> (None, bors)
     | Some x', Some x'' when Var.(x = x' && x = x'') ->
        (Some x, bors)
     | Some x', None when Var.(x = x') ->
        (Some x, bors)
     | None, Some x' when Var.(x = x')->
        (Some x, bors)
     | _,  _ ->
        failwith "bor-reassociate failed. Got the wrong variable name"
     end
  | _ ->
     (None, [e])

let reassociate_bors x e =
  match reassociate_bors_aux x e with
  | (None, _) -> None
  | (Some x', bor_list) when Var.(x' = x) ->
     if List.is_empty bor_list then
       None
     else
       Some (x', nary bor bor_list)
  | (Some _, _) ->
     failwith "bor-reassociate failed. got the wrong variable name"
  
     

(* returns true if (e11 != e12) /\ (e21 != e22) is contradictory *)               
let neq_contra (e11,e12) (e21, e22) =
  match e11, e12, e21, e22 with
  | Var x, BV (v,_), Var y, BV (u,_)
    | BV (v,_), Var x, Var y, BV (u,_)
    | BV (v,_), Var x, BV (u,_), Var y
    | Var x, BV (v,_), BV (u,_), Var y ->
     
     Var.equal x y && Var.size x = 1 && not (Bigint.(u = v))
  | _ ->
     false
               
let rec fun_subst f e =
  match e with
  | BV _ -> e
  | Var y -> f y
  | BinOp (op, e1, e2) ->
     get_smart2 op (fun_subst f e1) (fun_subst f e2)
  | UnOp (op, e) ->
     get_smart1 op (fun_subst f e)

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
     get_smart2 op e1' e2'
  | UnOp (op, e) ->
     let e' = normalize_names e in
     get_smart1 op e'
                
let rec size = function
  | BV (_, _) | Var _ -> 1
  | BinOp (_, e1, e2) -> size e1 + 1 + size e2
  | UnOp(_,e) -> 1 + size e

let rec width = function
  | BV(_, w) -> w
  | Var x -> Var.size x
  | UnOp(USlice (lo, hi), _) -> hi - lo + 1
  | UnOp(_, e) -> width e
  | BinOp(BConcat, e1, e2) -> width e1 + width e2
  | BinOp(_ , e1, e2) ->
     let w1 = width e1 in
     let w2 = width e2 in
     if w1 = w2 then
       w1
     else
       failwith "Type Error. sub expressions had different widths"
     
let rec label (ctx : Context.t) (e : t) =
  match e with
  | BV _ -> e
  | Var x -> Var (Context.label ctx x)
  | BinOp (bop,e1,e2) ->
     get_smart2 bop (label ctx e1) (label ctx e2)
  | UnOp (uop, e) ->
     get_smart1 uop (label ctx e)


let rec coerce_types gamma e =
  match e with
  | BV _ -> e
  | Var x ->
     begin match TypeContext.get x gamma with
     | Some y -> Var y
     | None -> Var x
     end
  | BinOp (bop, e1, e2) ->
     get_smart2 bop (coerce_types gamma e1) (coerce_types gamma e2)
  | UnOp (uop, e) ->
     get_smart1 uop (coerce_types gamma e)
     

let erase_max_label (ctx : Context.t) =
  let rec loop e =
    match e with
    | BV _ -> e
    | Var x ->
      Var (Context.unlabel_if_max ctx x)
    | BinOp (bop, e1, e2) ->
      get_smart2 bop (loop e1) (loop e2)
    | UnOp (uop, e) ->
      get_smart1 uop (loop e)
  in
  loop


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
