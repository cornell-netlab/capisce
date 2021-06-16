open Core

type t =
  | Assume of Test.t
  | Assert of Test.t
  | Havoc of Var.t
  | Assign of Var.t * Expr.t
  | Seq of t * t
  | Choice of t * t

(** Smart Constructors *)
let assume t = Assume t
let assert_ t = Assert t
let havoc x = Havoc x
let assign x e = Assign (x,e)
let seq c1 c2 = Seq(c1,c2)
let choice c1 c2 = Choice(c1,c2)              
            
let rec sequence cs =
  match cs with
  | [] -> failwith "sequence cannot be passed an empty list"
  | [c] -> c
  | c::cs -> Seq(c, sequence cs)
  (* List.fold cs ~init:(Assume Test.true_) ~f:(fun acc c -> Seq(acc,c)) *)

let negate = function
  | Assume t -> Assume (Test.not_ t)
  | Assert t -> Assert (Test.not_ t)
  | _ -> failwith "Can only negate an assumption or assertion"

(**/ END Smart Constructors*)            


            
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
          
let ghost_copy id k =
  let open Test in
  let open Expr in
  eq_ (var (Var.make_ghost id k)) (var k)

let match_key id k =
  let open Test in
  let open Expr in
  let v = Var.make_symbRow id k in
  (* let km = Var.(make (str k ^ "_match") (size k)) in
   * let m = Var.make_symbRow id km in *)
  (* eq_
   *   (band (var v) (var m))
   *   (band (var k) (var m))  *)
  eq_ (var v) (var k)

let matchrow id ks =
  let open Test in
  List.fold ks ~init:true_
    ~f:(fun acc k -> match_key id k |> and_ acc)  

let ghost_hit id =
  let open Expr in 
  let miss_var = Var.make "miss" 1 |> Var.make_ghost id in
  Test.eq_ (var miss_var) (bv Bigint.one 1)

let ghost_miss id =
  Test.not_ (ghost_hit id)

let row_action tid act_id n =
  let open Expr in 
  let v = Var.make_symbRow tid (Var.make "action" n) in
  Test.eq_ (var v) (bv (Bigint.of_int act_id) n)

let row_id tid =
  let open Expr in
  let g = Var.make_ghost tid (Var.make "hitAction" 32) in
  let r = Var.make_symbRow tid (Var.make "id" 32) in
  Test.eq_ (var g) (var r)

let action_subst tid (x, c) =
  let r_data = Var.make_symbRow tid x in
  subst x (Expr.var r_data) c
  
  
let table (id : int) (ks : Var.t list) (acts : (Var.t * t) list) (def : t) : t =
  let open Test in
  let gs = List.fold ks ~init:true_ ~f:(fun acc k -> ghost_copy id k |> and_ acc) in
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
  
      
let rec wp c t =
  let open Test in
  match c with
  | Assume t1 -> imp_ t1 t
  | Assert t1 -> and_ t1 t
  | Havoc x -> forall [x] t
  | Assign (x,e) -> Test.subst x e t
  | Seq (c1,c2) ->  wp c2 t |> wp c1
  | Choice (c1,c2) -> and_ (wp c1 t) (wp c2 t)                        
    
