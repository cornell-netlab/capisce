open Core

type t =
  | Assume of BExpr.t
  | Assert of (BExpr.t * int option)
  | Havoc of Var.t
  | Assign of Var.t * Expr.t
  | Seq of t * t
  | Choice of t * t
  [@@deriving eq]

let rec to_string_aux indent (c : t) : string =
  let open Printf in
  let space = Util.space indent in
  match c with
  | Assume t -> sprintf "%sassume %s" space (BExpr.to_smtlib t)
  | Assert (t,_) -> sprintf "%sassert %s" space (BExpr.to_smtlib t)
  | Assign (x,e) -> sprintf "%s%s := %s" space (Var.str x) (Expr.to_smtlib e)
  | Havoc x -> sprintf "%shavoc %s" space (Var.str x)
  | Seq (c1,c2) ->
     sprintf "%s;\n%s" (to_string_aux indent c1) (to_string_aux indent c2)
  | Choice (c1,c2) ->
     sprintf "%s{\n%s\n%s} [] {\n%s\n%s}" space (to_string_aux (indent+2) c1) space (to_string_aux (indent+2) c2) space

let to_string = to_string_aux 0    
    

(** Smart Constructors *)
let skip = Assume (BExpr.true_)            
let assume t = Assume t
let assert_ t = Assert (t,None)
let havoc x = Havoc x
let assign x e = Assign (x,e)
let seq c1 c2 =
  if equal c2 skip then
    c1
  else if equal c1 skip then
    c2
  else
    Seq(c1,c2)
let choice c1 c2 = Choice(c1,c2)              
            
let rec sequence cs =
  match cs with
  | [] -> skip
  | [c] -> c
  | c::cs -> Seq(c, sequence cs)

let negate = function
  | Assume t -> Assume (BExpr.not_ t)
  | Assert (t,i) -> Assert ((BExpr.not_ t), i)
  | _ -> failwith "Can only negate an assumption or assertion"

let choice_seq cs1 cs2 = choice (sequence cs1) (sequence cs2)  

let choice_seqs cs =
  List.fold cs ~init:(assume BExpr.false_)
    ~f:(fun c cs -> choice c (sequence cs))
       
(**/ END Smart Constructors*)            


            
(* PRE: x is not an lvalue in c *)            
let rec subst x e c =
  match c with
  | Assume t -> Assume (BExpr.subst x e t)
  | Assert (t,i) -> Assert (BExpr.subst x e t, i)
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
          
(* let ghost_copy id k =
 *   let open BExpr in
 *   let open Expr in
 *   eq_ (var (Var.make_ghost id k)) (var k) *)

let match_key id k =
  let open BExpr in
  let open Expr in
  let v = Var.make_symbRow id k in
  (* let km = Var.(make (str k ^ "_match") (size k)) in
   * let m = Var.make_symbRow id km in *)
  (* eq_
   *   (band (var v) (var m))
   *   (band (var k) (var m))  *)
  eq_ (var v) (var k)

let matchrow id ks =
  let open BExpr in
  List.fold ks ~init:true_
    ~f:(fun acc k -> match_key id k |> and_ acc)  

let assign_key id k =
  let open Expr in
  let v = Var.make_symbRow id k in
  (* let km = Var.(make (str k ^ "_match") (size k)) in
   * let m = Var.make_symbRow id km in *)
  (* eq_
   *   (band (var v) (var m))
   *   (band (var k) (var m))  *)
  assign k (var v)

let assignrow id ks =
  List.map ks ~f:(assign_key id)
  |> sequence 

  
(* let ghost_hit id =
 *   let open Expr in 
 *   let miss_var = Var.make "miss" 1 |> Var.make_ghost id in
 *   BExpr.eq_ (var miss_var) (bv Bigint.one 1)
 * 
 * let ghost_miss id =
 *   BExpr.not_ (ghost_hit id) *)

let row_action tid act_id n =
  let open Expr in
  let v = Var.make_symbRow tid (Var.make "action" n) in
  BExpr.eq_ (var v) (bv (Bigint.of_int act_id) n)

(* let row_id tid =
 *   let open Expr in
 *   let g = Var.make_ghost tid (Var.make "hitAction" 32) in
 *   let r = Var.make_symbRow tid (Var.make "id" 32) in
 *   BExpr.eq_ (var g) (var r) *)

let action_subst tid (x_opt, c) =
  match x_opt with
  | None ->
     c
  | Some x ->
     let r_data = Var.make_symbRow tid x in
     subst x (Expr.var r_data) c
  
  
let table (id : int) (ks : Var.t list) (acts : (Var.t option * t) list) : t =
  let read_keys = matchrow id ks in
  let assign_keys = assignrow id ks in
  let hit act_id act =
    [Assume (row_action id act_id (List.length acts));
     action_subst id act ]
  in
  let actions = List.foldi acts ~init:[] ~f:(fun i acc act -> (hit i act)::acc) in
  [Assume read_keys;
   if false then assign_keys else skip;
   choice_seqs actions]
  |> sequence 
  


(* let rec vars c : Var.t list =
 *   match c with
 *   | Assume t | Assert (t,_) ->
 *      Util.uncurry ((@)) (BExpr.vars t)
 *   | Havoc _ -> []
 *   | Assign (x,e) ->
 *      x :: Util.uncurry ((@)) (Expr.vars e)     
 *   | Seq (c1,c2) | Choice (c1,c2) ->
 *      vars c1 @ vars c2
 *      |> List.dedup_and_sort ~compare:Var.compare  *)
  
  
  
(* let zip_eq (l1 : (Var.t * Var.t) list) =
 *   let open List.Let_syntax in
 *   let%map (v1, v2) = l1 in
 *   BExpr.eq_ (Expr.var v1) (Expr.var v2)
 *   |> assume 
 *   
 *                     
 * (\** PRE, Assume s1 and s2 are defined on the same set of variables*\)
 * let merge (s1 : Subst.t option) (s2 : Subst.t option) : (Subst.t option * t * t) =
 *   match s1, s2 with
 *   | None, None -> None, skip, skip
 *   | Some _, None -> s1, skip, skip
 *   | None, Some _ -> s2, skip, skip
 *   | Some sa, Some sb ->
 *      let s' = Subst.max sa sb in
 *      let ra = Subst.sync sa s' |> zip_eq |> sequence in
 *      let rb = Subst.sync sb s' |> zip_eq |> sequence in
 *      (Some s', ra, rb) *)
                    
(* let rec passify (s0 : Subst.t option) c : (Subst.t option * t) option =
 *   let open Option.Let_syntax in
 *   match c with
 *   | Assert (t,_) ->
 *      if BExpr.(t = false_) then
 *        return (None, assert_ (BExpr.false_))
 *      else
 *        return (s0, assert_ (BExpr.index_subst s0 t))
 *   | Assume t ->
 *      if BExpr.(t = false_) then
 *        return (None, assume (BExpr.false_))
 *      else
 *        return (s0, assume (BExpr.index_subst s0 t))
 *   | Havoc x ->
 *      return (s0, havoc x)
 *   | Assign (x, e) ->
 *      let%map x', s1 = Subst.incr s0 x in
 *      (Some s1, assume (BExpr.eq_ (Expr.var x') (Expr.index_subst s0 e)))
 *   | Seq (c1,c2) ->
 *      let%bind s1, c1'  = passify s0 c1 in
 *      let%bind s2, c2' = passify s1 c2 in
 *      return (s2, seq c1' c2')
 *   | Choice (c1, c2) ->
 *      let%bind s1, c1' = passify s0 c1 in
 *      let%bind s2, c2' = passify s0 c2 in
 *      let s3, r1, r2 = merge s1 s2 in
 *      return (s3, choice (seq c1' r1) (seq c2' r2))
 * 
 * let rec norm_execs = function
 *   | Assert (t,_) 
 *     | Assume t -> t
 *   | Assign _ -> failwith "Assigns are not permitted in passive form"                
 *   | Havoc _ -> failwith "HAVOCS ARE CONFUSING"
 *   | Seq (c1,c2) -> BExpr.and_ (norm_execs c1) (norm_execs c2)
 *   | Choice (c1,c2) -> BExpr.or_ (norm_execs c1) (norm_execs c2)
 *   
 * let rec bad_execs = function
 *   | Assert (t,_) -> BExpr.not_ t
 *   | Assume _ -> BExpr.false_
 *   | Assign _ -> failwith "Assigns are not permitted in passive form"
 *   | Havoc _ -> failwith "HAVOCS ARE CONFUSING"
 *   | Seq (c1, c2) -> BExpr.(or_ (bad_execs c1) (and_ (norm_execs c1) (bad_execs c2)))
 *   | Choice (c1, c2) -> BExpr.or_ (bad_execs c1) (bad_execs c2)
 *      
 * let wp c t =
 *   let s = Subst.init (vars c) in  
 *   match passify (Some s) c with
 *   | None -> failwith "couldn't compute the passive form of the program"
 *   | Some (_,p)->
 *      Log.print (to_string p);
 *      let open BExpr in  
 *      and_ (imp_ (norm_execs p) t)
 *           (not_ (bad_execs p)) *)

let rec wp c t =
  let open BExpr in
  match c with
  | Assume t1 -> imp_ t1 t
  | Assert (t1,_) -> and_ t1 t
  | Havoc x -> forall [x] t
  | Assign (x,e) -> BExpr.subst x e t
  | Seq (c1,c2) ->  wp c2 t |> wp c1
  | Choice (c1,c2) -> and_ (wp c1 t) (wp c2 t)
     
let rec number_asserts c i =
  match c with 
  | Assert (t,_) -> Assert (t, Some i), i+1
  | Assume _ | Havoc _ | Assign _ -> c, i
  | Seq (c1,c2) ->
     let c1', i' = number_asserts c1 i in
     let c2', i'' = number_asserts c2 i' in
     seq c1' c2', i''
  | Choice (c1,c2) ->
     let c1', i' = number_asserts c1 i in
     let c2', i'' = number_asserts c2 i' in
     choice c1' c2', i''

let rec keep_assert_with_id c id =
  match c with 
  | Assert (t,Some i) when i = id -> Assert (t, Some id)
  | Assert _ -> Assume BExpr.true_
  | Assume _ | Havoc _ | Assign _ -> c
  | Seq (c1,c2) ->
     seq
       (keep_assert_with_id c1 id)
       (keep_assert_with_id c2 id)
  | Choice (c1,c2) ->
     choice
       (keep_assert_with_id c1 id)
       (keep_assert_with_id c2 id)
     
let assert_slices c =
  let c', i = number_asserts c 0 in
  List.map (Util.range (i-1)) ~f:(keep_assert_with_id c')
