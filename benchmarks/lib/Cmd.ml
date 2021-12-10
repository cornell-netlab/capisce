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

let match_key (id : string) k =
  let open BExpr in
  let open Expr in
  let v = Var.make_symbRow_str id k in
  eq_ (var v) (var k)

let matchrow (id : string) ks =
  let open BExpr in
  List.fold ks ~init:true_
    ~f:(fun acc k -> match_key id k |> and_ acc)  

let assign_key (id : string) k =
  let open Expr in
  let v = Var.make_symbRow_str id k in
  assign k (var v)

let assignrow id ks =
  List.map ks ~f:(assign_key id)
  |> sequence 

let row_action (tid : string) act_id n =
  let open Expr in
  let v = Var.make_symbRow_str tid (Var.make "action" n) in
  BExpr.eq_ (var v) (bv (Bigint.of_int act_id) n)

let action_subst (tid : string) (x_opt, c) =
  match x_opt with
  | None ->
     c
  | Some x ->
     let r_data = Var.make_symbRow_str tid x in
     subst x (Expr.var r_data) c

(** [mint_keyvar t i w] is a Var.t of width [w] corresponding to the [i]th key
   in table [t]*)     
let mint_keyvar t i w =
  let name = Printf.sprintf "_%s_key_$%d" t i in
  Var.make name w
     
let rec mint_key_names_aux idx assignments varkeys tbl_name ks =
  match ks with
  | [] -> (assignments, varkeys)
  | (kwidth, kexpr)::ks' ->
     (* mint key *)
     let v = mint_keyvar tbl_name idx kwidth in
     (* update recursive state *)
     let idx' = idx + 1 in
     let assignments' = assign v kexpr :: assignments in
     let varkeys' = v :: varkeys in
     (* make recusive call with updated state *)
     mint_key_names_aux idx' assignments' varkeys' tbl_name ks'
     
(** [mint_key_names tbl_name keys] is a pair of lists [(as,vs)] where [vs] is the set of variable keys and [as] is the list of assignments copying [keys] to [vs] *)
let mint_key_names = mint_key_names_aux 0 [] [] 
  
(* a lightweight table encoding scheme used for benchmarking *)     
let table (id_int : int) (ks : Var.t list) (acts : (Var.t option * t) list) : t =
  let id = Printf.sprintf "%d" id_int in
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

(* a full table encoding scheme for interfacing with p4*)
let full_table (tbl_name : string) (ks : (int * Expr.t) list) (acts : (string * t) list) : t =
  let (asgns, varkeys) = mint_key_names tbl_name ks in 
  let read_keys = matchrow tbl_name varkeys in
  let hit act_id act =
    [assume (row_action tbl_name act_id (List.length acts));
     act ]
  in
  let actions = List.foldi acts ~init:[] ~f:(fun i acc (_,act) -> (hit i act)::acc) in
  let table = [Assume read_keys; choice_seqs actions] in
  (* TODO optimization. Rather than sequencing asgns, do the substitution! *)
  sequence (asgns @ table)

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

let rec normalize_names (c : t) : t = 
  match c with
  | Havoc x -> Havoc (Var.normalize_name x)
  | Assign (x,e) -> Assign (Var.normalize_name x, Expr.normalize_names e)
  | Assert (b, id) ->
     Assert (BExpr.normalize_names b, id)
  | Assume b ->
     Assume (BExpr.normalize_names b)
  | Seq (c1,c2) ->
     seq (normalize_names c1) (normalize_names c2)
  | Choice (c1,c2) ->
     choice (normalize_names c1) (normalize_names c2)
