open Core

module VarSet = Set.Make (Var)
   
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
let assume t = Assume t
let assert_ t = Assert (t,None)
let skip = assume BExpr.true_
let pass = assert_ BExpr.true_         
let abort = assert_ BExpr.false_
let dead = assume BExpr.false_          
let havoc x = Havoc x
let assign x e = Assign (x,e)
let seq c1 c2 =
  if equal c2 skip || equal c2 pass then
    c1
  else if equal c1 skip || equal c1 pass then
    c2
  else if equal c1 abort || equal c2 abort then
    abort
  else if equal c1 dead || equal c2 dead then
    dead
  else
    Seq(c1,c2)

let choice c1 c2 =
  if equal c1 dead then
    c2
  else if equal c2 dead then
    c1
  else if equal c1 abort || equal c2 abort then
    abort
  else
    Choice(c1,c2)              

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

let rec normal (c : t) : BExpr.t =
  let open BExpr in
  match c with
  | Havoc x -> failwith ("not sure what to do about havoc " ^ Var.str x)
  | Assign _ -> failwith ("assignments should have been factored out "
                          ^ to_string c) 
  | Assert (b,_) | Assume b -> b
  | Seq (c1, c2) ->
     and_ (normal c1) (normal c2)
  | Choice (c1, c2) ->
     or_ (normal c1) (normal c2)
     
let rec wrong (c : t) : BExpr.t =
  let open BExpr in 
  match c with
  | Havoc x -> failwith ("not sure what to do about havoc " ^ Var.str x)
  | Assign _ -> failwith ("assignments should have been factored out "
                          ^ to_string c) 
  | Assert (b,_) ->
     not_ b
  | Assume _ ->
     false_
  | Seq (c1,c2) ->
     or_
       (wrong c1)
       (and_ (normal c1) (wrong c2))
  | Choice (c1,c2) ->
     or_ (wrong c1) (wrong c2) 

let rec update_resid x curr tgt resid =
  if curr >= tgt then
    resid
  else
    let x_ i = Expr.var (Var.index x i) in
    BExpr.(and_ resid (eq_ (x_ curr) (x_ (curr+1))))      
    |> update_resid x (curr + 1) tgt
    
let rec passify_aux (ctx : Context.t) (c : t) =
  match c with
  | Havoc x -> failwith ("dont know what to do about havoc " ^ Var.str x)
  | Assign (x,e) ->
     let ctx = Context.increment ctx x in
     let x' = Context.label ctx x in
     let e' = Expr.label ctx e in
     (ctx, Assume (BExpr.eq_ (Expr.var x') e'))
  | Assert (b, id) ->
     (ctx, Assert (BExpr.label ctx b, id))
  | Assume b ->
     (ctx, Assume (BExpr.label ctx b))
  | Seq (c1,c2) ->
     let ctx, c1 = passify_aux ctx c1 in
     let ctx, c2 = passify_aux ctx c2 in
     (ctx, Seq (c1, c2))
  | Choice (c1,c2) ->
     let ctx1, c1 = passify_aux ctx c1 in
     let ctx2, c2 = passify_aux ctx c2 in
     let ctx, resid1, resid2 =
       Context.merge ctx1 ctx2 ~init:(BExpr.true_) ~update:update_resid
     in
     let rc1 = Seq (c1, Assume resid1) in
     let rc2 = Seq (c2, Assume resid2) in
     (ctx, Choice (rc1, rc2))
    
let passify (c : t) : t =
  snd (passify_aux Context.empty c)

let rec const_prop_aux (f : Facts.t) (c : t) =
  match c with
  | Havoc x ->
     (Facts.remove f x, c)
  | Assign (x,e) ->
     let e = Expr.fun_subst (Facts.lookup f) e in 
     (Facts.update f x e, assign x e)
  | Assert (b, id) ->
     Log.print @@ lazy (Printf.sprintf "substitute %s using: %s\n" (to_string c) (Facts.to_string f));
     let b = BExpr.fun_subst (Facts.lookup f) b in
     Log.print @@ lazy (Printf.sprintf "Got assert(%s)\n" (BExpr.to_smtlib b));
     (f, Assert (b,id))
  | Assume b ->
     let b = BExpr.fun_subst (Facts.lookup f) b in
     (f, Assume b)
  | Seq (c1, c2) ->
     let f, c1 = const_prop_aux f c1 in
     let f, c2 = const_prop_aux f c2 in
     (f, seq c1 c2)
  | Choice (c1, c2) ->
     let f1, c1 = const_prop_aux f c1 in
     let f2, c2 = const_prop_aux f c2 in
     let f = Facts.merge f1 f2 in
     Log.print @@ lazy (Printf.sprintf "After []:\n%s \n"
                          (Facts.to_string f));
     (f, choice c1 c2)
  
  
let const_prop c = snd (const_prop_aux Facts.empty c)

let rec dead_code_elim_aux c (reads : VarSet.t) : (t * VarSet.t) =
  let open VarSet in
  let concat (x,y) = x @ y in
  match c with
  | Havoc x ->
     (havoc x, remove reads x) 
  | Assign (x, e) ->
     if exists reads ~f:(Var.(=) x) then
       let read_by_e = of_list (concat (Expr.vars e)) in
       let reads_minus_x = remove reads x in
       let reads = union read_by_e reads_minus_x in
       (assign x e, reads)
     else
       (skip, reads)
  | Assert (b,_) -> 
     let read_by_b = of_list (concat (BExpr.vars b)) in
     let simpl_b = BExpr.simplify b in
     (assert_ simpl_b, union reads read_by_b)
  | Assume b ->
     let read_by_b = of_list (concat (BExpr.vars b)) in
     let simpl_b = BExpr.simplify b in
     (assume simpl_b, union reads read_by_b)
  | Choice (c1, c2) ->
     let c1, read_by_c1 = dead_code_elim_aux c1 reads in
     let c2, read_by_c2 = dead_code_elim_aux c2 reads in
     (choice c1 c2, union read_by_c1 read_by_c2)
  | Seq (c1, c2) ->
     let c2, reads = dead_code_elim_aux c2 reads in
     let c1, reads = dead_code_elim_aux c1 reads in
     (seq c1 c2, reads)

let dead_code_elim c = fst (dead_code_elim_aux c VarSet.empty)  


let rec fix f x =
  let x' = f x in
  if equal x' x then
    x
  else
    fix f x'
                     
let optimize c =
  let o c = dead_code_elim (const_prop c) in 
  fix o c
                     
let vc (c : t) : BExpr.t =
  let o = optimize c in
  let p = passify o in
  let w = wrong p in
  BExpr.(cnf (not_ w))
  (* wp p BExpr.true_ *)
