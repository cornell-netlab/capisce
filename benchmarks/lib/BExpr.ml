open Base_quickcheck
open Core

let enable_smart_constructors = ref `On

let q_count = ref (Bigint.zero)
let measure s : unit =
  Log.measure "%s" (lazy (Printf.sprintf "%f,%s,%s" (Clock.now()) (Bigint.to_string !q_count) s))
let incr_q x : unit =
  Bigint.incr q_count;
  measure (Printf.sprintf "+,%s" (Var.str x))
let decr_q x why : unit =
  Bigint.decr q_count;
  measure (Printf.sprintf "-,%s,%s" (Var.str x) why) 
   
type bop =
  | LAnd
  | LOr
  | LArr
  | LIff
  [@@deriving eq, sexp, hash, compare, quickcheck]

let bop_to_smtlib = function
  | LAnd -> "and"
  | LOr -> "or"
  | LArr -> "=>"
  | LIff -> "="

type comp =
  | Eq
  | Ult
  | Ule
  | Uge
  | Ugt
  | Slt
  | Sle
  | Sgt
  | Sge
  [@@deriving eq, sexp, hash, compare, quickcheck]

let comp_to_smtlib = function
  | Eq -> "="
  | Ult -> "bvult"
  | Ule -> "bvule"
  | Uge -> "bvuge"
  | Ugt -> "bvugt"
  | Slt -> "bvslt"
  | Sle -> "bvsle"
  | Sgt -> "bvsgt"
  | Sge -> "bvsge"

type t = 
  | TFalse
  | TTrue
  | LVar of string
  | TNot of t
  | TNary of bop * t list
  | TComp of comp * Expr.t * Expr.t
  | Forall of Var.t * t
  | Exists of Var.t * t
  [@@deriving eq, sexp, hash, compare, quickcheck]

type s = t (*hack, is there a better way?*)        
module Set_t = Set.Make (struct
                 type t = s
                 let sexp_of_t = sexp_of_t
                 let t_of_sexp = t_of_sexp
                 let compare = compare
               end)

module PredAbs = PredAbstract.Make (struct
                 type t = s
                 let sexp_of_t = sexp_of_t
                 let t_of_sexp = t_of_sexp
                 let compare = compare
                   end)
               
             
module SetOfSet_t = Set.Make (Set_t)           

let (=) = equal
           
let rec to_smtlib_buffer indent buff b : unit =
  let space = Util.space (2 * indent) in
  Buffer.add_string buff space;
  match b with
  | TFalse ->
     Buffer.add_string buff "false"
  | TTrue ->
     Buffer.add_string buff "true"
  | LVar a ->
     Buffer.add_string buff a
  | TNot (t) ->
     Buffer.add_string buff "(not";
     to_smtlib_buffer (indent + 1) buff t;
     Buffer.add_string buff ")";
  | TNary (b,ts) ->
     Buffer.add_string buff "(";
     Buffer.add_string buff (bop_to_smtlib b);
     List.iter ts ~f:(fun t1 ->
         Buffer.add_string buff "\n";         
         to_smtlib_buffer (indent + 1) buff t1;
       );
     Buffer.add_string buff ")";
  | TComp (comp, e1, e2) ->
     Buffer.add_string buff "(";
     Buffer.add_string buff (comp_to_smtlib comp);
     Buffer.add_string buff " ";
     Buffer.add_string buff (Expr.to_smtlib e1);
     Buffer.add_string buff " ";     
     Buffer.add_string buff (Expr.to_smtlib e2);
     Buffer.add_string buff ")"
  | Forall (v, t) ->
     Buffer.add_string buff (Printf.sprintf "(forall (%s)\n" (Var.list_to_smtlib_quant [v]));
     to_smtlib_buffer (indent+1) buff t;
     Buffer.add_string buff ")"
  | Exists (v, t) ->
     Buffer.add_string buff (Printf.sprintf "(exists (%s)\n" (Var.list_to_smtlib_quant [v]));
     to_smtlib_buffer (indent+1) buff t;
     Buffer.add_string buff ")"
     
let varstime : float ref = ref 0.0

let rec compute_vars (t : t) =
  match t with
  | TFalse | TTrue | LVar _ ->
     ([],[])
  | TNot (t) ->
     compute_vars t
  | TNary (_, ts) ->
     let dedup = List.dedup_and_sort ~compare:Var.compare in
     List.fold_left ts ~init:([],[])
       ~f:(fun (dvs,cvs) t ->
         let dvs', cvs' = compute_vars t in
         (dedup (dvs @ dvs'), dedup (cvs @ cvs')))
  | TComp (_, e1, e2) ->
     Var.(Util.pairs_app_dedup ~dedup (Expr.vars e1) (Expr.vars e2))     
  | Forall (x, b) | Exists (x, b) ->
     let dvs, cvs = compute_vars b in
     Var.(Util.ldiff ~equal dvs [x], Util.ldiff ~equal cvs [x])                    

let get_labelled_vars b =
      compute_vars b |> Util.uncurry (@)
  
let vars t : Var.t list * Var.t list =
  let c = Clock.start () in
  let vars = get_labelled_vars t in
  let res = List.partition_tf vars ~f:(Fn.non Var.is_symbRow) in
  let dur = Clock.stop c in
  varstime := Float.(!varstime + dur);
  (* Log.print @@ lazy (Printf.sprintf "Vars has taken %fms" !varstime); *)
  res

let occurs_in x b =
  get_labelled_vars b
  (* compute_vars b
   * |> Util.uncurry (@)  *)
  |> List.exists ~f:(Var.(=) x)

let to_smtlib c =
  let b = Buffer.create 8000 in
  to_smtlib_buffer 0 b c;
  Buffer.contents b
    
let ctor1 ~default ~smart a =
  match !enable_smart_constructors with
  | `On -> smart default a
  | `Off ->
     default a
let ctor2 ~default ~smart a b =
  match !enable_smart_constructors with
  | `On ->
    smart default a b
  | `Off ->
    default a b
(* let rec ctor2rec ~default ~smart a b =
 *   match !enable_smart_constructors with
 *   | `On -> smart (ctor2rec ~default ~smart) default a b
 *   | `Off -> default a b *)
        
let false_ = TFalse
let true_ = TTrue
let not_ =
  ctor1
    ~default:(fun b -> TNot (b))
    ~smart:(fun default b ->
      match b with
      | TFalse -> true_
      | TTrue -> false_
      | TNot (b) -> b
      | b -> default b)

let rec fun_subst f t =
  match t with
  | TFalse | TTrue | LVar _ ->
     t
  | TNot (t) ->
     let t = fun_subst f t in
     TNot (t)
  | TNary (op, ts) ->
     let ts = List.map ts ~f:(fun_subst f) in
     TNary(op, ts)     
  | TComp (comp, e1, e2) ->
     let e1 = Expr.fun_subst f e1 in
     let e2 = Expr.fun_subst f e2 in
     TComp (comp, e1, e2)
  | Forall (x, t) ->
     let f' y = if Var.(x = y) then
                  Expr.var y
                else f y in
     Forall (x, fun_subst f' t)
  | Exists (x, t) ->
     let f' y = if Var.(y = x)  then
                  Expr.var y
                else
                  f y in
     Exists (x, fun_subst f' t) 
                    
let subst x e t =
  let f y = if Var.(y = x) then e else Expr.var y in
  fun_subst f t

let one_point_rule e1 e2 b : t =
  if Expr.is_var e1 then
    let v1 = Expr.get_var e1 in
    if Expr.is_var e2 then
      let v2 = Expr.get_var e2 in
      if not (Var.is_symbRow v1) then
        subst v1 e2 b
      else
        subst v2 e1 b
    else
      subst v1 e2 b
  else if Expr.is_var e2 then
    let v2 = Expr.get_var e2 in
    subst v2 e1 b
  else
    failwith "called one_point_rule but nothing was there!"

let lvar x = LVar x 
  
let and_ =
  ctor2
    ~default:(fun b1 b2 ->
      TNary(LAnd, [b1;b2]))
    ~smart:(fun default b1 b2 ->  
      if b1 = true_ then
        b2
      else if b2 = true_ then
        b1
      else if b1 = false_ || b2 = false_ then
        false_
      else if b1 = b2 then
        b1
      else
        match b1, b2 with
        | TNot (TComp(Eq, e11, e12)),
          TNot (TComp(Eq, e21, e22)) ->
           if Expr.neq_contra (e11, e12) (e21, e22) then
             false_
           else
             default b1 b2
        | TNot (bneg), b0 | b0, TNot (bneg) ->
           if bneg = b0 then
             false_
           else
             default b1 b2
        | TNary(LAnd, bs1), TNary(LAnd, bs2) ->
          Log.rewrites "%s" @@ lazy "SUBAND";
          TNary(LAnd, bs1@bs2)
        | TNary(LAnd, bs1), b2 ->
          Log.rewrites "%s" @@ lazy "LEFT_AND";
          TNary(LAnd, bs1@[b2])
        | b1, TNary(LAnd, bs2) ->
          Log.rewrites "%s" @@ lazy "RIGHT_AND";
          TNary(LAnd, b1::bs2)
        | _ -> default b1 b2)

let ands_ = List.fold ~init:true_ ~f:and_
  
let imp_ =
  ctor2
    ~default:(fun b1 b2 ->
      TNary(LArr, [b1; b2]))
    ~smart:(fun default b1 b2 ->
      if b2 = true_ || b1 = false_ then
        true_
      else if b2 = false_ then
        not_ b1
      else if b1 = true_ then
        b2
      else if b1 = b2 then
        true_
      else
        match b1 with
        | TComp (Eq, e1, e2) when Expr.is_var e1 || Expr.is_var e2 ->
           default b1 (one_point_rule e1 e2 b2)
        | _ ->
           default b1 b2)

let rec imps_ bs =
  match bs with
  | [] -> failwith "imps_ needs a nonempty list"
  | [b] -> b
  | b::bs -> imp_ b (imps_ bs)

let or_ =
    ctor2
      ~default:(fun b1 b2 ->
        match b1, b2 with
        | TNary(LOr, bs1), TNary(LOr, bs2) ->
           TNary(LOr, bs1@bs2)
        | TNary(LOr, bs1), b2 ->
           TNary(LOr, bs1@[b2])
        | b1, TNary(LOr, bs2) ->
           TNary(LOr, b1::bs2)
        | _ ->
           TNary(LOr, [b1;b2]))
    ~smart:(fun default b1 b2 ->
      if b2 = true_ || b1 = true_ then
        true_
      else if b2 = false_ then
        b1
      else if b1 = false_ then
        b2
      else if b1 = b2 then
        b1
      else
        match b1, b2 with
        | TNot (TComp (Eq, e1, e2)) as asm, body when Expr.(is_var e1 || is_var e2) ->
           let o_p_res = one_point_rule e1 e2 body |> default asm in
           (* Log.print @@ lazy (Printf.sprintf
            *                      "ONE POINT RULE STARTED WITH \n %s \n GOT: %s\n"
            *                      (default asm body |> to_smtlib)
            *                      (o_p_res |> to_smtlib)); *)
           o_p_res
        | body, (TNot (TComp (Eq, e1, e2)) as asm) when Expr.(is_var e1 || is_var e2) ->
           one_point_rule e1 e2 body           
           |> default asm
        | _, _->
           default b1 b2)

let ors_ = List.fold ~init:false_ ~f:or_
  
let iff_ =
  ctor2
    ~default:(fun b1 b2 -> TNary(LIff, [b1; b2]))
    ~smart:(fun default b1 b2 ->
      if b1 = b2 then
        true_      
      else
        default b1 b2
    )
  
let iffs_ bs = TNary(LIff, bs)
  
let eq_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Eq,e1,e2))
    ~smart:(fun default e1 e2 ->
      match Expr.static_eq e1 e2 with
      | None ->
         default e1 e2
      | Some true -> true_
      | Some false -> false_)

let ult_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Ult,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let ule_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Ule,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let uge_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Uge,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let ugt_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Ugt,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let slt_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Slt,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let sle_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Sle,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let sge_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Sge,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let sgt_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Sgt,e1,e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let dumb f =
  enable_smart_constructors := `Off;
  let b = f () in
  enable_smart_constructors := `On;
  b
  
let get_smart = function
  | LAnd -> and_
  | LOr -> or_
  | LArr -> imp_
  | LIff -> iff_

let get_smarts = function
  | LAnd -> ands_
  | LOr -> ors_
  | LArr -> imps_
  | LIff -> iffs_

let get_smart_comp = function
  | Eq -> eq_
  | Ult -> ult_
  | Ule -> ule_
  | Uge -> uge_
  | Ugt -> ugt_
  | Slt -> slt_
  | Sle -> sle_
  | Sgt -> sgt_
  | Sge -> sge_

let size_ = ref 0
         
let rec size_aux = function
  | TFalse | TTrue | LVar _ ->
     size_ := !size_ + 1  
  | TComp (_,e1,e2) ->
     size_ := !size_ + 1 + Expr.size e1 + Expr.size e2;
  | TNot (b) ->
     size_ := !size_ + 1;
     size_aux b
  | TNary (_, bs) ->
     size_ := !size_ + 1;
     List.iter bs ~f:size_aux
  | Forall (_, b) | Exists (_, b) ->
     size_ := !size_ + 1;
     size_aux b

let size b =
  size_ := 0;
  size_aux b;
  !size_

let ic_ugt x b e1 e2 =
  (* ∀ x. b
   * ≜ ∀ x. ¬(e1 >ᵤ e2)
   * ≡ ¬∃x. e1 >ᵤ e2
   * *)
  if Expr.is_var e1 then
    let v1 = Expr.get_var e1 in
    if Var.equal x v1 then begin
        (* ¬∃x. x >ᵤ e2  (we're in this case)
         * ≡ ¬ ∃ x. (x | 0) >ᵤ e2
         * ≡ ¬ (e2 <ᵤ -1) (APPLYING THE RELEVANT IC) *)
        not_ (ult_ e2 (Expr.bvi (-1) (Var.size v1)))
      end
    else if Expr.is_var e2 then
      let v2 = Expr.get_var e2 in
      if Var.equal x v2 then begin
          decr_q x "IC-ugt2";
          (* ¬∃x. e1 >ᵤ x
           * ≡ ¬∃x. x <ᵤ e1
           * ≡ ¬∃x. x & F..F <ᵤ e1
           * ≡ ¬ t ≠ 0
           * ≡ t = 0 *)          
          (eq_ e1 (Expr.bvi 0 (Var.size v2)))
        end
      else
        Forall(x, b)
    else
      Forall(x, b)
  else if Expr.is_var e2 then
    let v2 = Expr.get_var e2 in
    if Var.equal x v2 then begin
        decr_q x "IC-ugt3";
        (* same derivation as ic-ugt2 *)
        (eq_ e1 (Expr.bvi 0 (Var.size v2)))
      end
    else
      Forall(x, b)
  else
    Forall(x, b)

let process_bors e1 e2 e1_reassoc e2_reassoc =
  match e1_reassoc, e2_reassoc with
  | Some(x, s), _ ->
     let t = e2 in
     Some (x, s, t)
  | None, Some(x,s) ->
     let t = e1 in
     Some (x, s, t)
  | None, None ->
     None
  
let ic_neq x b e1 e2 =
  (* attempt to apply the ic: ∀ x. x | s ≠ t  *)
  (* which becomes ¬ ∃ x. x | s = t   *)
  (* we return either b or ¬ (s | t = t) *)
  let e1_reassoc = Expr.reassociate_bors x e1 in
  let e2_reassoc = Expr.reassociate_bors x e2 in
  match process_bors e1 e2 e1_reassoc e2_reassoc with
  | Some (x',s,t) when Var.(x = x') -> 
     not_ (eq_ (Expr.bor s t) t)
  | _ -> 
     Forall(x, b)

let ic_eq x b e1 e2 =
  (* attempt to apply the ic: ∀ x. x | s = t  *)
  (* which becomes ¬ ∃ x. x | s ≠ t *)
  (* we return either b or ¬ (s = !0 ∨ t = !0) *)  
  let e1_reassoc = Expr.reassociate_bors x e1 in
  let e2_reassoc = Expr.reassociate_bors x e2 in
  match process_bors e1 e2 e1_reassoc e2_reassoc with
  | Some (x',s,t) when Var.(x = x') ->
     and_ (eq_ s Expr.(bnot (bvi 0 (width s))))
          (eq_ t Expr.(bnot (bvi 0 (width t))))
  | _ -> 
     Forall(x, b)
  

let destruct_arr bs =
  let rec loop bs premises conclusion = 
    match bs with
    | [] -> (premises, conclusion)
    | [b] -> (premises, [b])
    | b::bs -> loop bs (premises@[b]) conclusion
  in
  loop bs [] []

let destruct_arr_forms bs =  
  let premises_list, conclusion_singleton = destruct_arr bs in
  let premises = ands_ premises_list in
  let conclusion = List.hd_exn conclusion_singleton in
  premises, conclusion
    
let forall_imp self x bs =
  let premises, conclusion = destruct_arr_forms bs in
  if occurs_in x premises && occurs_in x conclusion then
    Forall (x, (imp_ premises conclusion))
  else if occurs_in x premises then
    let premises = self x (not_ premises) in
    or_ premises conclusion
  else if occurs_in x conclusion then
    let conclusion = self x conclusion in 
    imp_ premises conclusion
  else begin
      decr_q x "not_free_imp_";
      imp_ premises conclusion
    end

let forall_or self x bs =
  let scoped, unscoped = List.partition_tf ~f:(occurs_in x) bs in
  if List.is_empty unscoped then
    Forall(x, ors_ bs)
  else if List.is_empty scoped then begin
      decr_q x "not_free_or_";
      ors_ unscoped
    end
  else begin
      or_ (self x (ors_ scoped)) (ors_ unscoped)
    end
  (* if occurs_in x b1 && occurs_in x b2 then
   *   Forall(x, (or_ b1 b2))
   * else if occurs_in x b1 then
   *   let b1 = self x b1 in
   *   or_ b1 b2
   * else if occurs_in x b2 then
   *   let b2 = self x b2 in
   *   or_ b1 b2
   * else begin
   *     decr_q x "not_free_or_";
   *     or_ b1 b2
   *   end *)
  
let rec forall_one (x : Var.t) b =  
  (* Log.size (size b); *)
  (* Log.print @@ lazy (Printf.sprintf "smart constructor for ∀ %s (_ BitVec %d) over an ast comprising %d bits and %d nodes!" (Var.str x) (Var.size x) (Obj.(reachable_words (repr b) + 1) * 64) (size b)); *)
  Log.smart "smart constructor for %s" (lazy (Var.str x));
  match `Off with (* !enable_smart_constructors with *)
  | `Off ->  Forall(x,b)
  | `On -> 
     (* Log.size (size b);       *)
     let bvs = get_labelled_vars b in
     if not (List.exists bvs ~f:(Var.(=) x)) then begin
         decr_q x "not free";
         b
       end else 
       match b with
       | TFalse ->
          decr_q x "false";
          false_
       | TTrue ->
          decr_q x "true";
          true_
       | TNot (TComp(Eq,e1,e2)) when Expr.uelim `Neq [x] e1 e2 ->
          decr_q x "neq_false";
          false_
       | TNot (TComp(Ugt,e1,e2)) ->
          (ic_ugt x b e1 e2)
       | TNot (TNary (LOr,bs)) ->
          (* ¬ ⋁ᵢ bᵢ = ¬ ¬ ⋀¬bᵢ = ⋀ ¬bᵢ  *)
          forall_one x (ands_ (List.map ~f:not_ bs))
       | TNot(TComp(Eq, e1, e2)) ->
          ic_neq x b e1 e2
       | TComp(Eq, e1, e2) when Expr.uelim `Eq [x] e1 e2 ->             
          decr_q x "eq_false";
          false_
       | TComp(Eq, e1, e2) ->
          ic_eq x b e1 e2                         
       | TNary (op, bs) ->
          begin match op with
          | LArr ->
             forall_imp forall_one x bs
          | LOr ->
             forall_or forall_one x bs 
          | LAnd ->
             decr_q x @@ Printf.sprintf "distributing across %d" (List.length bs);
             let bs = List.map ~f:(fun b -> incr_q x; forall_one x b) bs in
             ands_ bs
          | LIff ->
             Forall(x, (iffs_ bs))
          end
       | Forall(y, b') ->
          let b' = forall_one x b' in
          (* forall_one y b' *)
          Forall(y, b')
       | _ ->
          Forall(x, b)

let forall xs b = if List.is_empty xs then
                    true_
                  else
                    List.fold_right xs ~init:b ~f:forall_one 

let exists_one x b = Exists(x, b)

let exists x b = List.fold_right x ~init:b ~f:exists_one

let rec simplify_inner = function
  | TFalse -> TFalse
  | TTrue -> TTrue
  | LVar a -> LVar a
  | TNot (b) -> not_ (simplify_inner b)
  | TNary (op, bs) ->
     List.map bs ~f:simplify_inner
     |> get_smarts op
  | TComp (op, e1, e2) ->
     get_smart_comp op e1 e2
  | Forall (x, b) -> simplify_inner b |> forall_one x
  | Exists (x, b) -> simplify_inner b |> exists_one x

let simplify b =
  (* Log.size (size b); *)
  (* Log.print @@ lazy "simplify"; *)
  (* let tmp = !enable_smart_constructors in *)
  (* enable_smart_constructors := `On; *)
  let b' = simplify_inner b in
  (* enable_smart_constructors := tmp; *)
  b'

let rec label (ctx : Context.t) (b : t) : t =
  match b with
  | TFalse | TTrue | LVar _ -> b
  | TNot (b) -> not_ (label ctx b)
  | TNary (bop, bs) ->
     List.map bs ~f:(label ctx) 
     |> get_smarts bop
  | TComp (comp, e1, e2) ->
     (get_smart_comp comp) (Expr.label ctx e1) (Expr.label ctx e2)
  | Forall _ | Exists _ ->
     failwith "Not sure how to label quantifiers"

let rec nnf (b : t) : t = 
  match b with
  | TFalse | TTrue | LVar _ -> b
  | TComp _ -> b
  | Forall (x, e) -> forall_one x (nnf e)
  | Exists (vs, e) -> exists_one vs (nnf e) 
  | TNary (op, bs) ->
     begin match op with
     | LAnd -> ands_ (List.map bs ~f:nnf)
     | LOr -> ors_ (List.map bs ~f:nnf)
     | LArr ->
        let premises, conclusion = destruct_arr_forms bs in
        or_ (nnf (not_ premises)) (nnf conclusion)
     | LIff ->
        List.fold_left bs ~init:true_ ~f:(fun acc b1 ->
        List.fold_left bs ~init:acc ~f:(fun acc b2 ->
            ands_ [acc;
                   or_ (nnf (not_ b1)) (nnf b2);
                   or_ (nnf (not_ b2)) (nnf b1)] ))
     end
  | TNot (b) ->
     match b with
     | TFalse -> TTrue
     | TTrue -> TFalse
     | LVar _ -> TNot (b)
     | TNot (b) -> nnf b
     | TComp _ -> not_ b
     | Forall (vs, b) -> exists_one vs (nnf (not_ b))
     | Exists (vs, b) -> forall_one vs (nnf (not_ b))
     | TNary (op, bs) ->
        match op with
        | LAnd -> ors_ (List.map bs ~f:(fun b -> nnf (not_ b)))
        | LOr -> ands_ (List.map bs ~f:(fun b -> nnf (not_ b)))
        | LArr | LIff ->
           nnf b   (* normalize subterm, i.e. desugar => and <=> *)
           |> not_ (* negate *) 
           |> nnf  (* normalize full term*)
                       
let rec cnf_inner (b : t) : t list list =
  match b with
  | TFalse | TTrue | LVar _ | TComp _ ->
     [[b]]
  | Forall _ ->
     failwith "i swear you shouldn't use me"
  | Exists _ ->
     failwith "what in the world is my purpose"
  | TNary (op, bs) ->
     begin match op with
     | LAnd ->
        List.bind bs ~f:cnf_inner
     | LOr ->
        begin match bs with
        | [] -> failwith "list of bs cannot be empty"
        | [b] -> cnf_inner b
        | b1::bs -> 
           let open List.Let_syntax in
           let b2 = ors_ bs in
           let cb1 = cnf_inner b1 in
           let cb2 = cnf_inner b2 in
           let%bind conj1 = cb1 in
           let%map conj2 = cb2 in
           conj1 @ conj2 |> List.dedup_and_sort ~compare
        end
     | LArr -> failwith "whoops! crap on a carbunckle"
     | LIff -> failwith "whangdoodle winkerdinker" 
     end
  | TNot (b) ->
     match b with
     | TFalse -> [[true_]]
     | TTrue -> [[false_]]
     | TComp _ -> [[not_ b]]
     | _ ->
        failwithf  "You really shouldn't be out here this late with a (not %s) in your hands " (to_smtlib b) ()

let cnf b =
  Log.rewrites "cnfing.. %i " (lazy (size b));
  let nnfd = nnf b in
  Log.rewrites "nnfed.. %i" (lazy (size nnfd));
  let ands_of_ors = cnf_inner nnfd in
  Log.rewrites "un-cnfing...%s" (lazy "");
  let cnfd = TNary(LAnd, List.map ands_of_ors ~f:(fun ors -> TNary(LOr, ors))) in
  Log.rewrites "done, size %i" (lazy (size cnfd));
  cnfd


let rec get_conjuncts b =
  match b with
  | TNary (LAnd, bs) ->     
     List.bind bs ~f:get_conjuncts
  | _ ->
     [b]

let abstract_expressionism ~threshold b =
  let abstractable expr =
    (* expr is sufficiently big *)
    Expr.size expr > threshold
    && (* there are no symbolic variables *)
    (Expr.vars expr |> snd |> List.is_empty)
  in
  let abstract name_gen expr =
    if abstractable expr then
      let name, name_gen = NameGen.get name_gen in
      let width = Expr.width expr in
      let abstract_name = Var.make name width in
      (name_gen, Expr.var abstract_name, [abstract_name])
    else
      (name_gen, expr, [])
  in
  let rec abstract_inner threshold name_gen b =
    match b with
    | TFalse | TTrue | LVar _  ->
      name_gen, b, []
    | TNary (op, bs) ->
      let name_gen, bs, new_vars = List.fold bs ~init:(name_gen, [], [])
          ~f:(fun (name_gen, bs, new_vars) b ->
              let name_gen, b, b_vars = abstract_inner threshold name_gen b in
              name_gen, bs@[b], new_vars @ b_vars)
      in
      (name_gen, get_smarts op bs, new_vars)
    | TNot b ->
      let name_gen, b, new_vars = abstract_inner threshold name_gen b in
      (name_gen, not_ b, new_vars)
    | Forall (x, b) ->
      let name_gen, b, new_vars = abstract_inner threshold name_gen b in
      name_gen, forall_one x b, new_vars
    | Exists (x,b) ->
      let name_gen, b, new_vars = abstract_inner threshold name_gen b in
      name_gen, forall_one x b, new_vars
    | TComp (comp, e1, e2) ->
      let name_gen, e1, new_vars1 = abstract name_gen e1 in
      let name_gen, e2, new_vars2 = abstract name_gen e2 in
      (name_gen, (get_smart_comp comp) e1 e2, new_vars1 @ new_vars2)
  in
  let _, phi, xs = abstract_inner threshold (NameGen.create ()) b in
  List.fold xs ~init:phi ~f:(fun phi x -> Forall (x, phi))


let quickcheck_generator : t Generator.t =
  let open Quickcheck.Generator in
  let open Let_syntax in
  recursive_union
    [
      singleton TFalse;
      singleton TTrue;
      (let%bind e1 = Expr.quickcheck_generator in
       let%bind e2 = Expr.quickcheck_generator in
       let%map c = quickcheck_generator_comp in 
       TComp(c,e1,e2))
    ]
    ~f:(fun self ->
      [
        (let%map b = self in TNot b);

        (let%bind op = quickcheck_generator_bop in 
         match op with
         | LIff ->
            let%bind b1 = self in
            let%map  b2 = self in 
            TNary(LIff, [b1;b2])
         | _ ->
            let%map bs = list self |> filter ~f:(fun l -> List.length l > 1) in
            TNary (op, bs)
        );

        (let%bind b = self in
         let vs = vars b |> Util.uncurry (@) in
         if List.is_empty vs then
           return b
         else
           let%map x = vars b |> Util.uncurry (@) |> of_list in 
           Forall (x, b));

        (let%bind b = self in
         let vs = vars b |> Util.uncurry (@) in         
         if List.is_empty vs then
           return b
         else
           let%map x = vars b |> Util.uncurry (@) |> of_list in          
           Exists (x, b)
        )
      ]
    )
  
let qf_quickcheck_generator : t Generator.t =
  let open Quickcheck.Generator in
  let open Let_syntax in
  recursive_union
    [
      singleton TFalse;
      singleton TTrue;
      (let%bind e1 = Expr.quickcheck_generator in
       let%bind e2 = Expr.quickcheck_generator in
       let%map c = quickcheck_generator_comp in 
       TComp(c, e1, e2))
    ]
    ~f:(fun self ->
      [
        (let%map b = self in TNot b);

        (let%bind op = quickcheck_generator_bop in
         let%map bs = list self in
         TNary (op, bs)
        );
      ]
    )
  
let quickcheck_shrinker : t Shrinker.t = Shrinker.atomic
  
let rec well_formed b =
  match b with
  | TTrue | TFalse | LVar _ -> true
  | TComp (_,e1,e2) -> Expr.well_formed e1 && Expr.well_formed e2
  | TNary(_,bs) -> List.for_all bs ~f:well_formed
  | TNot (b) | Forall (_,b) | Exists(_,b) -> well_formed b

let rec normalize_names b =
  match b with
  | TTrue | TFalse | LVar _ -> b
  | TComp (comp,e1,e2) ->
     let e1' = Expr.normalize_names e1 in
     let e2' = Expr.normalize_names e2 in
     TComp(comp, e1', e2')
  | TNary(op, bs) ->
     let bs = List.map bs ~f:normalize_names in
     TNary(op, bs)
  | TNot (b) ->
     let b' = normalize_names b in
     TNot b'
  | Forall (x,b) ->
     Forall (Var.normalize_name x, normalize_names b)
  | Exists(x,b) ->
     Exists (Var.normalize_name x, normalize_names b)
  
let equivalence a b =
  let avars = vars a |> Util.uncurry (@) in
  let bvars = vars b |> Util.uncurry (@) in
  let xs = avars @ bvars |> List.dedup_and_sort ~compare:Var.compare in
  dumb (fun () -> exists xs (not_ (iff_ a b)))
    
let rec qf = function
  | TFalse
    | TTrue
    | TComp _ -> true
  | LVar _ -> false
  | TNot b -> qf b
  | TNary (_,bs) -> List.for_all bs ~f:qf
  | Forall (_,_) ->
     false
  | Exists (_,_) ->
     false

let rec predicate_abstraction_inner abs b : (PredAbs.t * t) =
  match b with
  | TFalse | TTrue | LVar _ -> (abs, b)
  | TComp (_, _, _) ->
     if List.exists (get_labelled_vars b) ~f:(Fn.non Var.is_symbRow) then
       let (x, abs) = PredAbs.abs abs b in
       (abs, LVar x)
     else
       (abs, b)
  | TNot (b) ->
     let (abs, b) = predicate_abstraction_inner abs b in
     (abs, not_ b)
  | TNary (op, bs) ->
     let abs, bs = 
       List.fold_left bs ~init:(abs,[]) ~f:(fun (abs, bs) b ->
           let (abs, b) = predicate_abstraction_inner abs b in
           (abs, b::bs) 
         )
     in
     (abs, (get_smarts op) bs)
  | Forall (x, b) ->
     let (abs, b) = predicate_abstraction_inner abs b in
     (abs, forall [x] b)
  | Exists (x, b) ->
     let (abs, b) = predicate_abstraction_inner abs b in
     (abs, exists [x] b)
    

let predicate_abstraction (b : t) =
  let abs = PredAbs.create () in
  let (_, b) = predicate_abstraction_inner abs b in
  b

let rec get_atoms b =
  match b with
  | TFalse | TTrue | LVar _ -> []
  | TComp _ -> [b]
  | TNot (b) -> get_atoms b
  | TNary (_, bs) -> List.bind bs ~f:get_atoms
  | _ -> failwith "cannot get atoms under quantifiers" 

let rec get_atoms_containing x b =
  match b with
  | TFalse | TTrue | LVar _ -> []
  | TComp _ ->
     if List.mem (get_labelled_vars b) x ~equal:Var.equal then
       [b]
     else []
  | TNot (b) ->
     get_atoms_containing x b
  | TNary (_, bs) ->
     List.bind bs  ~f:(get_atoms_containing x)
  | Forall (x', _) 
  | Exists (x', _) when Var.(x' = x) ->
     []
  | Forall (_, b)
   | Exists (_, b) ->
     get_atoms_containing x b

let rec abstract_atom atom var b =
  if b = atom then
    LVar var
  else
    let shadow x = List.mem (fst (vars atom)) x ~equal:Var.equal in
    match b with
    | TFalse | TTrue | LVar _ | TComp _ -> b
    | TNary (op, bs) ->
       List.map bs ~f:(abstract_atom atom var)
       |> get_smarts op
    | TNot (b) ->
       not_ (abstract_atom atom var b)
    | Forall (x, _)
      | Exists (x, _) when shadow x ->
       b
    | Forall (x, b) ->
       forall_one x (abstract_atom atom var b)
    | Exists (x, b) ->
       exists_one x (abstract_atom atom var b)

let one_or_zero atoms =
  List.for_all atoms ~f:(fun atom ->
      match atom with
      | TComp(Eq, e1, e2) ->
         Expr.is_var e1 && (Expr.is_one e2 || Expr.is_zero e2)
         || Expr.is_var e2 && (Expr.is_one e1 || Expr.is_one e1)
      | _ ->
         failwith "not do good"
    ) 
      
      
let abstraction_is_complete x atoms =
  let unique_atoms = List.dedup_and_sort atoms ~compare in
  Int.(List.length unique_atoms = 1)
  || (Int.(Var.size x = 1)
      && one_or_zero atoms) 
    
let complete_predicate_abstraction x (b : t) =
  let atoms = get_atoms_containing x b in
  if abstraction_is_complete x atoms then
    let atom = List.hd_exn atoms in
    let var = "$___REMOVE___$" in
    Some (abstract_atom atom var b)
  else
    None

let rec get_abstract_predicates b =
  match b with
  | TFalse | TTrue | TComp _ -> []
  | LVar x -> [x]
  | TNot (b) ->
     get_abstract_predicates b
  | TNary (_, bs) ->
     List.bind bs ~f:(get_abstract_predicates)
     |> List.dedup_and_sort ~compare:String.compare
  | Forall (_, b) | Exists (_, b)->
     get_abstract_predicates b
    
let abstract_qvars  b =
  let bs = get_abstract_predicates b in
  List.map bs ~f:(Printf.sprintf "(%s Bool)")
  |> String.concat ~sep:" "
  
let rec fun_subst_lvar f b =
  match b with
  | TFalse | TTrue | TComp _ -> b
  | LVar y ->
     f y
  | TNot (b) ->
     not_ (fun_subst_lvar f b)
  | TNary (op, bs) ->
     List.map bs ~f:(fun_subst_lvar f)  
     |> get_smarts op
  | Forall (y, b) ->
     forall_one y (fun_subst_lvar f b)
  | Exists (y, b)->
     exists_one y (fun_subst_lvar f b)

let subst_lvar x b0 =
  fun_subst_lvar (fun y -> if String.(x = y) then b0 else lvar y)

let eval_comp c (v1,w1) (v2,w2) =
  begin match c with
  | Slt | Sle | Sge | Sgt ->
    lazy (to_smtlib @@ get_smart_comp c (Expr.bv v1 w1) (Expr.bv v2 w2))
    |> Log.warn "Warning. implementing signed as unsigned: %s"
  | _ ->()
  end;
  match c with
  | Eq  -> Bigint.(=)  v1 v2
  | Ult -> Bigint.(<)  v1 v2
  | Ule -> Bigint.(<=) v1 v2
  | Uge -> Bigint.(>=) v1 v2
  | Ugt -> Bigint.(>)  v1 v2
  | Slt -> Bigint.(<)  v1 v2
  | Sle -> Bigint.(<=) v1 v2
  | Sgt -> Bigint.(>)  v1 v2
  | Sge -> Bigint.(>=) v1 v2

let rec eval_op op bs : bool =
  match op with
  | LAnd -> List.for_all   bs ~f:Fn.id
  | LOr  -> List.exists    bs ~f:Fn.id
  | LIff -> List.all_equal bs  ~equal:Bool.equal
            |> Option.is_some
  | LArr ->
    match List.rev bs with
    | []  -> failwith "cannot compute => of empty list"
    | [_] -> failwith "cannot compute => of singleton list"
    | b::bs ->
      (*=> bs b ==== (/\bs) => b ==== b \/ ~(/\bs) *)
      b || not (eval_op LAnd bs)

let rec eval (model : Model.t) (phi : t) : bool =
  match phi with
  | TFalse -> false
  | TTrue -> true
  | TComp (c, e1, e2) ->
    let v1 = Expr.eval model e1 |> Result.ok_or_failwith in
    let v2 = Expr.eval model e2 |> Result.ok_or_failwith in
    begin match c with
      | Eq ->
        Log.debug_s "evaluating (=)";
        Log.debug "\te1 was %s" @@ lazy (Expr.to_smtlib e1);
        Log.debug "\te1  is %s" @@ lazy (Bigint.to_string (fst v1));
        Log.debug "\te2 was %s" @@ lazy (Expr.to_smtlib e2);
        Log.debug "\te2  is %s" @@ lazy (Bigint.to_string (fst v2));
        let b = eval_comp c v1 v2 in
        Log.debug "\t==== %b"   @@ lazy b;
        b
      | _ -> eval_comp c v1 v2
    end
  | TNary (op, bs) ->
    List.map ~f:(eval model) bs
    |> eval_op op
  | TNot b ->
    let v = eval model b in
    not v
  | LVar _ -> failwith "Don't have evaluation for LVars"
  | Forall _  | Exists _ ->
    failwith "Dont have evaluation for quantifiers"


let get_equality b =
  match b with
  | TComp(Eq, e1, e2) when Expr.is_var e1 ->
     Some (Expr.get_var e1, e2)
  | TComp(Eq, e1, e2) when Expr.is_var e2 ->
     Some (Expr.get_var e2, e1)
  | _ ->
     None
  
(** Solver interface Code*)
  
module Ctx = Map.Make (String) 

let rec coerce_types gamma (b : t) : t =
  match b with
  | TFalse | TTrue | LVar _ -> b                    
  | TNot (b)  ->
     not_ (coerce_types gamma b) 

  | TNary (bop, bs) ->
     List.map bs ~f:(coerce_types gamma)
     |> get_smarts bop
  | TComp (comp, e1, e2) ->
     let ctor = get_smart_comp comp in
     let e1 = Expr.coerce_types gamma e1 in
     let e2 = Expr.coerce_types gamma e2 in
     ctor e1 e2
  | Forall (x, b) ->
     coerce_types (TypeContext.rem x gamma) b
     |> forall [x]
  | Exists (x, b) ->
     coerce_types (TypeContext.rem x gamma) b
     |> exists [x]

let rec order_all_quantifiers b =
  match b with
  | TTrue | TFalse | TComp _ | LVar _ -> b
  | TNot (b) ->
     not_ (order_all_quantifiers b)
  | TNary (op, bs) ->
     List.map bs ~f:order_all_quantifiers
     |> get_smarts op
  | Exists _ ->
     failwith "WHY IS THERE AN EXISTENTAL HERE?"
  | Forall (x, b) ->
     match order_all_quantifiers b with
     | Forall (y, b) ->
        if Var.size x > Var.size y then
          Forall (x, Forall (y, b))
        else
          Forall (y, Forall (x, b))
     | b -> forall_one x b 

let rec comparisons b : (Var.t * Expr.t) list option =
  let open Option.Let_syntax in
  match b with
  | TTrue | TFalse | LVar _ -> Some []
  | TNot b ->
    comparisons b
  | TComp (_, x, e) when Expr.is_var x ->
    Some ([Expr.get_var x, e])
  | TComp (_, e, x) when Expr.is_var x ->
    Some ([Expr.get_var x, e])
  | TComp _ ->
    Some ([])
  | TNary (_, bs) ->
    List.fold bs ~init:(Some [])
      ~f:(fun comps b ->
          let%bind comps = comps in
          let%map comps' = comparisons b in
          comps @ comps'
        )
  | Forall _ | Exists _ ->
    None

let erase_max_label (ctx : Context.t) : t ->  t =
  let rec loop b =
    match b with
    | TTrue | TFalse | LVar _ -> b
    | TNot b -> not_ (loop b)
    | TNary (op, bs) ->
      List.map bs ~f:loop
      |> get_smarts op
    | TComp (c, e1, e2) ->
      let e1 = Expr.erase_max_label ctx e1 in
      let e2 = Expr.erase_max_label ctx e2 in
      (get_smart_comp c) e1 e2
    | Forall _ | Exists _ ->
      failwith "Cannot erase max label under quantifiers"
  in
  loop

let check (phi : t) (m : Model.t) : bool =
  let sigma x =
    match Model.lookup m x with
    | Some (v, sz) -> Expr.bv v sz
    | None ->
      Log.error "Model %s" @@ lazy (Model.to_string m);
      failwithf "Couldn't find value for %s<%d> in model" (Var.str x) (Var.size x) ()
  in
  let phi = fun_subst sigma phi |> simplify  in
  match phi with
  | TFalse -> false
  | TTrue -> true
  | _ ->
    Log.error "After substituting with:\n%s\n------ " @@ lazy (Model.to_string m);
    Log.error "Got:\n%s\n--------" @@ lazy (to_smtlib phi);
    failwith "[check_one_model] Couldn't simplify model"
