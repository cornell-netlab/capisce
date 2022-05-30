open Base_quickcheck
open Core

let enable_smart_constructors = ref `Off

let q_count = ref 0
let measure s : unit = Log.measure (Printf.sprintf "%f,%d,%s" (Clock.now()) (!q_count) s)  
let incr_q x : unit =
  q_count := !q_count + 1;
  measure (Printf.sprintf "+,%s" (Var.str x))
let decr_q x why : unit =
  q_count := !q_count - 1;
  measure (Printf.sprintf "-,%s,%s" (Var.str x) why) 
   
type bop =
  | LAnd
  | LOr
  | LArr
  | LIff
  [@@deriving eq, sexp, compare, quickcheck]

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
  [@@deriving eq, sexp, compare, quickcheck]

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
  | TNot of t * Var.t list
  | TBin of bop * t * t * Var.t list
  | TComp of comp * Expr.t * Expr.t * Var.t list
  | Forall of Var.t * t
  | Exists of Var.t * t
  [@@deriving eq, sexp, compare, quickcheck]

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
  | TNot (t,_) ->
     Buffer.add_string buff "(not\n";
     to_smtlib_buffer (indent + 1) buff t;
     Buffer.add_string buff ")";
  | TBin (b,t1,t2,_) ->
     Buffer.add_string buff "(";
     Buffer.add_string buff (bop_to_smtlib b);
     Buffer.add_string buff "\n";
     to_smtlib_buffer (indent + 1) buff t1;
     Buffer.add_string buff "\n";
     to_smtlib_buffer (indent + 1) buff t2;
     Buffer.add_string buff ")";
  | TComp (comp, e1, e2,_) ->
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
     

let rec get_labelled_vars_aux = function
  | TFalse | TTrue -> []
  | LVar _ -> []
  | TNot (_,vs) 
    | TBin (_,_,_,vs)  
    | TComp (_,_,_,vs) -> vs
  | Forall (x, t) | Exists (x, t) ->
     Var.(Util.ldiff ~equal (get_labelled_vars_aux t) [x])

let varstime : float ref = ref 0.0

let rec compute_vars (t : t) =
  match t with
  | TFalse | TTrue | LVar _ ->
     ([],[])
  | TNot (t,_) ->
     compute_vars t
  | TBin (_, t1, t2,_) ->
     Var.(Util.pairs_app_dedup ~dedup (compute_vars t1) (compute_vars t2))
  | TComp (_, e1, e2, _) ->
     Var.(Util.pairs_app_dedup ~dedup (Expr.vars e1) (Expr.vars e2))     
  | Forall (x, b) | Exists (x, b) ->
     let dvs, cvs = compute_vars b in
     Var.(Util.ldiff ~equal dvs [x], Util.ldiff ~equal cvs [x])                    
    
let _compute_label_equal b =
  let setify = List.dedup_and_sort ~compare:Var.compare in
  List.equal Var.equal
    (get_labelled_vars_aux b |> setify)
    (compute_vars b |> Util.uncurry (@) |> setify)


let get_labelled_vars b =
  if !Log.debug && not (_compute_label_equal b) then begin
      Printf.printf "------formula------\n%s\n%!" (([%sexp_of: t] b) |> Sexp.to_string);
      Printf.printf "------compute------\n%s\n%!" (compute_vars b |> Util.uncurry (@) |> Var.list_to_smtlib_quant);
      Printf.printf "------labeled------\n%s\n%!" (get_labelled_vars_aux b|> Var.list_to_smtlib_quant);
            
      assert false
    end
  else
    get_labelled_vars_aux b
  
let vars t : Var.t list * Var.t list =
  let c = Clock.start () in
  let vars = get_labelled_vars t in
  let res = List.partition_tf vars ~f:(Fn.non Var.is_symbRow) in
  let dur = Clock.stop c |> Time.Span.to_ms in
  varstime := Float.(!varstime + dur);
  (* Log.print @@ lazy (Printf.sprintf "Vars has taken %fms" !varstime);  *)
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
  | `On -> smart default a b
  | `Off ->
    default a b
let rec ctor2rec ~default ~smart a b =
  match !enable_smart_constructors with
  | `On -> smart (ctor2rec ~default ~smart) default a b
  | `Off -> default a b
        
let false_ = TFalse
let true_ = TTrue
let not_ =
  ctor1
    ~default:(fun b -> TNot (b, get_labelled_vars b))
    ~smart:(fun default b ->
      match b with
      | TFalse -> true_
      | TTrue -> false_
      | TNot (b,_) -> b
      | b -> default b)

let binary_vars b1 b2 =
  (get_labelled_vars b1 @ get_labelled_vars b2)
  |> List.dedup_and_sort ~compare:Var.compare

let binary_exp_vars e1 e2 =
  let vs1 = Expr.vars e1 |> Util.uncurry (@) in
  let vs2 = Expr.vars e2 |> Util.uncurry (@) in
  List.dedup_and_sort (vs1 @ vs2) ~compare:Var.compare 
  
let rec fun_subst f t =
  match t with
  | TFalse | TTrue | LVar _ ->
     t
  | TNot (t, _) ->
     let t = fun_subst f t in
     TNot (t, get_labelled_vars t)
  | TBin (op, t1, t2, _) ->
     let t1 = fun_subst f t1 in
     let t2 = fun_subst f t2 in
     TBin (op, t1, t2, binary_vars t1 t2)     
  | TComp (comp, e1, e2, _) ->
     let e1 = Expr.fun_subst f e1 in
     let e2 = Expr.fun_subst f e2 in
     TComp (comp, e1, e2, binary_exp_vars e1 e2)
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
      TBin(LAnd, b1, b2, binary_vars b1 b2))
    ~smart:(fun default b1 b2 ->  
      if b1 = true_ then
        b2
      else if b2 = true_ then
        b1
      else if b1 = false_ || b2 = false_ then
        false_
      else
        match b1, b2 with
        | TNot (TComp(Eq, e11, e12, _), _),
          TNot (TComp(Eq, e21, e22, _), _) ->
           if Expr.neq_contra (e11, e12) (e21, e22) then
             false_
           else
             default b1 b2
        | TNot (bneg,_), b0 | b0, TNot (bneg,_) ->
           if bneg = b0 then
             false_
           else
             default b1 b2
        | _ -> default b1 b2)

let ands_ = List.fold ~init:true_ ~f:and_
  
let imp_ =
  ctor2
    ~default:(fun b1 b2 ->
      TBin(LArr, b1, b2, binary_vars b1 b2))
    ~smart:(fun default b1 b2 ->
      if b2 = true_ || b1 = false_ then
        true_
      else if b2 = false_ then
        not_ b1
      else if b1 = true_ then
        b2
      else
        match b1 with
        | TComp (Eq, e1, e2,_) when Expr.is_var e1 || Expr.is_var e2 ->
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
    ~default:(fun b1 b2 -> TBin(LOr, b1, b2, binary_vars b1 b2))
    ~smart:(fun default b1 b2 ->
      if b2 = true_ || b1 = true_ then
        true_
      else if b2 = false_ then
        b1
      else if b1 = false_ then
        b2
      else
        match b1, b2 with
        | TNot (TComp (Eq, e1, e2, _), _) as asm, body when Expr.(is_var e1 || is_var e2) ->
           one_point_rule e1 e2 body           
           |> default asm 
        | body, (TNot (TComp (Eq, e1, e2, _), _) as asm) when Expr.(is_var e1 || is_var e2) ->
           one_point_rule e1 e2 body           
           |> default asm 
        | _,_->
        default b1 b2)

let ors_ = List.fold ~init:false_ ~f:or_ 
  
let iff_ =
  ctor2
    ~default:(fun b1 b2 -> TBin(LIff, b1, b2, binary_vars b1 b2))
    ~smart:(fun default b1 b2 ->
      if b1 = b2 then
        true_      
      else
        default b1 b2
    )
  
let iffs_ bs =
  match bs with
  | [b1;b2] -> iff_ b1 b2 
  | _ -> failwith (Printf.sprintf "iffs_ needs a list of length 2, got %d\n%!" (List.length bs))

  
let eq_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Eq,e1,e2, binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 ->
      match Expr.static_eq e1 e2 with
      | None ->
         default e1 e2
      | Some true -> true_
      | Some false -> false_)

let ult_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Ult,e1,e2, binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let ule_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Ule,e1,e2, binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let uge_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Uge,e1,e2,binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let ugt_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Ugt,e1,e2, binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let slt_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Slt,e1,e2, binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let sle_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Sle,e1,e2, binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let sge_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Sge,e1,e2, binary_exp_vars e1 e2))
    ~smart:(fun default e1 e2 -> default e1 e2)

let sgt_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Sgt,e1,e2, binary_exp_vars e1 e2))
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
  | TComp (_,e1,e2,_) ->
     size_ := !size_ + 1 + Expr.size e1 + Expr.size e2;
  | TNot (b,_) ->
     size_ := !size_ + 1;
     size_aux b
  | TBin (_, a, b,_) ->
     size_ := !size_ + 1;
     size_aux a;
     size_aux b
  | Forall (_, b) | Exists (_, b) ->
     size_ := !size_ + 1;
     size_aux b

let size b =
  size_ := 0;
  size_aux b;
  !size_

let ic_ugt default x b e1 e2 =
  if Expr.is_var e1 then
    let v1 = Expr.get_var e1 in
    if Var.equal x v1 then begin
        decr_q x "Ic-ugt1";
        not_ (ugt_ e2 (Expr.bvi (-1) (Var.size v1)))
      end else if Expr.is_var e2 then
      let v2 = Expr.get_var e2 in
      if Var.equal x v2 then begin
          decr_q x "IC-ugt2";
          (eq_ e1 (Expr.bvi 0 (Var.size v2)))
        end
      else
        default x b
    else
      default x b
  else if Expr.is_var e2 then
    let v2 = Expr.get_var e2 in
    if Var.equal x v2 then begin
        decr_q x "ic-ugt3";
        (eq_ e1 (Expr.bvi 0 (Var.size v2)))
      end
    else
      default x b
  else
    default x b


let forall_imp self default x b1 b2 = 
  if occurs_in x b1 && occurs_in x b2 then
    default x (imp_ b1 b2)
  else if occurs_in x b1 then
    or_ (self x (not_ b1)) b2
  else if occurs_in x b2 then
    imp_ b1 (self x b2)
  else begin
      decr_q x "not_free_imp_";
      imp_ b1 b2
    end


let forall_or self default x b1 b2 = 
  if occurs_in x b1 && occurs_in x b2 then
    default x (or_ b1 b2)
  else if occurs_in x b1 then
    or_ (self x b1) b2
  else if occurs_in x b2 then
    or_ b1 (self x b2)
  else begin
      decr_q x "not_free_or_";
      or_ b1 b2
    end
  

  
let forall_one (x : Var.t) b =  
  Log.print @@ lazy (Printf.sprintf "smart constructor for %s (_ BitVec %d) " (Var.str x) (Var.size x));
  Log.size (size b);
  ctor2rec x b
    ~default:(fun x b ->
      (* if Int.(Var.size x = 1 && (size b) < 100) then
       *   let f bit y = if Var.(x = y) then Expr.bvi bit 1 else Expr.var y in
       *   and_
       *     (fun_subst (f 0) b)
       *     (fun_subst (f 1) b)
       * else              *)
        Forall(x,b))      
  (* ~smart:(Fn.const smart) *)
    ~smart:(fun self default x b ->
        Log.size (size b);      
        let bvs = get_labelled_vars b in
        if not (List.exists bvs ~f:(Var.(=) x)) then begin
            decr_q x "not free";
            b
        end else 
          match b with
          | TFalse ->
             decr_q x "false"; false_
          | TTrue ->
             decr_q x "true"; true_
          | TNot (TComp(Eq,e1,e2,_),_) when Expr.uelim `Neq [x] e1 e2 ->
             decr_q x "neq_false"; false_
          | TNot (TComp(Ugt,e1,e2,_),_) ->
             ic_ugt default x b e1 e2              
          | TNot (TBin(LOr,b1,b2,_),_) ->
             self x (and_ (not_ b1) (not_ b2))
          | TComp(Eq, e1, e2,_) when Expr.uelim `Eq [x] e1 e2 ->
             decr_q x "eq_false"; false_
          | TBin (op, b1, b2,_) ->
             begin match op with
             | LArr ->
                forall_imp self default x b1 b2
             | LOr ->
                forall_or self default x b1 b2
             | LAnd ->
                incr_q x;
                and_ (self x b1) (self x b2)
             | LIff -> default x (iff_ b1 b2)
             end
          | Forall(y, b') ->
             (* Log.print @@ lazy (Printf.sprintf "eliminating %s under %s" (Var.str y) (Var.str x));
              * begin match self y b' with
              * | Forall (y,bb) ->
              *    Log.print @@ lazy (Printf.sprintf "couldn't. moving %s out, and %s in" (Var.str y) (Var.str x)); *)
             default y (self x b') 
            (*  | bb ->
             *     Log.print @@ lazy (Printf.sprintf "yes! %s is gone. eliminating %s" (Var.str y) (Var.str x));
             *     self x bb
             * end *)
          | _ ->
             default x b 
    )

let forall xs b = List.fold_right xs ~init:b ~f:forall_one 

let exists_one x b = Exists(x, b)

let exists x b = List.fold_right x ~init:b ~f:exists_one

let rec simplify_inner = function
  | TFalse -> TFalse
  | TTrue -> TTrue
  | LVar a -> LVar a
  | TNot (b,_) -> not_ (simplify_inner b)
  | TBin (op, b1, b2,_) ->
     get_smart op (simplify_inner b1) (simplify_inner b2)
  | TComp (op, e1, e2,_) ->
     get_smart_comp op e1 e2
  | Forall (x, b) -> simplify_inner b |> forall_one x
  | Exists (x, b) -> simplify_inner b |> exists_one x

let simplify b =
  Log.size (size b);
  Log.print @@ lazy "simplify";
  let tmp = !enable_smart_constructors in
  enable_smart_constructors := `On;
  let b' = simplify_inner b in
  enable_smart_constructors := tmp;
  b'
  (* let b' = simplify_inner b in
   * if b = b' then
   *   b
   * else
   *   simplify b' *)
            
let index_subst s_opt t : t =
  match s_opt with
  | None -> t    
  | Some s -> 
     Subst.to_vsub_list s
     |> List.fold ~init:t
          ~f:(fun t (x,x') -> subst x (Expr.var x') t)


let rec label (ctx : Context.t) (b : t) : t =
  match b with
  | TFalse | TTrue | LVar _ -> b
  | TNot (b, _) -> not_ (label ctx b)
  | TBin (bop, b1, b2, _) ->
     (get_smart bop) (label ctx b1) (label ctx b2)
  | TComp (comp, e1, e2, _) ->
     (get_smart_comp comp) (Expr.label ctx e1) (Expr.label ctx e2)
  | Forall _ | Exists _ ->
     failwith "Not sure how to label quantifiers"

let rec nnf (b : t) : t = 
  match b with
  | TFalse | TTrue | LVar _ -> b
  | TComp _ -> b
  | Forall (x, e) -> forall_one x (nnf e)
  | Exists (vs, e) -> exists_one vs (nnf e) 
  | TBin (op, b1, b2, _) ->
     begin match op with
     | LAnd -> and_ (nnf b1) (nnf b2)
     | LOr -> or_ (nnf b1) (nnf b2)
     | LArr -> or_ (nnf (not_ b1)) (nnf b2)
     | LIff -> and_
                 (or_ (nnf (not_ b1)) (nnf b2))
                 (or_ (nnf (not_ b2)) (nnf b1))
     end
  | TNot (b,_) ->
     match b with
     | TFalse -> TTrue
     | TTrue -> TFalse
     | LVar _ -> TNot (b, [])
     | TNot (b,_) -> nnf b
     | TComp _ -> not_ b
     | Forall (vs, b) -> exists_one vs (nnf (not_ b))
     | Exists (vs, b) -> forall_one vs (nnf (not_ b))
     | TBin (op, b1, b2, _) ->
        match op with
        | LAnd -> or_ (nnf (not_ b1)) (nnf (not_ b2))
        | LOr -> and_ (nnf (not_ b1)) (nnf (not_ b2))
        | LIff | LArr -> nnf (not_ (nnf b))
                       
let rec cnf_inner (b : t) : t list list=
  match b with
  | TFalse | TTrue | LVar _ | TComp _ ->
     [[b]]
  | Forall _ ->
     failwith "i swear you shouldn't use me"
  | Exists _ ->
     failwith "what in the world is my purpose"
  | TBin (op, b1, b2, _) ->
     begin match op with
     | LAnd ->
        cnf_inner b1 @ cnf_inner b2 
     | LOr ->
        let open List.Let_syntax in
        let%bind conj1 = cnf_inner b1 in
        let%map conj2 = cnf_inner b2 in
        conj1 @ conj2 |> List.dedup_and_sort ~compare
     | LArr -> failwith "whoops! crap on a carbunckle"
     | LIff -> failwith "whangdoodle winkerdinker" 
     end
  | TNot (b,_) ->
     match b with
     | TFalse -> [[true_]]
     | TTrue -> [[false_]]
     | TComp _ -> [[not_ b]]
     | _ ->
        failwith (Printf.sprintf "You really shouldn't be out here this late with a (not %s) in your hands " (to_smtlib b))


let cnf b =
  Log.print @@ lazy (Printf.sprintf "cnfing.. %i " (size b)); 
  let ands_of_ors = cnf_inner (nnf b) in
  (* let sz = SetOfSet_t.fold ands_of_ors ~init:0 ~f:(fun sum conj -> sum + 1 + (Set_t.length conj)) in *)
  Log.print @@ lazy (Printf.sprintf "un-cnfing...");
  (* enable_smart_constructors := `Off; *)
  let cnf =
    List.fold_left ands_of_ors ~init:true_
      ~f:(fun ands ors ->
        let ored = List.fold_left ors ~f:or_ ~init:false_ in
        and_ ands ored
      )
  in
  (* enable_smart_constructors := `On; *)
  (* Log.print @@ lazy (Printf.sprintf "done. (size %i)" (size cnf)); *)
  cnf


let rec get_conjuncts b =
  match b with
  | TBin (LAnd,b1, b2, _) ->     
     get_conjuncts b1 @ get_conjuncts b2
  | _ ->
     [b]
    
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
       TComp(c,e1,e2, binary_exp_vars e1 e2))
    ]
    ~f:(fun self ->
      [
        (let%map b = self in TNot (b, get_labelled_vars b));

        (let%bind op = quickcheck_generator_bop in
         let%bind b1 = self in
         let%map b2 = self in
         TBin (op,b1,b2, binary_vars b1 b2)
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
       TComp(c,e1,e2, binary_exp_vars e1 e2 ))
    ]
    ~f:(fun self ->
      [
        (let%map b = self in TNot (b, get_labelled_vars b));

        (let%bind op = quickcheck_generator_bop in
         let%bind b1 = self in
         let%map b2 = self in
         TBin (op,b1,b2, binary_vars b1 b2)
        );
      ]
    )
  
let quickcheck_shrinker : t Shrinker.t = Shrinker.atomic
  
let rec well_formed b =
  match b with
  | TTrue | TFalse | LVar _ -> true
  | TComp (_,e1,e2,_) -> Expr.well_formed e1 && Expr.well_formed e2
  | TBin(_,b1,b2,_) -> well_formed b1 && well_formed b2
  | TNot (b,_) | Forall (_,b) | Exists(_,b) -> well_formed b

let rec normalize_names b =
  match b with
  | TTrue | TFalse | LVar _ -> b
  | TComp (comp,e1,e2,_) ->
     let e1' = Expr.normalize_names e1 in
     let e2' = Expr.normalize_names e2 in
     TComp(comp, e1', e2', binary_exp_vars e1' e2')
  | TBin(op,b1,b2,_) ->
     let b1' = normalize_names b1 in
     let b2' = normalize_names b2 in
     TBin(op,b1',b2', binary_vars b1' b2')
  | TNot (b, _) ->
     let b' = normalize_names b in
     TNot (b', get_labelled_vars b')
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
  | TNot (b,_) -> qf b
  | TBin (_,a,b,_) -> qf a && qf b
  | Forall (_,_) ->
     false
  | Exists (_,_) ->
     false

let rec predicate_abstraction_inner abs b : (PredAbs.t * t) =
  match b with
  | TFalse | TTrue | LVar _ -> (abs, b)
  | TComp (_, _, _, vars) ->
     if List.exists vars ~f:(Fn.non Var.is_symbRow) then
       let (x, abs) = PredAbs.abs abs b in
       (abs, LVar x)
     else
       (abs, b)
  | TNot (b,_) ->
     let (abs, b) = predicate_abstraction_inner abs b in
     (abs, not_ b)
  | TBin (op, a, b, _) ->
     let (abs, a) = predicate_abstraction_inner abs a in
     let (abs, b) = predicate_abstraction_inner abs b in
     (abs, (get_smart op) a b)
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

let rec get_abstract_predicates b =
  match b with
  | TFalse | TTrue | TComp _ -> []
  | LVar x -> [x]
  | TNot (b,_) ->
     get_abstract_predicates b
  | TBin (_, a, b, _) ->
     get_abstract_predicates a
     @ get_abstract_predicates b
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
  | TNot (b,_) ->
     not_ (fun_subst_lvar f b)
  | TBin (op, b1, b2, _) ->
     (get_smart op)
       (fun_subst_lvar f b1)
       (fun_subst_lvar f b2)
  | Forall (y, b) ->
     forall_one y (fun_subst_lvar f b)
  | Exists (y, b)->
     exists_one y (fun_subst_lvar f b)

let subst_lvar x b0 =
  fun_subst_lvar (fun y -> if String.(x = y) then b0 else lvar y)
    
    
(** Solver interface Code*)
  
module Ctx = Map.Make (String) 

(* let add_sort x e =
 *   let open SmtAst in
 *   match e with
 *   | Fun (Id "_", [Id "BitVec"; Id n]) ->
 *      Var.make x (int_of_string n)
 *   | Id "Bool" ->
 *      failwith "Not sure how to translate boolean sorts"
 *   | _ -> failwith "unrecognized sort" 
 *      
 *   
 * let rec to_vars (gamma : Var.t Ctx.t) (bound : SmtAst.t list) =
 *   let open SmtAst in
 *   match bound with
 *   | [] -> gamma, []
 *   | Fun (Id x_name, [sort]) :: rst ->
 *      let x = add_sort x_name sort in
 *      let gamma = Ctx.set gamma ~key:x_name ~data:x in
 *      let gamma, vars = to_vars gamma rst in
 *      gamma, x::vars 
 *   | _ ->
 *      failwith "malformed sort" *)

(* let rec to_expr gamma expr_bindings b : Expr.t =
 *   let open SmtAst in
 *   match b with
 *   | Id x ->
 *      begin match Ctx.find gamma x with
 *      | None ->
 *         begin match Ctx.find expr_bindings x with
 *         | None -> 
 *            failwith (x ^ " was missing from expression context and expression bindings")
 *         | Some e ->
 *            e
 *         end
 *      | Some x ->
 *         Expr.var x
 *      end
 *   | Fun (Id "bvnot", [e]) ->
 *      Expr.bnot (to_expr gamma expr_bindings e)
 *   | Fun (Id "_", [Id bv; Id size]) ->
 *      Expr.bv (Bigint.of_string (String.chop_prefix_exn bv ~prefix:"bv")) (Bigint.of_string size |> Bigint.to_int_exn)
 *   | Fun (Id f, [e1; e2]) ->
 *      let e1 = to_expr gamma expr_bindings e1 in
 *      let e2 = to_expr gamma expr_bindings e2 in
 *      begin match f with
 *      | "bvor"  -> Expr.bor e1 e2
 *      | "bvand" -> Expr.band e1 e2
 *      | "bvxor" -> Expr.bxor e1 e2
 *      | "bvadd" -> Expr.badd e1 e2
 *      | "bvmul" -> Expr.bmul e1 e2
 *      | "bvsub" -> Expr.bsub e1 e2
 *      | "concat" -> Expr.bconcat e1 e2
 *      | "bvshl" -> Expr.shl_ e1 e2
 *      | "bvashr" -> Expr.ashr_ e1 e2
 *      | "bvlshr" -> Expr.lshr_ e1 e2
 *      | _ ->
 *         failwith ("unrecognized binary function " ^ f)
 *      end
 *   | Fun (Id "bvor", args) -> List.map args ~f:(to_expr gamma expr_bindings) |> Expr.(nary bor)
 *   | Fun (Id "concat", args) -> List.map args ~f:(to_expr gamma expr_bindings) |> Expr.(nary bconcat)
 *   | Fun (Fun (Id "_", [Id "extract"; Id hi; Id lo]), [arg]) ->
 *      Expr.bslice (int_of_string lo) (int_of_string hi) (to_expr gamma expr_bindings arg)
 *   | Fun (Fun (Id "_", [Id "extract"; Id hi; Id lo]),  args)->
 *      failwith (Printf.sprintf "How do I (_ extract %s %s) %d arguments" hi lo (List.length args)) 
 *     
 *   | Fun (Id f, args) ->
 *      failwith (Printf.sprintf "[expr] gotta support %s over %d args" f (List.length args))
 *   | Fun _ ->
 *      failwith ("unrecognized function " ^ to_sexp_string [b])
 *   | BV (v, w) -> Expr.bv v w
 *   | Forall _ | Exists _ ->
 *      failwith "quantifier are not expressions"
 *   | Let _ ->
 *      failwith "let bindings are not expressions" *)
     
    
(* let rec translate_assignments gamma (bool_bindings : t Ctx.t) (expr_bindings : Expr.t Ctx.t) assignments : (t Ctx.t * Expr.t Ctx.t) =
 *   let open SmtAst in
 *   match assignments with
 *   | [] -> (bool_bindings, expr_bindings)
 *   | Fun (Id var, [bexpr_smt])::rst ->
 *      begin try
 *        let bexpr = to_bexpr_inner gamma bool_bindings expr_bindings bexpr_smt in
 *        let bool_bindings =  Ctx.set bool_bindings ~key:var ~data:bexpr in
 *        translate_assignments gamma bool_bindings expr_bindings rst
 *      with
 *      | Failure _ ->
 *         (\* Log.print @@ lazy (Printf.sprintf "warning: %s" msg); *\)
 *         let expr = to_expr gamma expr_bindings bexpr_smt in
 *         let expr_bindings = Ctx.set expr_bindings ~key:var ~data:expr in
 *         translate_assignments gamma bool_bindings expr_bindings rst
 *      end
 *   | _ ->
 *     failwith "malformed let-binding"
 * and to_bexpr_inner (gamma : Var.t Ctx.t) (bool_bindings : t Ctx.t) (expr_bindings : Expr.t Ctx.t) (b : SmtAst.t) : t =
 *   match b with
 *   | Id "false" ->
 *      false_
 *   | Id "true" ->
 *      true_
 *   | Id x ->
 *      begin match Ctx.find bool_bindings x with
 *      | None ->
 *         failwith ("tried to look up " ^ x ^ " in boolean context, but couldn't find it")
 *      | Some b ->
 *         b
 *      end
 *   | Forall (bound_ids, exp) ->
 *      let gamma, vars = to_vars gamma bound_ids in
 *      forall vars (to_bexpr_inner gamma bool_bindings expr_bindings exp)
 *   | Exists (bound_ids, exp) ->
 *      let gamma, vars = to_vars gamma bound_ids in
 *      exists vars (to_bexpr_inner gamma bool_bindings expr_bindings exp)
 *   | Let (assignments, body) ->
 *      let bool_bindings, expr_bindings = translate_assignments gamma bool_bindings expr_bindings assignments in
 *      to_bexpr_inner gamma bool_bindings expr_bindings body
 *   | Fun (Id x, args) ->
 *      let f = to_bexpr_inner gamma bool_bindings expr_bindings in
 *      begin match x, args with
 *      | "goals", [Fun (Id "goal", goals) ] ->
 *         let goals = List.sub goals ~pos:0 ~len:(List.length goals -4) in
 *         List.map goals ~f |> ands_
 *      | "assert", [phi] ->
 *         f phi
 *      | "not", [a] ->
 *         not_ (f a)
 *      | "and",_ ->
 *         List.map args ~f |> ands_
 *      | "or", _->
 *         List.map args ~f |> ors_
 *      | "=>", _->
 *         List.map args ~f |> imps_
 *      | "=", [a; b] ->
 *         begin try
 *             let a_bool = to_bexpr_inner gamma bool_bindings expr_bindings a in
 *             let b_bool = to_bexpr_inner gamma bool_bindings expr_bindings b in
 *             iff_ a_bool b_bool
 *           with
 *           | Failure _ ->
 *              (\* Log.print @@ lazy (Printf.sprintf "Warning: %s" msg); *\)
 *              let a_expr = to_expr gamma expr_bindings a in
 *              let b_expr = to_expr gamma expr_bindings b in
 *              eq_ a_expr b_expr
 *         end        
 *      | "bvule", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         ule_ e1 e2
 *      | "bvult", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         ult_ e1 e2
 *      | "bvugt", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         ugt_ e1 e2
 *      | "bvuge", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         uge_ e1 e2
 *      | "bvsle", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         sle_ e1 e2
 *      | "bvslt", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         slt_ e1 e2
 *      | "bvsgt", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         sgt_ e1 e2
 *      | "bvsge", [e1; e2] ->
 *         let e1 = to_expr gamma expr_bindings e1 in
 *         let e2 = to_expr gamma expr_bindings e2 in
 *         sge_ e1 e2
 *      | "=", _ | "bvule", _ | "bvult", _ | "bvuge", _ | "bvsle", _ |
 *        "bvslt", _ | "bvsgt", _ | "bvsge", _ ->
 *         failwith (Printf.sprintf "Gotta support %s over %d terms" x (List.length args))
 *         
 *      | _,_ ->
 *         failwith ("unrecognized boolean function: " ^ x)
 *      end
 *   | BV (_, _) ->
 *      failwith "got bitvector when converting to boolean expression:("
 *   | _ ->
 *      failwith "unrecognized expression" *)

let rec coerce_types gamma (b : t) : t =
  match b with
  | TFalse | TTrue | LVar _ -> b                    
  | TNot (b,_)  ->
     not_ (coerce_types gamma b) 

  | TBin (bop, b1, b2, _) ->
     let ctor = get_smart bop in
     let b1 = coerce_types gamma b1 in
     let b2 = coerce_types gamma b2 in
     ctor b1 b2
  | TComp (comp, e1, e2, _) ->
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
  | TNot (b, _) ->
     not_ (order_all_quantifiers b)
  | TBin (o, b1, b2, _) ->
     (get_smart o) (order_all_quantifiers b1) (order_all_quantifiers b2)
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
       
