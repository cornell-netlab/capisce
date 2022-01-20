open Base_quickcheck
open Core

let enable_smart_constructors = ref `Off
   
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
  | TNot of t
  | TBin of bop * t * t
  | TComp of (comp * Expr.t * Expr.t)
  | Forall of Var.t list * t
  | Exists of Var.t list * t
  [@@deriving eq, sexp, compare, quickcheck]

type s = t (*hack, is there a better way?*)        
module Set_t = Set.Make (struct
                 type t = s
                 let sexp_of_t = sexp_of_t
                 let t_of_sexp = t_of_sexp
                 let compare = compare
               end)

module SetOfSet_t = Set.Make (Set_t)           

let (=) = equal
           
let rec to_smtlib_aux indent b =
  let space = Util.space (2 * indent) in
  match b with
  | TFalse ->
     Printf.sprintf "%sfalse" space
  | TTrue ->
     Printf.sprintf "%strue" space
  | TNot t ->
     Printf.sprintf "%s(not\n%s)" space (to_smtlib_aux (indent + 1) t)
  | TBin (b,t1,t2) ->
     Printf.sprintf "%s(%s\n%s\n%s)"
       space
       (bop_to_smtlib b)
       (to_smtlib_aux (indent + 1) t1)
       (to_smtlib_aux (indent + 1) t2)
  | TComp (comp, e1, e2) ->
     Printf.sprintf "%s(%s %s %s)"
       space
       (comp_to_smtlib comp)
       (Expr.to_smtlib e1)
       (Expr.to_smtlib e2)
  | Forall (vs, t) ->
     Printf.sprintf "%s(forall (%s)\n %s)\n"
       space
       (Var.list_to_smtlib_quant vs)
       (to_smtlib_aux (indent + 1) t)
  | Exists (vs, t) ->
     Printf.sprintf "%s(exists (%s)\n %s)\n"
       space
       (Var.list_to_smtlib_quant vs)
       (to_smtlib_aux (indent + 1) t)        

let to_smtlib = to_smtlib_aux 0
    
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
    ~default:(fun b -> TNot b)
    ~smart:(fun default b ->
      match b with
      | TFalse -> true_
      | TTrue -> false_
      | TNot b -> b
      | b -> default b)


let rec fun_subst f t =
  match t with
  | TFalse | TTrue -> t
  | TNot t -> not_ (fun_subst f t)
  | TBin (op,t1,t2) -> TBin (op, fun_subst f t1, fun_subst f t2)
  | TComp (comp,e1,e2) ->
     TComp (comp, Expr.fun_subst f e1, Expr.fun_subst f e2)
  | Forall (vs, t) ->
     let f' x = if List.exists vs ~f:(Var.(=) x) then
                  Expr.var x
                else f x in
     Forall (vs, fun_subst f' t)
  | Exists (vs, t) ->
     let f' x = if List.exists vs ~f:(Var.(=) x) then
                  Expr.var x
                else
                  f x in
     Exists (vs, fun_subst f' t) 
                    
let subst x e t =
  let f y = if Var.(y = x) then e else Expr.var y in
  fun_subst f t
  
let one_point_rule e1 e2 b : t =
  if Expr.is_var e1 then
    let v1 = Expr.get_var e1 in
    if Expr.is_var e2 then
      let v2 = Expr.get_var e2 in
      if not (Var.is_symbRow v2) then
        subst v2 e1 b
      else
        subst v1 e2 b
    else
      subst v1 e2 b
  else if Expr.is_var e2 then
    let v2 = Expr.get_var e2 in    
    subst v2 e1 b
  else
    failwith "called one_point_rule but nothing was there!"

let and_ =
  ctor2
    ~default:(fun b1 b2 -> TBin(LAnd, b1, b2))
    ~smart:(fun default b1 b2 ->  
      if b1 = true_ then
        b2
      else if b2 = true_ then
        b1
      else if b1 = false_ || b2 = false_ then
        false_
      else default b1 b2)
  
let imp_ =
  ctor2
    ~default:(fun b1 b2 -> TBin(LArr, b1, b2))
    ~smart:(fun default b1 b2 ->
      if b2 = true_ || b1 = false_ then
        true_
      else if b2 = false_ then
        not_ b1
      else if b1 = true_ then
        b2
      else
        match b1 with
        | TComp (Eq, e1, e2) when Expr.is_var e1 || Expr.is_var e2 ->
           default b1 (one_point_rule e1 e2 b2)
        | _ ->
           default b1 b2)

let or_ =
    ctor2
    ~default:(fun b1 b2 -> TBin(LOr, b1, b2))
    ~smart:(fun default b1 b2 ->
      if b2 = true_ || b1 = true_ then
        true_
      else if b2 = false_ then
        b1
      else if b1 = false_ then
        b2
      else
        match b1, b2 with
        | TNot (TComp (Eq, e1, e2)) as asm, body when Expr.(is_var e1 || is_var e2) ->
           one_point_rule e1 e2 body           
           |> default asm 
        | body, (TNot (TComp (Eq, e1, e2) as asm)) when Expr.(is_var e1 || is_var e2) ->
           one_point_rule e1 e2 body           
           |> default asm 
        | _,_->
        default b1 b2)
  
let iff_ =
  ctor2
    ~default:(fun e1 e2 -> TBin(LIff, e1, e2))
    ~smart:(fun default e1 e2 ->
      if e1 = e2 then
        true_      
      else
        default e1 e2
    )
                
let eq_ =
  ctor2
    ~default:(fun e1 e2 -> TComp(Eq,e1,e2))
    ~smart:(fun default e1 e2 ->
      match Expr.static_eq e1 e2 with
      | None -> default e1 e2
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

let varstime : float ref = ref 0.0

let rec vars_inner (t : t) =
  match t with
  | TFalse
    | TTrue -> ([],[])
  | TNot t -> vars_inner t
  | TBin (_, t1, t2) ->
     Var.(Util.pairs_app_dedup ~dedup (vars_inner t1) (vars_inner t2))
  | TComp (_, e1, e2) ->
     Var.(Util.pairs_app_dedup ~dedup (Expr.vars e1) (Expr.vars e2))     
  | Forall (vs, b) | Exists (vs, b) ->
     let dvs, cvs = vars_inner b in
     Var.(Util.ldiff ~equal dvs vs, Util.ldiff ~equal cvs vs)

                         
let vars t : Var.t list * Var.t list =
  let c = Clock.start () in
  let res = vars_inner t in
  let dur = Clock.stop c |> Time.Span.to_ms in
  varstime := Float.(!varstime + dur);
  Log.print @@ lazy (Printf.sprintf "Vars has taken %fms" !varstime); 
  res
     
let forall_simplify forall vs vsa a op vsb b =
  let phi =
    match op with
    | LAnd ->
       and_ (forall vsa a) (forall vsb b)
    | LArr ->
       or_ (forall vsa (not_ a)) (forall vsb b)
    | LOr  ->
       or_ (forall vsa a) (forall vsb b)
    | LIff ->
       iff_ (forall vsa a) (forall vsb b)
  in
  (* Log.print @@ lazy (Printf.sprintf "∀-simplifying: ∀ %s. %s\n%!" (Var.list_to_smtlib_quant vs) (to_smtlib phi)); *)
  if Int.(List.length vsa = 0 && List.length vsb = 0) then
    Forall(vs, phi)
  else
    forall vs phi
            
let forall vs b =
  ctor2rec vs b
    ~default:(fun vs b ->
      if List.is_empty vs then
        b
      else
        Forall(vs,b)      
    )
    ~smart:(fun self default vs b ->
      (* Log.print @@ lazy (Printf.sprintf "%s" (Forall (vs, b) |> to_smtlib)); *)
      if List.is_empty vs then
        (* let () = Log.print @@ lazy (Printf.sprintf "Emptiness is a warm gun: %s" (to_smtlib b)) in *)
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
          | TNot (TComp(Eq,e1,e2)) when Expr.uelim `Neq vs' e1 e2 -> false_
          | TComp(Eq, e1,e2) when Expr.uelim `Eq vs' e1 e2 -> false_
          | TBin (op, b1, b2) ->
             begin match op with
             | LArr | LOr ->
                let open Util in
                let dedup = List.dedup_and_sort ~compare:Var.compare in
                let frees1 = vars b1 |> uncurry (@) |> dedup |> linter ~equal:Var.equal vs' in
                let frees2 = vars b2 |> uncurry (@) |> dedup |> linter ~equal:Var.equal vs' in
                (* vs2 = vs' ∩ (frees(b2) \ frees(b1))
                 * vs1 = vs' ∩ (frees(b1) \ frees(b2)) *)                
                let vs1 = Var.(ldiff ~equal frees1 frees2) |> dedup in
                let vs2 = Var.(ldiff ~equal frees2 frees1) |> dedup in
                let vs'' = Var.(linter ~equal frees1 frees2) |> dedup in 
                (* its the case that vs' = vs'' @ vs2 @ vs1 *)
                (* This is a simple sanity check *)
                (* Log.print @@ lazy (Printf.sprintf
                 *                      "*****\nof %s filtered to %s,\n(%s) are in\n%s\n\nand (%s) are in%s\n*****\n"
                 *                      (Var.list_to_smtlib_quant vs)
                 *                      (Var.list_to_smtlib_quant vs')
                 *                      (Var.list_to_smtlib_quant vs1)
                 *                      (to_smtlib b1)
                 *                      (Var.list_to_smtlib_quant vs2)
                 *                      (to_smtlib b2)); *)
                
                assert(Int.(List.length vs' = List.length(vs'' @ vs2 @ vs1)));
                
                forall_simplify self vs'' vs1 b1 op vs2 b2
             | LAnd -> and_ (self vs b1) (self vs b2)
             | LIff -> default vs' (iff_ b1 b2)
             end
          | Forall(vs'', b') -> self (Var.dedup (vs' @ vs'')) b'
          | _ ->
             default vs b 
    )
    

    
let exists vs b = Exists(vs, b)

let rec simplify_inner = function
  | TFalse -> TFalse
  | TTrue -> TTrue
  | TNot b -> not_ (simplify_inner b)
  | TBin (op, b1, b2) ->
     get_smart op (simplify_inner b1) (simplify_inner b2)
  | TComp (op, e1, e2) ->
     get_smart_comp op e1 e2
  | Forall (vs, b) -> simplify_inner b |> forall vs
  | Exists (vs, b) -> simplify_inner b |> exists vs

let simplify b =
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
  | TFalse -> TFalse
  | TTrue -> TTrue
  | TNot b -> TNot (label ctx b)
  | TBin (bop, b1, b2) ->
     TBin (bop, label ctx b1, label ctx b2)
  | TComp (comp, e1, e2) ->
     TComp (comp, Expr.label ctx e1, Expr.label ctx e2) 
  | Forall _ | Exists _ ->
     failwith "Not sure how to label quantifiers"

let rec nnf (b : t) : t = 
  match b with
  | TFalse | TTrue -> b
  | TComp _ -> b
  | Forall (vs, e) -> forall vs (nnf e)
  | Exists (vs, e) -> exists vs (nnf e) 
  | TBin (op, b1, b2) ->
     begin match op with
     | LAnd -> and_ (nnf b1) (nnf b2)
     | LOr -> or_ (nnf b1) (nnf b2)
     | LArr -> or_ (nnf (not_ b1)) (nnf b2)
     | LIff -> and_
                 (or_ (nnf (not_ b1)) (nnf b2))
                 (or_ (nnf (not_ b2)) (nnf b1))
     end
  | TNot b ->
     match b with
     | TFalse -> TTrue
     | TTrue -> TFalse
     | TNot b -> nnf b
     | TComp _ -> not_ b
     | Forall (vs, b) -> exists vs (nnf (not_ b))
     | Exists (vs, b) -> forall vs (nnf (not_ b))
     | TBin (op, b1, b2) ->
        match op with
        | LAnd -> or_ (nnf (not_ b1)) (nnf (not_ b2))
        | LOr -> and_ (nnf (not_ b1)) (nnf (not_ b2))
        | LIff | LArr -> nnf (not_ (nnf b))
                       
let rec cnf_inner (b : t) : t list list=
  match b with
  | TFalse | TTrue | TComp _ ->
     [[b]]
  | Forall _ ->
     failwith "I swear, you shouldnt use me"
  | Exists _ ->
     failwith "what in the world is my purpose"
  | TBin (op, b1, b2) ->
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
  | TNot b ->
     match b with
     | TFalse -> [[true_]]
     | TTrue -> [[false_]]
     | TComp _ -> [[not_ b]]
     | _ ->
        failwith (Printf.sprintf "You really shouldn't be out here this late with a (not %s) in your hands " (to_smtlib b))

let rec size = function
  | TFalse | TTrue -> 1
  | TComp (_,e1,e2) -> Expr.size e1 + 1 + Expr.size e2
  | TNot b -> size b + 1
  | TBin (_, a, b) -> 1 + size a + size b
  | Forall (vs, b) | Exists (vs, b) ->
     1 + List.length vs + size b

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
  | TBin (LAnd,b1, b2) ->     
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
       TComp(c,e1,e2))
    ]
    ~f:(fun self ->
      [
        (let%map e = self in TNot e);

        (let%bind op = quickcheck_generator_bop in
         let%bind b1 = self in
         let%map b2 = self in
         TBin (op,b1,b2)
        );

        (let%bind b = self in
         let vs = vars b |> Util.uncurry (@) in
         if List.is_empty vs then
           return b
         else
           let%map v = vars b |> Util.uncurry (@) |> of_list in 
           Forall ([v], b));

        (let%bind b = self in
         let vs = vars b |> Util.uncurry (@) in         
         if List.is_empty vs then
           return b
         else
           let%map v = vars b |> Util.uncurry (@) |> of_list in          
           Exists ([v], b)
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
       TComp(c,e1,e2))
    ]
    ~f:(fun self ->
      [
        (let%map e = self in TNot e);

        (let%bind op = quickcheck_generator_bop in
         let%bind b1 = self in
         let%map b2 = self in
         TBin (op,b1,b2)
        );
      ]
    )
  
let quickcheck_shrinker : t Shrinker.t = Shrinker.atomic
  
let rec well_formed b =
  match b with
  | TTrue | TFalse -> true
  | TComp (_,e1,e2) -> Expr.well_formed e1 && Expr.well_formed e2
  | TBin(_,b1,b2) -> well_formed b1 && well_formed b2
  | TNot b | Forall (_,b) | Exists(_,b) -> well_formed b

let rec normalize_names b =
  match b with
  | TTrue | TFalse -> b
  | TComp (comp,e1,e2) ->
     let e1' = Expr.normalize_names e1 in
     let e2' = Expr.normalize_names e2 in
     TComp(comp, e1', e2')
  | TBin(op,b1,b2) ->
     let b1' = normalize_names b1 in
     let b2' = normalize_names b2 in
     TBin(op,b1',b2')
  | TNot b ->
     TNot (normalize_names b)
  | Forall (xs,b) ->
     Forall (List.map xs ~f:Var.normalize_name, normalize_names b)
  | Exists(xs,b) ->
     Exists (List.map xs ~f:Var.normalize_name, normalize_names b)
  
                                         
let equivalence a b =
  let avars = vars a |> Util.uncurry (@) in
  let bvars = vars b |> Util.uncurry (@) in
  dumb (fun () -> iff_ (forall avars a) (forall bvars b))
  
    
let rec qf = function
  | TFalse
    | TTrue
    | TComp _ -> true
  | TNot b -> qf b
  | TBin (_,a,b) -> qf a && qf b
  | Forall ([],b) ->
     qf b
  | Forall (_,_) ->
     false
  | Exists ([],b) ->
     qf b
  | Exists (_,_) ->
     false       
