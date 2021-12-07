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
      Log.print @@ lazy (Printf.sprintf "simplifying NOT (%s)" (to_smtlib b));
      match b with
      | TFalse -> true_
      | TTrue -> false_
      | TNot b -> b
      | b -> default b)
           
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

let rec vars t : Var.t list * Var.t list =
  match t with
  | TFalse
    | TTrue -> ([],[])
  | TNot t -> vars t
  | TBin (_, t1, t2) ->
     Var.(Util.pairs_app_dedup ~dedup (vars t1) (vars t2))
  | TComp (_, e1, e2) ->
     Var.(Util.pairs_app_dedup ~dedup (Expr.vars e1) (Expr.vars e2))     
  | Forall (vs, b) | Exists (vs, b) ->
     let dvs, cvs = vars b in
     Var.(Util.ldiff ~equal dvs vs, Util.ldiff ~equal cvs vs)
       
let forall_simplify forall vs vsa a op vsb b =
  let phi =
    match op with
    | LAnd ->
       and_ (forall vsa a) (forall vsb b)
    | LArr ->
       let out = or_ (forall vsa (not_ a)) (forall vsb b) in
       Log.print @@ lazy (Printf.sprintf "(or (forall (%s) %s) (forall (%s) %s))\n became %s\n"
                            (Var.list_to_smtlib_quant vsa) (to_smtlib (not_ a)) (Var.list_to_smtlib_quant vsb) (to_smtlib b)
                            (to_smtlib out));
       out
    | LOr  ->
       or_ (forall vsa a) (forall vsb b)
    | LIff ->
       iff_ (forall vsa a) (forall vsb b)
  in
  Log.print @@ lazy (Printf.sprintf "∀-simplifying: ∀ %s. %s\n%!" (Var.list_to_smtlib_quant vs) (to_smtlib phi));
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
      Log.print @@ lazy (Printf.sprintf "%s" (Forall (vs, b) |> to_smtlib));
      if List.is_empty vs then
        let () = Log.print @@ lazy (Printf.sprintf "Emptiness is a warm gun: %s" (to_smtlib b)) in
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
                Log.print @@ lazy (Printf.sprintf
                                     "*****\nof %s filtered to %s,\n(%s) are in\n%s\n\nand (%s) are in%s\n*****\n"
                                     (Var.list_to_smtlib_quant vs)
                                     (Var.list_to_smtlib_quant vs')
                                     (Var.list_to_smtlib_quant vs1)
                                     (to_smtlib b1)
                                     (Var.list_to_smtlib_quant vs2)
                                     (to_smtlib b2));
                
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
            

                    
let rec subst x e t =
  match t with
  | TFalse | TTrue -> t
  | TNot t -> not_ (subst x e t)
  | TBin (op,t1,t2) -> get_smart op (subst x e t1) (subst x e t2)
  | TComp (comp,e1,e2) ->
     get_smart_comp comp (Expr.subst x e e1) (Expr.subst x e e2)
  | Forall (vs, t) ->
     if List.exists vs ~f:(Var.(=) x) then
       forall vs t
     else
       Forall(vs, subst x e t)
  | Exists (vs, t) ->
     if List.exists vs ~f:(Var.(=) x) then
       Exists (vs, t)
     else
       Exists (vs, subst x e t)         
     

let index_subst s_opt t : t =
  match s_opt with
  | None -> t    
  | Some s -> 
     Subst.to_vsub_list s
     |> List.fold ~init:t
          ~f:(fun t (x,x') -> subst x (Expr.var x') t)

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
  

let rec size = function
  | TFalse | TTrue -> 1
  | TComp (_,e1,e2) -> Expr.size e1 + 1 + Expr.size e2
  | TNot b -> size b + 1
  | TBin (_, a, b) -> 1 + size a + size b
  | Forall (vs, b) | Exists (vs, b) ->
     1 + List.length vs + size b
    
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
     
  
