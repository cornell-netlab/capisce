open Base_quickcheck
open Core

let __testing__only__smart = ref `On
   
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

type t =
  | TFalse
  | TTrue
  | TNot of t
  | TBin of bop * t * t
  | TEq of Expr.t * Expr.t
  | Forall of Var.t list * t
  | Exists of Var.t list * t
  [@@deriving eq, sexp, compare, quickcheck]

let (=) = equal

let rec to_smtlib = function
  | TFalse -> "false"
  | TTrue -> "true"
  | TNot t -> Printf.sprintf "(not %s)" (to_smtlib t)
  | TBin (b,t1,t2) ->
     Printf.sprintf "(%s %s %s)" (bop_to_smtlib b) (to_smtlib t1) (to_smtlib t2)
  | TEq (e1,e2) ->
     Printf.sprintf "(= %s %s)" (Expr.to_smtlib e1) (Expr.to_smtlib e2)
  | Forall (vs, t) ->
     Printf.sprintf "(forall (%s) %s)"
       (Var.list_to_smtlib_quant vs)
       (to_smtlib t)
  | Exists (vs, t) ->
     Printf.sprintf "(exists (%s) %s)"
       (Var.list_to_smtlib_quant vs)
       (to_smtlib t)        

let ctor1 ~default ~smart a =
  match !__testing__only__smart with
  | `On -> smart default a
  | `Off ->
     Printf.printf "DEFAULT\n%!";     
     default a
let ctor2 ~default ~smart a b =
  match !__testing__only__smart with
  | `On -> smart default a b
  | `Off ->
     Printf.printf "DEFAULT\n%!";
     default a b
let rec ctor2rec ~default ~smart a b =
  match !__testing__only__smart with
  | `On -> smart (ctor2rec ~default ~smart) default a b
  | `Off -> default a b
        
let false_ = TFalse
let true_ = TTrue
let not_ =
  ctor1
    ~default:(fun b -> TNot b)
    ~smart:(fun default b ->
      Log.print @@ Printf.sprintf "simplifying NOT (%s)" (to_smtlib b);
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
  
let or_ =
  ctor2
    ~default:(fun b1 b2 -> TBin(LOr, b1, b2))    
    ~smart:(fun default b1 b2 ->
      if b1 = false_ then
        b2
      else if b2 = false_ then
        b1
      else if b1 = true_ || b2 = true_ then
        true_
      else
        default b1 b2)

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
    ~default:(fun e1 e2 -> TEq(e1,e2))
    ~smart:(fun default e1 e2 ->
      match Expr.static_eq e1 e2 with
      | None -> default e1 e2
      | Some true -> true_
      | Some false -> false_)

let dumb f =
  __testing__only__smart := `Off;
  let b = f () in
  __testing__only__smart := `On;
  b
  
let get_smart = function
  | LAnd -> and_
  | LOr -> or_
  | LArr -> imp_
  | LIff -> iff_

let rec vars t : Var.t list * Var.t list =
  match t with
  | TFalse
    | TTrue -> ([],[])
  | TNot t -> vars t
  | TBin (_, t1, t2) ->
     Var.(Util.pairs_app_dedup ~dedup (vars t1) (vars t2))
  | TEq (e1, e2) ->
     Var.(Util.pairs_app_dedup ~dedup (Expr.vars e1) (Expr.vars e2))     
  | Forall (vs, b) | Exists (vs, b) ->
     let dvs, cvs = vars b in
     Var.(Util.ldiff ~equal dvs vs, Util.ldiff ~equal cvs vs)
       
let forall_simplify forall vs vsa a op vsb b =
  let phi =
    match op with
    | LAnd -> and_ (forall vsa a) (forall vsb b)
    | LArr -> or_ (forall vsa (not_ a)) (forall vsb b)
    | LOr  -> or_ (forall vsa a) (forall vsb b)
    | LIff -> iff_ (forall vsa a) (forall vsb b)
  in
  Log.print @@ Printf.sprintf "∀-simplifying: ∀ %s. %s\n%!" (Var.list_to_smtlib_quant vs) (to_smtlib phi);        
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
      if List.is_empty vs then
        let () = Log.print @@ Printf.sprintf "Emptiness is a warm gun: %s" (to_smtlib b) in
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
          | TNot (TEq(e1,e2)) | TEq (e1, e2) when Expr.uelim vs' e1 e2 ->
             false_
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
  | TBin (op, b1, b2) -> get_smart op (simplify_inner b1) (simplify_inner b2)
  | TEq (e1, e2) -> eq_ e1 e2
  | Forall (vs, b) -> simplify_inner b |> forall vs
  | Exists (vs, b) -> simplify_inner b |> exists vs

let simplify b =
  Log.print "==SIMPLIFYING==";
  simplify_inner b
  (* let b' = simplify_inner b in
   * if b = b' then
   *   b
   * else
   *   simplify b' *)
            

                    
let rec subst x e t =
  match t with
  | TFalse | TTrue -> t
  | TNot t -> not_ (subst x e t)
  | TBin (op, t1,t2) -> (get_smart op) (subst x e t1) (subst x e t2)
  | TEq (e1,e2) ->
     eq_ (Expr.subst x e e1) (Expr.subst x e e2)
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
       let%map e2 = Expr.quickcheck_generator in
       TEq(e1,e2))
    ]
    ~f:(fun self ->
      [
        (let%map e = self in TNot e);

        (let%bind op = quickcheck_generator_bop in
         let%bind b1 = self in
         let%map b2 = self in
         Printf.printf "Generate LHS %s RHS %s\n%!" (to_smtlib b1) (to_smtlib b2);         
         TBin (op,b1,b2)
        );

        (let%bind b = self in
         Log.print "Generate Forall\n";
         let vs = vars b |> Util.uncurry (@) in
         if List.is_empty vs then
           return b
         else
           let%map v = vars b |> Util.uncurry (@) |> of_list in 
           Forall ([v], b));

        (let%bind b = self in
         Log.print "Generate Exists\n";
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
  | TEq (e1,e2) -> Expr.well_formed e1 && Expr.well_formed e2
  | TBin(_,b1,b2) -> well_formed b1 && well_formed b2
  | TNot b | Forall (_,b) | Exists(_,b) -> well_formed b

let equivalence a b =
  let avars = vars a |> Util.uncurry (@) in
  let bvars = vars b |> Util.uncurry (@) in
  let qa = forall avars a in
  let qb = forall bvars b in
  Log.print @@ Printf.sprintf "CHECKING %s = %s \n%!" (to_smtlib qa) (to_smtlib qb);
  dumb (fun () -> iff_ (forall avars a) (forall bvars b))
  
