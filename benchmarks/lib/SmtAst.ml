open Core

type typ = Unknown
       | Bool 
       | BitVec 
       [@@deriving eq, sexp, compare, quickcheck]

let typ_to_string s =
  [%sexp_of: typ] s
  |> Sexp.to_string

type ctx = typ String.Map.t
   
type t = True
       | False
       | BV of (Bigint.t * int)
       | Id of (string * typ) (* Ambiguous *)
       | Forall of Var.t list * t
       | Exists of Var.t list * t
       | Not of t
       | Imp of t list
       | Or of t list 
       | And of t list
       | Eq of t * t (* Ambiguous *)
       | BVNot of t
       | BVAnd of t list
       | BVOr of t list
       | BVAdd of t list
       | BVMul of t list
       | BVSub of t list
       | BVXor of t list
       | BVConcat of t list
       | BVExtract of (int * int * t)
       | Shl of t * t
       | Ashr of t * t
       | Lshr of t * t
       | Ult of t * t
       | Ule of t * t
       | Ugt of t * t
       | Uge of t * t
       | Slt of t * t
       | Sle of t * t
       | Sgt of t * t
       | Sge of t * t         
       | Let of (string * t) list * t  (* Ambiguous *)
        [@@deriving eq, sexp, compare, quickcheck]

let to_sexp_string s =
  [%sexp_of: t list] s
  |> Sexp.to_string

let mismatch_error msg =
  failwith (Printf.sprintf "Type Error. Types BitVec and Bool are not compatible: %s" msg)

let inference_mismatch msg =
  failwith (Printf.sprintf "Expected inferred types to both have BitVec or Bool, instead got one of each: %s" msg)

let known_type_error typ =
  typ_to_string typ
  |> Printf.sprintf "input was known to be %s, but we returned UNKNOWN type"
  |> failwith
  
let unify ~error t1 t2 =
  match t1, t2 with
  | Unknown, _ -> t2
  | _, Unknown -> t1
  | Bool, Bool -> Bool
  | BitVec, BitVec -> BitVec
  | BitVec, Bool | Bool, BitVec ->
     mismatch_error (Printf.sprintf "%s: %s %s" error (typ_to_string t1) (typ_to_string t2))

    
let update ~error (gamma : ctx) x t =
  let open String.Map in 
  match find gamma x with
  | None -> add_exn gamma ~key:x ~data:t
  | Some t' ->
     set gamma ~key:x ~data:(unify ~error t t')

let remove (gamma : ctx) x =
  let open String.Map in
  remove gamma (Var.str x)

let get (gamma : ctx) x =
  let open String.Map in
  match find gamma x with
  | None -> Unknown
  | Some t -> t

let update_list ~error gamma xs =
  let f gamma x =
    update ~error gamma (Var.str x) BitVec
  in
  List.fold xs ~init:gamma ~f

let remove_list gamma xs = List.fold xs ~init:gamma ~f:remove
             
let overwrite (gamma : ctx) x t =
  let open String.Map in
  set gamma ~key:x ~data:t

let unify_ctxs ~error ctx1 ctx2 =
  String.Map.merge ctx1 ctx2 ~f:(fun ~key -> function
   | `Left typ | `Right typ -> Some typ
   | `Both (typ1, typ2) ->
      Some (unify ~error:(Printf.sprintf "Got the following error when trying to unify the types for variable %s: %s" key error)
              typ1 typ2))
  
let unify_typestate ~error (b1, g1, t1) (b2, g2, t2) =
  b1 @ b2, unify_ctxs ~error g1 g2, unify ~error t1 t2
  
let expect_bool msg (b, gamma, typ) =
    match typ with
    | Bool -> (b, gamma, typ)
    | Unknown -> known_type_error Bool
    | BitVec -> mismatch_error msg

let expect_bitvec msg (b, gamma, typ) =
    match typ with
    | BitVec -> (b, gamma, typ)
    | Unknown -> known_type_error BitVec
    | Bool -> mismatch_error msg

let rec subst (sigma : t String.Map.t) term : t =
  let f = subst sigma in
  match term with
  | True | False  | BV _ ->
     term
  | Id (x,_) ->
     begin match String.Map.find sigma x with
     | None -> term
     | Some term' -> term'
     end
  | Forall (xs, b) ->
     let sigma' =
       String.Map.filter_keys sigma ~f:(fun x -> List.for_all xs ~f:(fun y -> String.(x <> (Var.str y))))
     in
     Forall (xs, subst sigma' b)
  | Exists (xs, b) ->
     let sigma' =
       String.Map.filter_keys sigma ~f:(fun x -> List.for_all xs ~f:(fun y -> String.(x <> (Var.str y))))
     in
     Forall (xs, subst sigma' b)     
  | Not b ->
     Not (f b)
  | Imp bs ->
     List.map bs ~f
     |> Imp 
  | Or bs ->
     List.map bs ~f
     |> Or
  | And bs ->
     List.map bs ~f
     |> And
  | Eq (term1, term2) ->
     Eq (f term1, f term2)
  | BVNot b ->
     f b
     |> BVNot
  | BVAnd bs ->
     List.map bs ~f
     |> BVAnd
  | BVOr bs ->
     List.map bs ~f
     |> BVOr
  | BVAdd bs ->
     List.map bs ~f
     |> BVAdd 
  | BVMul bs ->
     List.map bs ~f
     |> BVMul
  | BVSub bs ->
     List.map bs ~f
     |> BVSub
  | BVXor bs ->
     List.map bs ~f
     |> BVXor
  | BVConcat bs ->
     List.map bs ~f
     |> BVConcat 
  | BVExtract (lo, hi, b) ->
     BVExtract (lo, hi, f b)
  | Shl (e1, e2) ->
     Shl (f e1, f e2)
  | Ashr (e1, e2) ->
     Ashr (f e1, f e2) 
  | Lshr (e1, e2) ->
     Lshr (f e1, f e2)
  | Ult (e1, e2) ->
     Ult (f e1, f e2)
  | Ule (e1, e2) ->
     Ule (f e1, f e2)
  | Ugt (e1, e2) ->
     Ugt (f e1, f e2)
  | Uge (e1, e2) ->
     Uge (f e1, f e2)
  | Slt (e1, e2) ->
     Slt (f e1, f e2)
  | Sle (e1, e2) ->
     Sle (f e1, f e2)
  | Sgt (e1, e2) ->
     Sgt (f e1, f e2)
  | Sge (e1, e2) ->
     Sge (f e1, f e2)
  | Let (bindings, b) ->
     (* Is this correct? sync with inlining below *)
     let sigma = List.fold bindings ~init:sigma
                   ~f:(fun sigma (x,term) ->
                     let term' = subst sigma term in
                     String.Map.add_exn sigma ~key:x ~data:term' ) in
     subst sigma b
     
     

(* returns (e', τ) where Γ ⊢ e : τ and e' is e with all vars annotated according
   to Γ. *)
let rec infer_type (gamma : ctx) (term : t) typ : (t * ctx * typ) =
  match term, typ with

  (* unknowns *)
  | Id (x,typ'), _ ->
     let typ = unify typ typ' ~error:(Printf.sprintf "%s assumed, annotated:" x) in
     let gamma = update gamma x typ ~error:(Printf.sprintf "%s inferred (%s) conflicted with annotated" x (typ_to_string typ))  in
     let typ'' = get gamma x in
     (* Printf.printf "%s assumed %s, annotated %s, conclude %s\n%!"
      *   x (typ_to_string typ) (typ_to_string typ') (typ_to_string typ'');            *)
     Id (x, typ''), gamma, typ''

  | Eq (term1, term2), _ ->
     let term1, gamma, typ1 = infer_type gamma term1 Unknown in
     let term2, gamma, typ2 = infer_type gamma term2 typ1 in
     begin match typ1, typ2 with
     | Bool, Bool | BitVec, BitVec ->
        Eq(term1,term2), gamma, Bool
     | Unknown, Bool ->
        let term1, gamma, _ = infer_type gamma term1 Bool |> expect_bool "infer (= (?) bool)" in
        (* need to traverse term2 as well?*)
        Eq(term1,term2), gamma, Bool
          
     | Bool, Unknown ->
        let term2, gamma, _ = infer_type gamma term2 Bool |> expect_bool "infer (= bool (?))" in
        Eq(term1, term2), gamma, Bool

     | Unknown, BitVec ->
        let term1, gamma, _ = infer_type gamma term1 BitVec |> expect_bitvec "infer (= bv (?))" in
        Eq(term1, term2), gamma, Bool
     | BitVec, Unknown ->
        let term2, gamma, _ = infer_type gamma term2 BitVec |> expect_bitvec "infer (= bv (?))" in
        Eq(term1, term2), gamma, Bool
     | Bool, BitVec | BitVec, Bool ->
        inference_mismatch "equality"
     | Unknown, Unknown ->
        (* String.Map.to_alist gamma
         * |> List.to_string ~f:(fun (x, typ) -> Printf.sprintf "%s : %s" x (typ_to_string typ))
         * |> Printf.printf "%s\n";  *)
        Eq(term1,term2), gamma, typ2
     end

  | Let _, BitVec -> mismatch_error "let cannot be a bitvec"
  | Let (bindings, b), _ ->
     let sigma = List.fold bindings ~init:String.Map.empty
                   ~f:(fun sigma (x, term) ->
                     String.Map.add_exn sigma ~key:x ~data:(subst sigma term)
                   ) in
     let b = subst sigma b in
     infer_type gamma b Bool
     
  (* Known Booleans *)
  | True, BitVec
  | False, BitVec -> mismatch_error "False is not a BitVec"
  | True, _ -> True, gamma, Bool
  | False, _ -> False, gamma, Bool
  | Forall _, BitVec -> mismatch_error "Forall is not a bitvec"
  | Forall (xs, b), _ ->
     let gamma' = update_list gamma xs ~error:"Forall clashed with gamma" in
     let b, gamma, _ = infer_type gamma' b Bool |> expect_bool "Forall body" in
     let gamma = remove_list gamma xs in
     Forall(xs, b), gamma, Bool
  | Exists _, BitVec -> mismatch_error "Exists is not a bitvec"
  | Exists (xs, b),_ ->
     let gamma' = update_list gamma xs ~error:"Exist clashed with gamma " in
     let b, gamma, _ = infer_type gamma' b Bool |> expect_bool "Exists body bust be a bool" in
     let gamma = remove_list gamma xs in
     Exists(xs, b), gamma, Bool
  | Not _, BitVec -> mismatch_error "Not does not produce a bitvec"
  | Not b, _  ->
     let b, gamma, _ = infer_type gamma b Bool |> expect_bool "Not argument must be a bool" in
     Not b, gamma, Bool
  | Imp _, BitVec -> mismatch_error "Imp does not produce a bitvec"
  | Imp bs, _ ->
     let bs, gamma, _ = infer_type_list gamma bs Bool ~error:"Imp"
                        |> expect_bool "Imp arguments must be bools" in
     Imp bs, gamma, Bool

  | Or _, BitVec -> mismatch_error "Or does not produce a bitvector"
  | Or bs, _ ->
     let bs, gamma, _ = infer_type_list gamma bs Bool ~error:"Or"
                        |> expect_bool "Or arguments must be bools"in
     Or bs, gamma, Bool
  | And _, BitVec -> mismatch_error "And does not produce"
  | And bs, _ ->
     let bs, gamma, _ = infer_type_list gamma bs Bool ~error:"And"
                        |> expect_bool "And arguments must be bools" in
     And bs, gamma, Bool

  (* Known Bitvectors *)
  | BV _, Bool -> mismatch_error "BVs are not booleans"
  | BV _, _ -> term, gamma, BitVec
  | BVNot _, Bool -> mismatch_error "BVNot does not produce a boolean "
  | BVNot e, _ ->
     let e, gamma, _ = infer_type gamma e BitVec |> expect_bitvec "BVNot argument must be a bitvec" in
     BVNot e, gamma, BitVec     

  | BVAnd _, Bool -> mismatch_error "BVAnd does not produce a boolean "
  | BVAnd es, _ ->
     let es, gamma, _ = infer_type_list gamma es BitVec ~error:"BVAnd"
                        |> expect_bitvec "BVAnd arguments must be bitvecs" in
     BVAnd es, gamma, BitVec

  | BVOr _ , Bool -> mismatch_error "BVOr does not produce a boolean"
  | BVOr es, _ ->
     let es, gamma, _ = infer_type_list gamma es BitVec ~error:"BVOr"
                        |> expect_bitvec "BVOr arguments must be bitvecs" in
     BVOr es, gamma, BitVec

  | BVAdd _, Bool -> mismatch_error "BVAdd does not produce a boolean"
  | BVAdd es, _ ->
     let es, gamma, _ = infer_type_list gamma es BitVec ~error:"BVAdd"
                        |> expect_bitvec "BVAdd arguments must be bitvecs" in
     BVAdd es, gamma, BitVec

  | BVMul _, Bool -> mismatch_error "BVMul does not produce a boolean"
  | BVMul es, _ ->
     let es, gamma, _ = infer_type_list gamma es BitVec ~error:"BVMul"
                        |> expect_bitvec "BVMul arguments must be bitvecs" in
     BVMul es, gamma, BitVec
     
  | BVSub _, Bool -> mismatch_error "BVSub does not produce a boolean"
  | BVSub es, _ ->
     let es, gamma, _ = infer_type_list gamma es BitVec ~error:"BVSub"
                        |> expect_bitvec "BVSub's arguments must be bitvecs" in
     BVSub es, gamma, BitVec

  | BVXor _ , Bool -> mismatch_error "BVXor does not produce a boolean"
  | BVXor es, _ ->
     let es, gamma, _ = infer_type_list gamma es BitVec ~error:"BVXor"
                        |> expect_bitvec "BVXor's arguments must be bitvecs" in
     BVXor es, gamma, BitVec
     
  | BVConcat _, Bool -> mismatch_error "BVConcat does not produce a bool"
  | BVConcat es, _ ->
     let es, gamma, _ = infer_type_list gamma es BitVec ~error:"BVConcat"
                        |> expect_bitvec "BVConcat's arguments must be bitvectors" in
     BVConcat es, gamma, BitVec
     
  | BVExtract _ , Bool -> mismatch_error "BVExtract does not produce a bool"
  | BVExtract (lo,hi,e), _ ->
     let e, gamma, _ = infer_type gamma e BitVec |> expect_bitvec "BVExtracts last argument must be a bitvector" in
     BVExtract (lo,hi,e), gamma, BitVec

  | Shl _, Bool -> mismatch_error "Shl does not produce a boolean"
  | Shl (e1, e2), _ ->     
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "shl *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "shl bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over shl failed" in
     Shl(e1,e2), gamma, BitVec

  | Ashr _, Bool -> mismatch_error "Ashr does not produce a boolean"
  | Ashr (e1,e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "ashr *bool _ "in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "shl bv *bool " in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over ashr failed" in
     Ashr (e1,e2), gamma, BitVec

  | Lshr _, Bool -> mismatch_error "Lshr does not produce a boolean"
  | Lshr (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "lshr *bool _ " in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "lshr bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over lshr failed" in
     Lshr (e1, e2), gamma, BitVec

  | Ult _, BitVec -> mismatch_error "Ult does not produce a bitvector"
  | Ult (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "ult *bool _ " in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "ult bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over ult failed" in
     Ult (e1,e2), gamma, Bool

  | Ule _, BitVec -> mismatch_error "Ule does not produce a bitvector"
  | Ule (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "ule *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "ule bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over ule failed" in
     Ule (e1,e2), gamma, Bool

  | Ugt _, BitVec -> mismatch_error "Ugt does not produce a bitvector"
  | Ugt (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "ugt *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "ugt bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over ugt failed" in
     Ugt (e1,e2), gamma, Bool

  | Uge _, BitVec -> mismatch_error "Uge does not produce a bitvector"
  | Uge (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "uge *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "uge bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over uge failed" in
     Uge (e1,e2), gamma, Bool

  | Slt _, BitVec -> mismatch_error "Slt does not produce a bitvector"
  | Slt (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "slt *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "slt bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over slt failed" in
     Slt (e1,e2), gamma, Bool

  | Sle _, BitVec -> mismatch_error "Sle does not produce a bitvector "
  | Sle (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "sle *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "sle bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over sle failed" in
     Sle (e1,e2), gamma, Bool

  | Sgt _, BitVec -> mismatch_error "Sgt does not produce a bitvector"
  | Sgt (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "sgt *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "sgt bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over sgt failed" in
     Sgt (e1,e2), gamma, Bool

  | Sge _, BitVec -> mismatch_error "Sge does not produce a bitvector"
  | Sge (e1, e2), _ ->
     let e1, gamma1, _ = infer_type gamma e1 BitVec |> expect_bitvec "sge *bool _" in
     let e2, gamma2, _ = infer_type gamma e2 BitVec |> expect_bitvec "sge bv *bool" in
     let gamma = unify_ctxs gamma1 gamma2 ~error:"Unifying contexts over sge failed" in
     Sge (e1,e2), gamma, Bool
     

and infer_type_list ~error gamma bs typ =
  let f b =
    infer_type gamma b typ
    |> fun (b,g,t) -> ([b], g, t)
  in
  match List.map bs ~f with
  | [] ->
     failwith @@ Printf.sprintf "%s: mapping over %d arguments returned empty " error (List.length bs)
  | bs -> 
     List.reduce_exn bs ~f:(unify_typestate ~error) 


let fst_map f = Either.map ~first:f ~second:(fun _ -> failwith "got expr, meant to get bexpr")
let snd_map f = Either.map ~second:f ~first:(fun _ -> failwith "got bexpr, meant to get expr")
let fst_bind (f : BExpr.t -> (BExpr.t, Expr.t) Either.t) either : (BExpr.t, Expr.t) Either.t =
  match either with
  | Either.First b -> f b
  | _ -> failwith "got expr, meant to get bexpr"
       
let snd_bind f either =
  match either with
  | Either.Second e -> f e
  | _ -> failwith "got expr, meant to get bexpr"
  

  
let rec to_either_b_expr_inner gamma ~cvs ~dvs term : (BExpr.t, Expr.t) Either.t =
  let open Either in
  let commute_fst = List.fold ~init:(First [])
                      ~f:(fun acc x ->
                        match acc, x with
                        | First acc, First x -> First (acc @ [x])
                        | _, Second e ->
                          failwithf "parsed %s as an expression but expected a BEXPR" (Expr.to_smtlib e) ()
                        | _, _ ->
                          failwith "passed a Second to commute_fst")
  in
  let commute_snd = List.fold ~init:(Second [])
                      ~f:(fun acc x ->
                        match acc, x with
                        | Second acc, Second x -> Second (acc @ [x])
                        | _, _ -> failwith "passed a First to commute_snd" 
                      )
  in
  match term with
  | True ->
     First BExpr.true_
  | False ->
     First BExpr.false_
  | BV (v,w) ->
     Expr.bv v w
     |> Second 
  | Id (x,_) ->
     (* begin match List.find (cvs @ dvs) ~f:(fun c -> String.(Var.str c = x)) with *)
     (* | Some x_var -> *)
     Var.make x (-1) |> Expr.var |> Second
     (* | None -> *)
     (*   failwith (Printf.sprintf "Couldn't identify variable %s from:\n%s" x (Var.list_to_smtlib_decls (cvs @ dvs))) *)
     (* end *)
  | Forall (xs, b) ->
     to_either_b_expr_inner gamma ~cvs ~dvs:(dvs @ xs) b
     |> fst_map @@ BExpr.forall xs

  | Exists (xs, b) ->
     to_either_b_expr_inner gamma ~cvs ~dvs:(dvs @ xs) b
     |> fst_map @@ BExpr.exists xs     
  | Not b ->
     to_either_b_expr_inner gamma b ~cvs ~dvs 
     |> fst_map @@ BExpr.not_
  | Imp bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_fst 
     |> fst_map @@ BExpr.imps_ 
  | Or bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_fst 
     |> fst_map @@ BExpr.ors_
  | And bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_fst 
     |> fst_map @@ BExpr.ands_
  | Eq (term1, term2) ->
     let term1, gamma, typ1 = infer_type gamma term1 Unknown in
     let term2, gamma, typ2 = infer_type gamma term2 Unknown in
     let typ = unify typ1 typ2  ~error:"Could not unify equality type" in
     begin match typ with
     | Unknown ->
        Printf.printf  "Couldn't find the type of %s\n%!" (to_sexp_string [term1]);
        Printf.printf  "Couldn't find the type of %s\n%!" (to_sexp_string [term2]);
        failwith "Couldn't resolve type of equality"
     | BitVec ->
        to_either_b_expr_inner gamma term1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
        to_either_b_expr_inner gamma term2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                        
        First (BExpr.eq_ e1 e2)
     | Bool -> 
        to_either_b_expr_inner gamma term1 ~cvs ~dvs |> fst_bind @@ fun e1 ->
        to_either_b_expr_inner gamma term2 ~cvs ~dvs |> fst_map  @@ fun e2 ->                                        
        BExpr.iff_ e1 e2
     end
  | BVNot b ->
     to_either_b_expr_inner gamma b ~cvs ~dvs 
     |> snd_map @@ Expr.bnot 
  | BVAnd bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_snd
     |> snd_map @@ Expr.(nary band)
  | BVOr bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_snd 
     |> snd_map @@ Expr.(nary bor)
  | BVAdd bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_snd 
     |> snd_map @@ Expr.(nary badd) 
  | BVMul bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_snd 
     |> snd_map @@ Expr.(nary bmul)
  | BVSub bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_snd 
     |> snd_map @@ Expr.(nary bsub)
  | BVXor bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_snd 
     |> snd_map @@ Expr.(nary bsub)
  | BVConcat bs ->
     List.map bs ~f:(to_either_b_expr_inner gamma ~cvs ~dvs)
     |> commute_snd
     |> snd_map @@ Expr.(nary bconcat) 
  | BVExtract (lo, hi, b) ->
     to_either_b_expr_inner gamma b ~cvs ~dvs
     |> snd_map @@ (Expr.bslice lo hi) 
  | Shl (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_map  @@ fun e2 ->                                                 
     Expr.shl_ e1 e2
  | Ashr (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_map  @@ fun e2 ->                                                 
     Expr.ashr_ e1 e2
  | Lshr (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_map  @@ fun e2 ->                                                 
     Expr.lshr_ e1 e2
  | Ult (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.ult_ e1 e2)
  | Ule (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.ule_ e1 e2)
  | Ugt (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.ugt_ e1 e2)
  | Uge (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.uge_ e1 e2)     
  | Slt (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.slt_ e1 e2)          
  | Sle (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.sle_ e1 e2)          
  | Sgt (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.sgt_ e1 e2)          
  | Sge (e1, e2) ->
     to_either_b_expr_inner gamma e1 ~cvs ~dvs |> snd_bind @@ fun e1 ->
     to_either_b_expr_inner gamma e2 ~cvs ~dvs |> snd_bind @@ fun e2 ->                                                 
     First (BExpr.sge_ e1 e2)          
  | Let (_, _) ->
     failwith "`Let`s should've been inlined"  

let to_bexpr gamma ~cvs ~dvs term : BExpr.t =
  match to_either_b_expr_inner gamma ~cvs ~dvs term with
  | First b -> b 
  | Second _ -> failwith "parsed a toplevel expression, it should be a bexpr"              

let translate ~cvs ~dvs term =
  (* Printf.printf "%s" (to_sexp_string [term]);  *)
  let gamma = cvs @ dvs
              |> List.fold ~init:String.Map.empty ~f:(fun acc x ->
                     update acc (Var.str x) BitVec ~error:"BOGUS" ) in
  let b, gamma, _ = infer_type gamma term Bool
                    |> expect_bool "infered the outermost type to be a bitvector when it should be a boolean type" in
  to_bexpr gamma ~cvs ~dvs b
  |> BExpr.simplify
