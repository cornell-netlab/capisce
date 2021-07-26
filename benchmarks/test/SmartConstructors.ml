open Core
open Pbench
open Base_quickcheck    

let count = ref 0   

let z3_returned_sat s =
  let open String in
  (is_substring ~substring:"sat" s || is_substring s ~substring:"unknown")
  && not (is_substring ~substring:"unsat" s)
  && not (is_substring ~substring:"error" s)
    
          
let log_eq b1 b2 =
  let () = Printf.printf "\nEquality\n%s\n = %s\n%!" (BExpr.to_smtlib b1) (BExpr.to_smtlib b2) in
  let smtlib_exp = BExpr.equivalence b1 b2 |> Smt.check_sat ~timeout:(Some 100) [] in
  let () = Printf.printf "Checking Z3 with \n %s \n%!" smtlib_exp in
  let res =  Solver.run_z3 smtlib_exp in
  let () = Printf.printf "Z3 responded with \n %s \n%!" res in
  z3_returned_sat res

let bexpr = Alcotest.testable (Fmt.of_to_string BExpr.to_smtlib) (BExpr.(=))
let smt_equiv = Alcotest.testable (Fmt.of_to_string BExpr.to_smtlib) (log_eq) 
let z3_config =
  let open Sequence in
  let open Test.Config in
    { seed = Seed.Nondeterministic;
      test_count = 100;
      shrink_count = 0;
      sizes = unfold ~init:5 ~f:(function n -> Some (n, n+1));
    } 
              
let identity () =
  Test.run_exn (module BExpr) ~config:z3_config
    ~f:(fun b ->
      [%test_pred: BExpr.t] (log_eq b) (BExpr.simplify b))

let well_formed_var () =
  Test.run_exn (module Var)
    ~f:([%test_pred: Var.t] Var.well_formed)

let well_formed_expr () =
  Test.run_exn (module Expr)
    ~f:([%test_pred: Expr.t] Expr.well_formed)

let well_formed_bexpr () =
  Test.run_exn (module BExpr)
    ~f:([%test_pred: BExpr.t] BExpr.well_formed)


let nested_foralls () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let start =
    dumb (fun () -> not_ (forall [z] (imp_ (eq_ (var z) (bvi 4 32))
                                        (forall [a] (eq_ (bvi 73722014 32) (var a))))))
  in
  let expected = not_ (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) 
                                     (forall [a] (eq_ (bvi 73722014 32) (var a))))) in 
  let simplified = simplify start in 
  Alcotest.(check bexpr) "syntactically equivalent" expected simplified

let nested_foralls1 () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let start =
    dumb (fun () -> (forall [z] (imp_ (eq_ (var z) (bvi 4 32))
                                        (forall [a] (eq_ (bvi 73722014 32) (var a))))))
  in
  let expected = (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) 
                                     (forall [a] (eq_ (bvi 73722014 32) (var a))))) in
  let simplified = simplify start in 
  Alcotest.(check bexpr) "syntactically equivalent" expected simplified  

let single_forall () =
  let open BExpr in
  let open Expr in
  let a = Var.make "a" 32 in
  let start =
    dumb (fun () -> forall [a] (eq_ (bvi 73722014 32) (var a)))
  in
  let expected = forall [a] (eq_ (bvi 73722014 32) (var a)) in
  let simplified = simplify start in 
  Alcotest.(check bexpr) "syntactically equivalent" expected simplified

let true_or_phi__true () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] true_ (or_ true_ b))
  
let phi_or_true__true () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] true_ (or_ b true_))

let false_or_phi__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (or_ false_ b))

let phi_or_false__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (or_ b false_))

(** TESTING CONJUNCTIONS *)
  
let false_and_phi__false () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] false_ (and_ false_ b))

let phi_and_false__false () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] false_ (and_ b false_))

let true_and_phi__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (and_ true_ b))

let phi_and_true__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (and_ b true_))


let reduce_scope_right () =
  Test.run_exn
    ~config:{z3_config with test_count = 50}
    (module struct
       type t = Var.t * BExpr.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let open BExpr in
         let%bind v = Var.quickcheck_generator in
         let f b1 = not (BExpr.vars b1 |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
         let%bind b1 = quickcheck_generator |> filter ~f in
         let%bind b2 = quickcheck_generator in
         return (v, b1, b2)
     end)
    ~f:(fun (v,b1,b2) ->
      let open BExpr in
      let phi = forall [v] (imp_ b1 b2)  |> simplify in
      let phi' = imp_ b1 (forall [v] b2) |> simplify in
      Alcotest.(check smt_equiv) "logically equivalent" phi phi'
    )


let reduce_scope_left () =
  Test.run_exn
    ~config:{z3_config with test_count = 25}
    (module struct
       type t = Var.t * BExpr.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let open BExpr in
         let%bind v = Var.quickcheck_generator in
         let f b2 = not (BExpr.vars b2 |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
         let%bind b1 = quickcheck_generator in
         let%bind b2 = quickcheck_generator |> filter ~f in
         return (v, b1, b2)
     end)
    ~f:(fun (v,b1,b2) ->
      let open BExpr in
      let phi = forall [v] (imp_ b1 b2) |> simplify in
      let phi' = or_ (forall [v] (not_ b1)) b2 |> simplify in
      Alcotest.(check smt_equiv) "logically equivalent" phi phi'
    )

let unused_u_var () =
  Test.run_exn
    ~config:{z3_config with test_count = 50}
    (module struct
       type t = Var.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
          let open Quickcheck.Generator in
          let open Let_syntax in
          let open BExpr in
          let%bind v = Var.quickcheck_generator in
          let f b = not (BExpr.vars b |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
          let%bind b = quickcheck_generator |> filter ~f in
          return (v, b)
     end)
    ~f:(fun (v,b) ->
      let open BExpr in
      Alcotest.(check smt_equiv) "logically equivalent" b (forall [v] b)      
    )

let unused_e_var () =
  Test.run_exn
    ~config:{z3_config with test_count = 50}
    (module struct
       type t = Var.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
          let open Quickcheck.Generator in
          let open Let_syntax in
          let open BExpr in
          let%bind v = Var.quickcheck_generator in
          let f b = not (BExpr.vars b |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
          let%bind b = quickcheck_generator |> filter ~f in
          return (v, b)
     end)
    ~f:(fun (v,b) ->
      let open BExpr in
      [%test_pred: BExpr.t] (log_eq b) (exists [v] b)      
    )

let univ_eq () =
  Test.run_exn
    ~config:z3_config
    (module struct
       type t = Var.t * Expr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let%bind v = Var.quickcheck_generator in
         let f e = Expr.vars e |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v |> not in 
         let%bind e = Expr.quickcheck_generator |> filter ~f in
         return (v, e)
     end)
    ~f:(fun (v,e) ->
      let open BExpr in
      let open Expr in
      Alcotest.(check smt_equiv) "logically equivalent" false_ (forall [v] (eq_ (var v) e)) 
    ) 

let univ_neq () =
  Test.run_exn
    ~config:z3_config
    (module struct
       type t = Var.t * Expr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let%bind v = Var.quickcheck_generator in
         let f e = Expr.vars e |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v |> not in 
         let%bind e = Expr.quickcheck_generator |> filter ~f in
         return (v, e)
     end)
    ~f:(fun (v,e) ->
      let open BExpr in
      let open Expr in
      Alcotest.(check smt_equiv) "logically equivalent" false_ (forall [v] (not_ (eq_ (var v) e))) 
    )   
  
let buggy_qc_example () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let phi () =
    forall [z]
      (imp_
        (not_ (exists [a] (eq_ (var a) (bvi 264974479 32))))
        (iff_ false_
           (eq_ (bsub (bvi 5371006 32) (bneg (bvi 1 32))) (var z))))
  in
  let smart_phi = phi () in
  let dumb_phi = dumb phi in
  Alcotest.(check smt_equiv) "Z3 proves equivalent" dumb_phi smart_phi
  
let buggy_qc_example_literal () =
    let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let got =
    forall [z]
      (imp_
        (not_ (exists [a] (eq_ (var a) (bvi 264974479 32))))
        (iff_ false_
           (eq_ (bsub (bvi 5371006 32) (bneg (bvi 1 32))) (var z)))) in
  let expected =
    dumb @@ fun () ->
              (or_ (exists [a] (eq_ (var a) (bvi 264974479 32)))
                 (forall [z] (iff_ false_ (eq_ (bsub (bvi 5371006 32) (bneg (bvi 1 32))) (var z)))))
  in
  Alcotest.(check bexpr) "literally equivalent" expected got


let buggy_qc_example_1 () =
  let open BExpr in
  let open Expr in
  let m = Var.make "m" 32 in
  let c = Var.make "c" 32 in
  let h = Var.make "h" 32 in
  let z = Var.make "z" 32 in  
  let phi () =
    (iff_ false_
       (forall [m]
          (imp_
             (eq_ (bor (bvi 8 32) (bsub (bvi 3 32) (bvi 1172 32)))
                (var m))
             (forall [c]
                (forall [h]
                   (forall [z]
                      (eq_
                         (bor (var z)
                            (bsub (var h) (var c)))
                         (bneg (bvi 3 32))))))))) in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())

let buggy_qc_example_2 () =
  let open BExpr in
  let open Expr in
  let m = Var.make "m" 32 in
  let y = Var.make "y" 32 in
  let h = Var.make "h" 32 in
  let j = Var.make "j" 32 in
  let phi () =
    (forall [y]
       (imp_
          (iff_
             (or_
                (not_
                   (iff_ (imp_ (not_ false_) (not_ (not_ (not_ false_))))
                      (not_ true_)))
                false_)
             (imp_ false_
                (forall [m] (not_ (eq_ (bneg (bvi 679 32)) (var m))))))
          (forall [j]
             (eq_
                (bor (var y)
                   (bmul (bneg (var h)) (bvi 5173488 32))) 
                (var j)))))
  in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())
  
  

let single_foralls1 () =
    let open BExpr in
    let open Expr in
    let z = Var.make "z" 32 in
    let start =
      dumb (fun () -> (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) false_)))
    in
    let expected = (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) false_)) in  
    let simplified = simplify start in 
    Alcotest.(check bexpr) "syntactically equivalent" expected simplified  
  
  
let nested_foralls_literal () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let got =
    not_ (forall [z] (imp_ (eq_ (var z) (bvi 4 32))
                        (forall [a] (eq_ (bvi 73722014 32) (var a)))))
    |> simplify
  in
  let expected = true_ in
  Alcotest.(check bexpr) "syntactically equivalent" expected got    
  
let and_not_example () =
  let open BExpr in
  let open Expr in
  let c = Var.make "c" 32 |> var in
  let b = Var.make "b" 32 |> var in
  let init =
    dumb (fun () ->
        (and_ (imp_ (eq_ c (badd b (bvi 3999 32))) false_) true_))
  in
  let simplified = BExpr.simplify init in
  [%test_pred: BExpr.t] (log_eq init) simplified

let and_not_example_literal () =
  let open BExpr in
  let open Expr in
  let c = Var.make "c" 32 |> var in
  let b = Var.make "b" 32 |> var in
  let phi = dumb (fun () -> eq_ c (badd b (bvi 3999 32))) in
  let init =
    dumb (fun () -> (and_ (imp_ phi false_) true_)) in
  let expected =
    dumb (fun () -> not_ phi)
  in
  let simplified = BExpr.simplify init in
  Alcotest.(check bexpr) "literal equivalence" expected simplified
  
  
let tests =
  [
    Alcotest.test_case "Variable Generator is well-formed" `Quick well_formed_var;
    Alcotest.test_case "Expression Generator is well-formed" `Quick well_formed_expr;
    Alcotest.test_case "Boolean Generator is well-formed" `Quick well_formed_bexpr;
    Alcotest.test_case "QE buggy example" `Quick and_not_example;
    Alcotest.test_case "simplify((φ⇒⊥) ∧ ⊤) = ¬φ" `Quick and_not_example_literal;
    Alcotest.test_case "simplify(¬∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ ¬∀z. z=4 ⇒ (∀ a. 73722014=a)" `Quick nested_foralls;
    Alcotest.test_case "simplify(∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ ∀z. z=4 ⇒ (∀ a. 73722014=a)" `Quick nested_foralls1;
    Alcotest.test_case "simplify(¬∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ true" `Quick nested_foralls_literal;
    Alcotest.test_case "simplify(∀a. 73722014 = a) = smart(∀a.73722014=a)" `Quick single_forall;
    Alcotest.test_case "smart φ ⇔ dumb φ, φ = ∀ z. (¬ ∃ a. a = V) ⇒ (⊥ ⇔ z = N-1)" `Quick buggy_qc_example;
    Alcotest.test_case "∀ z. (¬ ∃ a. a = V) ⇒ (⊥ ⇔ z = N-1) = (¬ ∃ a. a = V) ⇒ ∀ z. (⊥ ⇔ z = N-1)" `Quick buggy_qc_example_literal;
    Alcotest.test_case "∀m. (m = e) ⇒ ∀ c h z. z|(h-c) = ~3 simplifies correctly" `Quick buggy_qc_example_1;
    Alcotest.test_case "complicated formula simplifies correctly" `Quick buggy_qc_example_2;
    Alcotest.test_case "QC Smart QE" `Slow identity;
    Alcotest.test_case "QC ⊤ ∨ φ = ⊤" `Quick true_or_phi__true;
    Alcotest.test_case "QC ⊥ ∨ φ = φ" `Quick false_or_phi__phi;
    Alcotest.test_case "QC φ ∨ ⊤ = ⊤" `Quick phi_or_true__true;
    Alcotest.test_case "QC φ ∨ ⊤ = φ" `Quick phi_or_false__phi;    
    Alcotest.test_case "QC φ ∧ ⊤ = φ" `Quick phi_and_true__phi;
    Alcotest.test_case "QC ⊤ ∧ φ = φ" `Quick true_and_phi__phi;
    Alcotest.test_case "QC φ ∧ ⊥ = ⊥" `Quick phi_and_false__false;
    Alcotest.test_case "QC ⊥ ∧ φ = ⊥" `Quick false_and_phi__false;
    Alcotest.test_case "QC reduce_scope_right" `Slow reduce_scope_right;
    Alcotest.test_case "QC reduce_scope_left" `Slow reduce_scope_left;
    Alcotest.test_case "QC unused_u_var" `Quick unused_u_var;
    Alcotest.test_case "QC unused_e_var" `Quick unused_e_var;
    Alcotest.test_case "QC univ_eq" `Quick univ_eq;
    Alcotest.test_case "QC univ_neq" `Quick univ_neq;    
  ]

  
                   
