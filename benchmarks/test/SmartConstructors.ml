open Core
open Pbench
open Base_quickcheck    

let count = ref 0   


let bexpr = Alcotest.testable (Fmt.of_to_string BExpr.to_smtlib) (BExpr.(=))
          
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
          
let identity () =
  Test.run_exn (module BExpr)
    ~f:(fun b ->
      [%test_pred: BExpr.t] (log_eq b) (BExpr.simplify b))

let well_formed_var () =
  Test.run_exn (module Var)
    ~f:([%test_pred: Var.t] Var.well_formed)

let well_formed_expr () =
  Test.run_exn (module Expr)
    ~f:([%test_pred: Expr.t] Expr.well_formed)

let well_formed_bexpr () =
  let config : Test.Config.t =
    let open Sequence in
    let open Test.Config in
    { seed = Seed.Nondeterministic;
      test_count = 1;
      shrink_count = 0;
      sizes = unfold ~init:5 ~f:(function n -> Some (n, n*2));
    }
  in
  Test.run_exn (module BExpr)  ~config
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
    Alcotest.test_case "Quickcheck Smart QE" `Slow identity;
    Alcotest.test_case "QE buggy example" `Quick and_not_example;
    Alcotest.test_case "simplify((φ⇒⊥) ∧ ⊤) = ¬φ" `Quick and_not_example_literal;
    Alcotest.test_case "simplify(¬∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ ¬∀z. z=4 ⇒ (∀ a. 73722014=a)" `Quick nested_foralls;
    Alcotest.test_case "simplify(∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ ∀z. z=4 ⇒ (∀ a. 73722014=a)" `Quick nested_foralls1;
    Alcotest.test_case "simplify(¬∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ true" `Quick nested_foralls_literal;
    Alcotest.test_case "simplify(∀a. 73722014 = a) = smart(∀a.73722014=a)" `Quick single_forall;
    Alcotest.test_case "Quickcheck ⊤ ∨ ϕ = ⊤" `Quick true_or_phi__true;
  ]

  
                   
