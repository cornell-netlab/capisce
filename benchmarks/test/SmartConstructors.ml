open Core
open Pbench
open Base_quickcheck    

let count = ref 0   

let z3_returned_sat s =
  let open String in
  is_substring ~substring:"sat" s
  && not (is_substring ~substring:"unsat" s)
  || is_substring s ~substring:"unknown"
    
          
let log_eq b1 b2 =
  let () = Printf.printf "\nEquality\n%s\n = %s\n%!" (BExpr.to_smtlib b1) (BExpr.to_smtlib b2) in
  let smtlib_exp = BExpr.equivalence b1 b2 |> Smt.check_sat ~timeout:(Some 100) [] in
  let () = Printf.printf "Checking Z3 with \n %s \n%!" smtlib_exp in
  let res =  Solver.run_z3 smtlib_exp in
  let () = Printf.printf "Z3 responded with \n %s \n%!" res in
  z3_returned_sat res
          
let identity () =
  Test.run_exn
    (module BExpr)
    ~f:(fun b ->
      [%test_pred: BExpr.t] (log_eq b) (BExpr.simplify b))

let well_formed_var () =
  Test.run_exn
    (module Var)
    ~f:([%test_pred: Var.t] Var.well_formed)

let well_formed_expr () =
  Test.run_exn
    (module Expr)
    ~f:([%test_pred: Expr.t] Expr.well_formed)

let well_formed_bexpr () =
  Test.run_exn
    (module BExpr)
    ~f:([%test_pred: BExpr.t] BExpr.well_formed)


let qe_example () =
  let open BExpr in
  let open Expr in
  let c = Var.make "c" 32 |> var in
  let b = Var.make "b" 32 |> var in
  let init =
    dumb (fun () ->
        (and_ (imp_ (eq_ c (bneg (bor (bneg (bneg (band (bneg (bvi 3094 32)) b))) (bsub (bneg (bsub (badd (bvi 15810 32) (bsub (bvi 26 32) (bvi 97 32))) (bvi 234777059 32))) (bvi 41086432 32))))) false_) true_))
  in
  let simplified = BExpr.simplify init in
  [%test_pred: BExpr.t] (log_eq init) simplified

(* let qe_example_literal () =
 *   let open BExpr in
 *   let open Expr in
 *   let c = Var.make "c" 32 |> var in
 *   let b = Var.make "b" 32 |> var in
 *   let init =
 *     dumb (fun () ->
 *         (iff_
 *            (and_ (imp_ (eq_ c (bneg (bor (bneg (bneg (band (bneg (bvi 3094 32)) b))) (bsub (bneg (bsub (badd (bvi 15810 32) (bsub (bvi 26 32) (bvi 97 32))) (bvi 234777059 32))) (bvi 41086432 32))))) false_) true_)
 *            (not_ (eq_ c (bneg (bor (bneg (bneg (band (bneg (bvi 3094 32)) b))) (bsub (bneg (bsub (badd (bvi 15810 32) (bsub (bvi 26 32) (bvi 97 32))) (bvi 234777059 32))) (bvi 41086432 32)))))))) in
 *   let simplified = BExpr.simplify init in
 *   [%test_eq: BExpr.t] init simplified *)
  
  
let tests =
  [
    (* Alcotest.test_case "Variable Generator is well-formed" `Quick well_formed_var;
     * Alcotest.test_case "Expression Generator is well-formed" `Quick well_formed_expr;
     * Alcotest.test_case "Boolean Generator is well-formed" `Quick well_formed_bexpr; *)
    (* Alcotest.test_case "Quickcheck Smart QE" `Quick identity; *)
    Alcotest.test_case "QE buggy example" `Quick qe_example;
  ]

  
                   
