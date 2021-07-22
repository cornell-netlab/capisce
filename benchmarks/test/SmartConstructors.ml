open Pbench
open Base_quickcheck    

let count = ref 0   
   
let identity () =
  Test.run_exn
    (module BExpr)
    ~f:(fun b ->
      Printf.printf "%i -- %s -- well_formed? %b\n%!" !count (BExpr.to_smtlib b) (BExpr.well_formed b);
      count := !count + 1;
      [%test_eq: BExpr.t] b (BExpr.simplify b))


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
  
let tests =
  [
    Alcotest.test_case "Variable Generator is well-formed" `Quick well_formed_var;
    Alcotest.test_case "Expression Generator is well-formed" `Quick well_formed_expr;
    Alcotest.test_case "Boolean Generator is well-formed" `Quick well_formed_bexpr;
    Alcotest.test_case "Quickcheck Identity" `Quick identity
  ]

  
                   
