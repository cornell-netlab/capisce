open Pbench
open Equivalences   

   
let cnf_foils () =
  let open BExpr in
  let one = Expr.bvi 1 1 in
  let istrue x = eq_ one (Expr.var x) in
  let prop v = Var.make v 1 |> istrue in
  let a = prop "a" in
  let b = prop "b" in
  let c = prop "c" in
  let d = prop "d" in
  let phi = BExpr.(or_ (and_ a b) (and_ c d)) in
  Alcotest.(check smt_equiv) "logically equivalent" phi (cnf phi)
  
let tests =
  [
    Alcotest.test_case "cnf foils" `Quick cnf_foils;
  ]

  
                   
