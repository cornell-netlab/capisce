(* open Core *)
open Pbench
open Base_quickcheck
open Equivalences

let quant b = BExpr.forall (fst (BExpr.vars b)) b   
let roundtrip b = b |> BExpr.to_smtlib |> BExpr.of_smtlib
let check_roundtrip_smt_equiv b = Alcotest.(check smt_equiv) "parsers equivalent" (quant b) (roundtrip (quant b))
  
   
let smtlib_roundtrip () =
  Test.run_exn (module BExpr)
    ~config:{z3_config with test_count = 200}
    ~f:check_roundtrip_smt_equiv
      

let roundtrip_sle () =
  BExpr.sle_ (Expr.var (Var.make "il" 32)) (Expr.bvi 8 32)
  |> check_roundtrip_smt_equiv
  
let tests =
  [ Alcotest.test_case "QC smt parser roundtrips" `Slow smtlib_roundtrip
  ; Alcotest.test_case "(sle il 8)" `Quick roundtrip_sle
  ]
  
  
