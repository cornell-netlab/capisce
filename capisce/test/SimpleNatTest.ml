open Core
open Capiscelib
open Programs.SimpleNat
open DependentTypeChecker

let test_infer_timeout () =
  HoareNet.infer ~qe:`Enum simple_nat None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is not trivial"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc simple_nat None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is not trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "simple_nat infer enum unannotated" `Slow test_infer_timeout;
  Alcotest.test_case "simple_nat  infer concolic with annotation" `Quick test_concolic;
]
