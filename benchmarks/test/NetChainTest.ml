open Core
open Pbench
open DependentTypeChecker
open Programs.NetChain

let test_infer_timeout () =
  HoareNet.infer ~qe:`Enum netchain None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc netchain None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is not trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "NetChain infer enum unannotated" `Slow test_infer_timeout;
  Alcotest.test_case "NetChain infer concolic with annotation" `Quick test_concolic;
]
