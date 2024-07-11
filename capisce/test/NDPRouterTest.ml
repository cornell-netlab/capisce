open Capisce
open DependentTypeChecker
open Programs.NDPRouter


let test_infer () =
  HoareNet.infer ndp_router None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc ndp_router None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "ndp_router all_paths inference" `Quick test_infer;
  Alcotest.test_case "ndp_router concolic inference" `Quick test_concolic;
]
