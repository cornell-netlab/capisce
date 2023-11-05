open Pbench
open Programs.Resubmit
open DependentTypeChecker

let test_infer () =
  HoareNet.infer resubmit None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc resubmit None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "resubmit all_paths inference" `Quick test_infer;
  Alcotest.test_case "resubmit concolic inference" `Quick test_concolic;
]
