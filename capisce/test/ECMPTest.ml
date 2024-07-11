open Capisce
open DependentTypeChecker
open Programs.ECMP

let test_annotations () =
  HoareNet.check_annotations ecmp
   |> Alcotest.(check bool) "check_annotations should pass" true

let test_infer () =
  HoareNet.infer ecmp None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc ecmp None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "ecmp2 annotations" `Quick test_annotations;
  Alcotest.test_case "ecmp2 all_paths inference" `Quick test_infer;
  Alcotest.test_case "ecmp2 concolic inference" `Quick test_concolic;
]
