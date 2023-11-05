open Pbench
open DependentTypeChecker
open Programs.HeavyHitter1

let test_infer () =
  HoareNet.infer ~qe:`Enum heavy_hitter_1 None None
  |> Alcotest.(check (neg Equivalences.smt_equiv))
    "Enum CPI is not trivial"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc heavy_hitter_1 None None
  |> Alcotest.(check (neg Equivalences.smt_equiv))
    "Conc CPI is not trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "heavy_hitter_1 infer enum" `Quick test_infer;
  Alcotest.test_case "heavy_hitter_1 infer conc" `Quick test_concolic;
]
