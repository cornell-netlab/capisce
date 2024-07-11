open Core
open Capisce
open DependentTypeChecker
open Programs.MCNat

let test_infer_buggy () =
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (mc_nat false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (mc_nat true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (mc_nat false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (mc_nat true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Conc CPI is trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "mc_nat infer enum buggy" `Quick test_infer_buggy;
  Alcotest.test_case "mc_nat infer enum fixed" `Quick test_infer_fixed;
  Alcotest.test_case "mc_nat infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "mc_nat infer conc fixed" `Quick test_concolic_fixed;
]
