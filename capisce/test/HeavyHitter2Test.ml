open Core
open Capiscelib
open DependentTypeChecker
open Programs.HeavyHitter2

let test_infer_buggy () =
  Printf.printf "GPL Program: %s ------\n" @@ HoareNet.to_string (heavy_hitter_2 false);
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (heavy_hitter_2 false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (heavy_hitter_2 true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (heavy_hitter_2 false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (heavy_hitter_2 true) None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "Conc CPI is trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "heavy_hitter_2 infer enum buggy" `Quick test_infer_buggy;
  Alcotest.test_case "heavy_hitter_2 infer enum fixed" `Quick test_infer_fixed;
  Alcotest.test_case "heavy_hitter_2 infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "heavy_hitter_2 infer conc fixed" `Quick test_concolic_fixed;
]
