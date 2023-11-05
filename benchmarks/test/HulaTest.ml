open Core
open Pbench
open DependentTypeChecker
open Programs.Hula

let test_infer_buggy () =
  Printf.printf "GPL Program: %s ------\n" @@ HoareNet.to_string (hula false);
  Alcotest.check_raises
    "Enum CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Enum (hula false) None None))

let test_infer_fixed () =
  HoareNet.infer ~qe:`Enum (hula true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.false_

let test_concolic_buggy () =
  Alcotest.check_raises
    "Conc CPI is unsolveable"
    (Failure "unsolveable")
    (fun () -> ignore (HoareNet.infer ~qe:`Conc (hula false) None None))

let test_concolic_fixed () =
  HoareNet.infer ~qe:`Conc (hula true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is sat"
    BExpr.false_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "Hula enum buggy" `Slow test_infer_buggy;
  Alcotest.test_case "Hula infer enum fixed" `Slow test_infer_fixed;
  Alcotest.test_case "Hula infer conc buggy" `Quick test_concolic_buggy;
  Alcotest.test_case "Hula infer conc fixed" `Quick test_concolic_fixed;
]
