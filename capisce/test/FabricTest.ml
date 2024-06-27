open Core
open Capiscelib
open DependentTypeChecker
open Programs.Fabric

let test_infer_timeout () =
  HoareNet.infer ~qe:`Enum (fabric true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is trivial"
    BExpr.true_

let test_concolic () =
  Log.parse_flags "pzd";
  HoareNet.infer ~qe:`Conc (fabric true) None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is not trivial"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "Fabric infer enum unannotated" `Slow test_infer_timeout;
  Alcotest.test_case "Fabric infer concolic with annotation" `Quick test_concolic;
]
