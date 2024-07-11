open Core
open Capisce
open DependentTypeChecker
open Programs.Multiprotocol


let test_infer () =
  HoareNet.infer ~qe:`Enum multiprotocol None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Enum CPI is not true"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc multiprotocol None None
  |> Alcotest.(check @@ neg Equivalences.smt_equiv)
    "Conc CPI is not true"
    BExpr.true_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "07-Multiprotocol infer enum" `Slow test_infer;
  Alcotest.test_case "07-Multiprotocol infer conc" `Quick test_concolic;
]
