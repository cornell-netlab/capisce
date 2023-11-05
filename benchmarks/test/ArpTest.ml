open Pbench
open DependentTypeChecker
open Programs.Arp

let test_infer () =
  HoareNet.infer ~qe:`Enum arp None None
  |> Alcotest.(check (neg Equivalences.smt_equiv))
    "CPI is sat"
    BExpr.false_

let test_concolic () =
  HoareNet.infer ~qe:`Conc arp None None
  |> Alcotest.(check (neg Equivalences.smt_equiv))
    "CPI is sat"
    BExpr.false_

let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "arp infer enum" `Slow test_infer;
  Alcotest.test_case "arp infer conc" `Quick test_concolic;
]
