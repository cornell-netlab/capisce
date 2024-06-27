open Capiscelib
open DependentTypeChecker
open Programs.NetpaxosAcceptor

let test_enum () =
  HoareNet.infer ~qe:`Enum netpaxos_acceptor None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is Valid using enum"
    BExpr.true_

let test_concolic () =
  HoareNet.infer ~qe:`Conc netpaxos_acceptor None None
  |> Alcotest.(check Equivalences.smt_equiv)
    "CPI is valid using concolic"
    BExpr.true_

let tests = [
  Alcotest.test_case "netpaxos_acceptor enum" `Quick test_enum;
  Alcotest.test_case "netpaxos_acceptor concolic" `Quick test_concolic;

]
