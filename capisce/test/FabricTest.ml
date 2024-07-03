open Core
open Capiscelib
open DependentTypeChecker
open Programs.Fabric

let test_count_bits () =
  let vars = HoareNet.vars (fabric false) in
  let data_vars = 
    List.filter vars ~f:(Fn.non Var.is_symbRow) 
    |> Var.dedup
  in  
  List.sum (module Int) data_vars ~f:(Var.size)
  |> Alcotest.(check @@ neg int) "equal" 0
  

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
  Alcotest.test_case "Fabric uses nonzero dataplane bits" `Quick test_count_bits;
  Alcotest.test_case "Fabric infer enum unannotated" `Slow test_infer_timeout;
  Alcotest.test_case "Fabric infer concolic with annotation" `Quick test_concolic;
]
