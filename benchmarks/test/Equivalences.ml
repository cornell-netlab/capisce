open Core
open Base_quickcheck
open Pbench
open Cmd

   
let log_eq b1 b2 =
  let res = Solver.check_iff_str ~timeout:(Some 1000) b1 b2 in
  Smt.is_unsat res || Smt.is_unknown res

let bexpr_sexp = Alcotest.testable
              (Fmt.of_to_string (Fn.compose Sexp.to_string [%sexp_of: BExpr.t]))
              (BExpr.(=))

let bexpr = Alcotest.testable
              (Fmt.of_to_string BExpr.to_smtlib)
              (BExpr.(=))

let bigint = Alcotest.testable
               (Fmt.of_to_string Bigint.to_string)
               (Bigint.(=))


let smt_equiv = Alcotest.testable (Fmt.of_to_string BExpr.to_smtlib) (log_eq)
let gcl = Alcotest.testable (Fmt.of_to_string GCL.to_string) (GCL.equal)
let psv = Alcotest.testable (Fmt.of_to_string PassiveGCL.to_string) (PassiveGCL.equal)
let var = Alcotest.testable (Fmt.of_to_string Var.str) (Var.equal)
        
let z3_config =
  let open Sequence in
  let open Test.Config in
  { seed = Seed.Nondeterministic;
    test_count = 60;
    shrink_count = 0;
    sizes = unfold ~init:5 ~f:(function n -> Some (n, n+1));
  } 
