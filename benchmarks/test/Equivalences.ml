open Core
open Base_quickcheck
open Pbench

   
let log_eq b1 b2 =
  let res = BExpr.check_iff_str ~timeout:(Some 100) b1 b2 in
  Smt.is_unsat res || Smt.is_unknown res

let bexpr_sexp = Alcotest.testable
              (Fmt.of_to_string (Fn.compose Sexp.to_string [%sexp_of: BExpr.t]))
              (BExpr.(=))

let bexpr = Alcotest.testable
              (Fmt.of_to_string BExpr.to_smtlib)
              (BExpr.(=))
               
let smt_equiv = Alcotest.testable (Fmt.of_to_string BExpr.to_smtlib) (log_eq)
let cmd = Alcotest.testable (Fmt.of_to_string Cmd.to_string) (Cmd.equal)              
let var = Alcotest.testable (Fmt.of_to_string Var.str) (Var.equal)
        
let z3_config =
  let open Sequence in
  let open Test.Config in
  { seed = Seed.Nondeterministic;
    test_count = 100;
    shrink_count = 0;
    sizes = unfold ~init:5 ~f:(function n -> Some (n, n+1));
  } 
