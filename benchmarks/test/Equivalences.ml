open Core
open Pbench

let z3_returned_sat s =
  let open String in
  (is_substring ~substring:"sat" s || is_substring s ~substring:"unknown")
  && not (is_substring ~substring:"unsat" s)
  && not (is_substring ~substring:"error" s)

   
let log_eq b1 b2 =
  let () = Printf.printf "\nEquality\n%s\n = %s\n%!" (BExpr.to_smtlib b1) (BExpr.to_smtlib b2) in
  let smtlib_exp = BExpr.equivalence b1 b2 |> Smt.check_sat ~timeout:(Some 100) [] in
  let () = Printf.printf "Checking Z3 with \n %s \n%!" smtlib_exp in
  let res =  Solver.run_z3 smtlib_exp in
  let () = Printf.printf "Z3 responded with \n %s \n%!" res in
  z3_returned_sat res

let bexpr = Alcotest.testable (Fmt.of_to_string BExpr.to_smtlib) (BExpr.(=))
let smt_equiv = Alcotest.testable (Fmt.of_to_string BExpr.to_smtlib) (log_eq) 
