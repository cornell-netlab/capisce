
let test_suites : unit Alcotest.test list = [
  "Optimizer", Optimizer.tests;
  "Iterators", Cmd.tests;
  "Smtlib Parser", Parser.tests;
  "Smarts", SmartConstructors.tests; (*  *)
  "Logic Algorithms", Algorithms.tests;
  "Traversals", Traversals.tests;
  "Dependent Type System", Dependent.tests;
]
          
(* let%test_unit "identity" = SmartConstructors.identity () *)

let () =
  Pbench.Log.override ();
  Pbench.Log.parse_flags "d";
  Pbench.BExpr.enable_smart_constructors := `On;
  Alcotest.run "Inference" test_suites
