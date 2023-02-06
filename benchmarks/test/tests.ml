
let () = Pbench.Log.override ()

let test_suites : unit Alcotest.test list = [
  "Monitor", MonitorTest.tests;
  "Optimizer", Optimizer.tests;
  "Iterators", Cmd.tests;
  "Smtlib Parser", Parser.tests;
  "Smarts", SmartConstructors.tests; (*  *)
  "Logic Algorithms", Algorithms.tests;
  "Traversals", Traversals.tests;
  "Dependent Type System", Dependent.tests;
  "Util", UtilTest.tests;
]
          
(* let%test_unit "identity" = SmartConstructors.identity () *)

let () =
  Pbench.Log.parse_flags "dzo";
  Pbench.BExpr.enable_smart_constructors := `On;
  Alcotest.run "Inference" test_suites
