
let () = Capisce.Log.override ()

let test_suites : unit Alcotest.test list = [
  (* "Optimizer", Optimizer.tests; *)
  (* "Survey", SurveyTests.tests; *)
  "Smtlib Parser", Parser.tests;
  "Smarts", SmartConstructors.tests;
  "ProgramSmarts", ProgramSmarts.tests;
  "Logic Algorithms", Algorithms.tests;
  "Traversals", Traversals.tests;
  "Util", UtilTest.tests;
  "Concolic Helpers", ConcolicTest.tests;
]

let () =
  Capisce.Log.parse_flags "dzo";
  Capisce.Log.override ();
  Capisce.BExpr.enable_smart_constructors := `On;
  Alcotest.run "Inference" test_suites
