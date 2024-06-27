
let () = Capiscelib.Log.override ()

let test_suites : unit Alcotest.test list = [
  (* "Optimizer", Optimizer.tests; *)
  "Survey", SurveyTests.tests;
  "Smtlib Parser", Parser.tests;
  "Smarts", SmartConstructors.tests;
  "ProgramSmarts", ProgramSmarts.tests;
  "Logic Algorithms", Algorithms.tests;
  "Traversals", Traversals.tests;
  "Dependent Type System", Dependent.tests;
  "Util", UtilTest.tests;
  "Concolic Helpers", ConcolicTest.tests;
]

let () =
  Capiscelib.Log.parse_flags "dzo";
  Capiscelib.Log.override ();
  Capiscelib.BExpr.enable_smart_constructors := `On;
  Alcotest.run "Inference" test_suites
