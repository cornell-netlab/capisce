let test_suites : unit Alcotest.test list = [
    "Smart Constructors Are Correct", SmartConstructors.tests
  ]

let () = Alcotest.run "Inference" test_suites
