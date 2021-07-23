let test_suites : unit Alcotest.test list = [
    "Smart Constructors Are Correct", SmartConstructors.tests
  ]
          
(* let%test_unit "identity" = SmartConstructors.identity ()  *)
  

let () =
  Alcotest.run "Inference" test_suites
