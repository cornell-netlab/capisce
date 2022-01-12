let test_suites : unit Alcotest.test list = [
    "Smarts", SmartConstructors.tests;
    "Logic Algorithms", Algorithms.tests; 
  ]
          
(* let%test_unit "identity" = SmartConstructors.identity () *)

let () =
  Pbench.Log.debug := true;
  Alcotest.run "Inference" test_suites
