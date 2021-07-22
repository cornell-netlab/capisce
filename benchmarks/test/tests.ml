open Base_quickcheck    
let test_suites : unit Alcotest.test list = [
    "Smart Constructors Are Correct",
    [
      Alcotest.test_case "Quickcheck Identity" `Quick (fun () ->          
          Test.run_exn
            (module Pbench.Test)
            ~f:(fun b -> [%test_eq: Pbench.Test.t] b Pbench.Test.true_)
        )
    ]
  ]

let () = Alcotest.run "Inference" test_suites
