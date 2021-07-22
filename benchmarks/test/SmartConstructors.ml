open Base_quickcheck    
let identity () =
  Test.run_exn
    (module Pbench.Test)
    ~f:(fun b -> [%test_eq: Pbench.Test.t] b b)



let tests =
  [
    Alcotest.test_case "Quickcheck Identity" `Quick identity
  ]

  
                   
