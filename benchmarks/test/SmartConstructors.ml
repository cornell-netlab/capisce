open Pbench
open Base_quickcheck    
let identity () =
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b b)



let tests =
  [
    Alcotest.test_case "Quickcheck Identity" `Quick identity
  ]

  
                   
