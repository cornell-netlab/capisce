open Pbench
open Base_quickcheck   
open Equivalences   

   
let cnf_foils () =
  let open BExpr in
  let one = Expr.bvi 1 1 in
  let istrue x = eq_ one (Expr.var x) in
  let prop v = Var.make v 1 |> istrue in
  let a = prop "a" in
  let b = prop "b" in
  let c = prop "c" in
  let d = prop "d" in
  let phi = BExpr.(or_ (and_ a b) (and_ c d)) in
  Alcotest.(check smt_equiv) "logically equivalent" phi (cnf phi)

let cnf_equiv () =
  Test.run_exn
    (module struct
       type t = BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         BExpr.qf_quickcheck_generator
    end)
    ~config:{z3_config with test_count = 1000}
    ~f:(fun b ->
      [%test_pred: BExpr.t] (log_eq b) (BExpr.cnf b))

  
let tests =
  [
    Alcotest.test_case "cnf foils" `Quick cnf_foils;
    Alcotest.test_case "qc cnf_equiv" `Slow cnf_equiv;
  ]

  
                   
