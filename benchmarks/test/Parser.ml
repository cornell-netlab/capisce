(* open Core *)
open Pbench
open Base_quickcheck
open Equivalences

let quant b = BExpr.forall (fst (BExpr.vars b)) b   
let roundtrip b = b |> BExpr.to_smtlib |> Solver.of_smtlib []
let check_roundtrip b = Alcotest.(check smt_equiv) "parser roundtrips" (quant b) (roundtrip (quant b))
  
   
let smtlib_roundtrip () =
  Test.run_exn (module BExpr)
    ~config:{z3_config with test_count = 1000}
    ~f:check_roundtrip
      

let roundtrip_sle () =
  BExpr.sle_ (Expr.var (Var.make "il" 32)) (Expr.bvi 8 32)
  |> check_roundtrip

let roundtrip_gen_1 () =
  let open BExpr in
  let open Expr in
  let ss_var = Var.make "ss" 32 in
  let sm_var = Var.make "sm" 32 in
  let oj_var = Var.make "oj" 32 in
  let hw_var = Var.make "hw" 32 in
  let pz_var = Var.make "pz" 32 in
  let hv_var = Var.make "hv" 32 in
  let jm_var = Var.make "jm" 32 in
  let bx_var = Var.make "bx" 32 in
  let ss = var ss_var in
  let sm = var sm_var in
  let oj = var oj_var in
  let hw = var hw_var in
  let pz = var pz_var in
  let hv = var hv_var in
  let jm = var jm_var in
  let bx = var bx_var in
  (fun () ->
    or_
     (forall [ss_var]
        (forall [sm_var]
           (forall [oj_var]
              (forall [hw_var]
                 (ugt_ ss (badd (bnot (bnot (badd (bvi 12870125 32) (shl_ hw sm))))
                             (shl_ (bsub (bsub (bvi 205956 32) (bnot oj)) pz) (bvi 440674625 32))))))))
        (iff_
          (exists [hv_var]
            (exists [jm_var]
              (and_
                (imp_
                  false_
                  (exists [bx_var]
                    (ugt_ hv (bnot (bnot (bxor (bvi 498808408 32) (badd jm bx)))))))
                (not_
                  true_))))
          (not_
             true_)))
  |> dumb 
  |> check_roundtrip


let roundtrip_gen_2 () =
  let open BExpr in
  let open Expr in
  let tt_var = Var.make "tt" 32 in
  let tt = var tt_var in
  (fun () ->
    forall [tt_var]
      (and_
         (ule_ (bvi 10055514 32) tt)
         (sge_ (bvi 25 32) (bnot (bvi 13 32)))))
  |> dumb 
  |> check_roundtrip

let roundtrip_gen_3 () =
  let open BExpr in
  let open Expr in
  let bw_var = Var.make "bw" 32 in
  let ga_var = Var.make "ga" 32 in
  let dq_var = Var.make "dq" 32 in
  let bw = var bw_var in
  let ga = var ga_var in
  let dq = var dq_var in
  (fun () ->
    forall [bw_var]
        (forall [ga_var]
          (forall [dq_var]
            (not_
               (ugt_ bw (bxor dq (ashr_ (bvi 4340 32) ga)))))))
  |> dumb
  |> check_roundtrip 
  
let tests =
  [ Alcotest.test_case "QC smt parser roundtrips" `Slow smtlib_roundtrip;
    Alcotest.test_case "(sle il 8)" `Quick roundtrip_sle;
    Alcotest.test_case "debugging generated example_1" `Quick roundtrip_gen_1;
    Alcotest.test_case "debugging generated example_2" `Quick roundtrip_gen_2;
    Alcotest.test_case "debugging generated example_3" `Quick roundtrip_gen_3;    
    
  ]
