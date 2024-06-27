open Core
open Equivalences
open Pbench
open ASTs

let fabric_gpl =
  P4Parse.tbl_abstraction_from_file
    ["./examples/includes"]
    "./examples/bf4_failing/fabric_no_consts.p4"
    1000
    1
    false
    false
  |> Tuple2.map ~f:(Translate.gcl_to_gpl)

let (prsr, pipe) = fabric_gpl

module CP = Transform.ConstProp (
  struct
    include GPL
    module P = Primitives.Pipeline
    let prim_const_prop = P.const_prop
  end)
module DCE = Transform.DeadCodeElim(
    struct
      include GPL
      module P = Primitives.Pipeline
      let prim_dead_code_elim = P.dead_code_elim
    end
  )

let const_prop_noop () =
  let prog =
    GPL.(sequence [
      assign (Var.make "x" 8) (Expr.bvi 1 8);
      choices [
        assign (Var.make "y" 8) (Expr.bvi 1 8);
        assign (Var.make "z" 8) (Expr.bvi 1 8);
      ]
    ])
  in
  CP.propagate_exn prog
  |> Alcotest.(check @@ gpl)
    "finishes with different non_erroneous program"
    prog

let const_prop_wikipedia_example () =
  let open GPL in
  let x = Var.make "x" 8 in
  let y = Var.make "y" 8 in
  let prog =
    sequence [
      assign x (Expr.bvi 14 8);
      assign y Expr.(bsub (bvi 7 8) (Expr.lshr_ (var x) (bvi 1 8)));
      assert_ Expr.(BExpr.eq_ (bmul (var y) (bsub (bvi 28 8) (badd (var x) (bvi 2 8)))) (bvi 0 8))
    ]
  in
  let exp =
    sequence [
      assign x @@ Expr.bvi 14 8;
      assign y @@ Expr.bvi 0 8;
      assert_ BExpr.true_
    ]
  in
  CP.propagate_exn prog
  |> Alcotest.(check @@ gpl) "equivalent" exp


let const_prop_lossy_join () =
  let x = Var.make "x" 8 in
  let y = Var.make "y" 8 in
  let prg =
    GPL.(sequence [
      assign x (Expr.bvi 1 8);
      choices [
        assign y @@ Expr.var x;
        assign y @@ Expr.bvi 2 8;
      ];
      assert_ Expr.(BExpr.eq_ (var y) (bvi 0 8));
    ])
  in
  let exp =
    GPL.(sequence [
      assign x @@ Expr.bvi 1 8;
      choices [
        assign y @@ Expr.bvi 1 8;
        assign y @@ Expr.bvi 2 8;
      ];
      assert_ Expr.(BExpr.eq_ (var y) (bvi 0 8));
    ])
  in
  CP.propagate_exn prg
  |> Alcotest.(check gpl)
    "finishes with different non_erroneous program"
    exp



let propagate_pipeline_assignment () =
  let open Primitives in
  let x = Var.make "x" 8 in
  let y = Var.make "x" 8 in
  let p = Pipeline.assign y @@ Expr.(bsub (bvi 7 8) (Expr.lshr_ (var x) (bvi 1 8))) in
  let (produced,_) = Pipeline.const_prop (Var.Map.singleton x Expr.(bvi 14 8)) p in
  let  expected = Pipeline.assign y @@ Expr.bvi 0 8 in
  Alcotest.(check @@ gpl) "equivalent"
    (GPL.prim expected)
    (GPL.prim produced)

let const_prop_fabric_terminates () =
  let prog = GPL.sequence [prsr; pipe] in
  CP.propagate_exn prog
  |> Alcotest.(check @@ neg @@ gpl)
    "finishes with different non_erroneous program"
    prog


let dce_fabric_terminates_after_cp ()=
  let prog = GPL.sequence [prsr; pipe] in
  CP.propagate_exn prog
  |> DCE.elim
  (* |> Alcotest.(check @@ neg gpl) *)
  (*   "finishes with different non_erroneous program" *)
  (*   prog *)
  |> Alcotest.(check gpl)
       "[EXFAIL] finishes with empty program"
       GPL.skip

let optimizing_fabric_terminates () =
  let (prsr, pipe) = fabric_gpl in
  let prog =  GPL.sequence [prsr; pipe] in
  GPL.optimize prog
  |> Alcotest.(check @@ gpl)
    "finishes with different non-erroneous program"
    prog


let tests = [
  Alcotest.test_case "checking that const_prop with no variable reads is the identity"
    `Quick const_prop_noop;
  Alcotest.test_case "propagate Pipeline assignment"
    `Quick propagate_pipeline_assignment;
  Alcotest.test_case "propagate lossy join"
    `Quick const_prop_lossy_join;
  Alcotest.test_case "checking sequential constant propagation"
    `Quick const_prop_wikipedia_example;
  Alcotest.test_case
    "checking that const_prop for fabric terminates"
    `Quick const_prop_fabric_terminates;
  Alcotest.test_case
    "checking that dead_code_elim for fabric terminates after constant_propagation"
    `Quick dce_fabric_terminates_after_cp;
  Alcotest.test_case
    "checking that optimizing fabric terminates"
    `Quick optimizing_fabric_terminates;
]
