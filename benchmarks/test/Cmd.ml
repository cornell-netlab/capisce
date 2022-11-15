open Core
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
  |> Tuple2.uncurry (GPL.seq)


let tables_fwd () =
  let init = 0 in
  let prim p =
    if Primitives.Pipeline.is_table p then
      (+) 1
    else
      (+) 0
  in
  let choices = List.sum (module Int) ~f:Fn.id in
  let fwd_count =
    GPL.forward fabric_gpl
      ~init
      ~prim:(Fn.flip prim)
      ~choices
  in
  Alcotest.(check int) "equivalent" 15 fwd_count

let tables_bwd () =
  let init = 0 in
  let prim p =
    if Primitives.Pipeline.is_table p then
      (+) 1
    else
      (+) 0
  in
  let choices = List.sum (module Int) ~f:Fn.id in
  let bwd_count =
    GPL.backward fabric_gpl
      ~init
      ~choices
      ~prim
  in
  Alcotest.(check int) "equivalent" 15 bwd_count

let tables_bot () =
  let prim p =
    if Primitives.Pipeline.is_table p then
      1
    else
      0
  in
  let choices = List.sum (module Int) ~f:Fn.id in
  let bottom_up_count =
    GPL.bottom_up fabric_gpl
      ~prim
      ~choices
      ~sequence:choices
  in
  Alcotest.(check int) "equivalent" 15 bottom_up_count

let tables_top () =
  let init = 0 in
  let prim p =
    if Primitives.Pipeline.is_table p then
      1
    else
      0
  in
  let top_down_count =
    GPL.top_down fabric_gpl
      ~init
      ~prim:(fun acc p -> acc + prim p)
      ~choices:(fun acc cs f ->
          List.map cs ~f:(f 0)
          |> List.sum (module Int) ~f:Fn.id
          |> (+) acc
      )
      ~sequence:(fun acc cs f ->
          List.fold cs ~init:acc ~f:(fun acc c ->
              f acc c
            )
        )
  in
  Alcotest.(check int) "equivalent" 15 top_down_count




let tests =
  [
    Alcotest.test_case "checking fabric has 15 tables (fwd)" `Quick tables_fwd;
    Alcotest.test_case "checking fabric has 15 tables (bwd)" `Quick tables_bwd;
    Alcotest.test_case "checking fabric has 15 tables (bot)" `Quick tables_bot;
    Alcotest.test_case "checking fabric has 15 tables (top)" `Quick tables_top;
  ]
