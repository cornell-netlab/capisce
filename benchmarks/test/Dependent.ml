open Pbench
open DependentTypeChecker

let passing_table_example () =
  let open Primitives in
  let open HoareNet in
  let ghost_vlan = Var.make "_symb$vlan$ghost" 9 in
  let vlan = Var.make "hdr.vlan.id" 8 in
  let egress = Var.make "egress" 9 in
  let key = Var.make "_symb$vlan$match_0" 8 in
  sequence [
    table
      ~pre:(BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ~post:(BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ("vlan", [key], [
          ([], [Action.Assign (egress, Expr.bvi 511 9)]);
          ([], [Action.Assign (egress, Expr.bvi 11  9)])
        ])
  ]
  |> check
  |> Alcotest.(check bool) "is true" true

let failing_table_example () =
  let open Primitives in
  let open HoareNet in
  let ghost_vlan = Var.make "_symb$vlan$ghost" 9 in
  let vlan = Var.make "hdr.vlan.id" 8 in
  let egress = Var.make "egress" 9 in
  let key = Var.make "_symb$vlan$match_0" 8 in
  sequence [
    table
      ~pre:(BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ~post:(BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ("vlan", [key], [
          ([], [Action.Assign (egress, Expr.bvi 511 9)]);
          ([], [Action.Assign (vlan, Expr.bvi 11 9)])
        ])
  ]
  |> check
  |> Alcotest.(check bool) "fails" false


let tests =
  [
    Alcotest.test_case "Modular Safe Example from Pi4 paper" `Quick passing_table_example;
    Alcotest.test_case "Modular Unsafe Example from Pi4 paper" `Quick failing_table_example

  ]
