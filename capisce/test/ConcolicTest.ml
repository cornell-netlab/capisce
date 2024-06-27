(* open Core *)
open Capiscelib



let evaluation_not_eq () =
  let model =
    Model.of_alist_exn
      [ Var.make "hdr.ethernet.etherType" 16,
        (Bigint.of_int 63487, 16)
      ]
  in
  let bexpr =
    let open BExpr in
    let open Expr in
    not_ (eq_
       (var (Var.make "hdr.ethernet.etherType" 16))
       (bvi 2048 16))
  in
  BExpr.eval model bexpr
  |> Alcotest.(check bool) "boolean evaluates correctly" true

let evaluation_eq () =
  let model =
    Model.of_alist_exn
      [ Var.make "hdr.ethernet.etherType" 16,
        (Bigint.of_int 63487, 16)
      ]
  in
  let bexpr =
    let open BExpr in
    let open Expr in
    (eq_
       (var (Var.make "hdr.ethernet.etherType" 16))
       (bvi 2048 16))
  in
  BExpr.eval model bexpr
  |> Alcotest.(check bool) "boolean evaluates correctly" false


let tests : unit Alcotest.test_case list = [
  Alcotest.test_case "true = not_ @@ eq_" `Quick evaluation_not_eq;
  Alcotest.test_case "false = eq_" `Quick evaluation_eq;
]
