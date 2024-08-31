open Capisce
open ASTs.GPL
open Equivalences


let df_infer () =
  let port = Var.make "port" 9 in 
  let dst = Var.make "dst" 32 in 
  let simpletable =
    table "t" [
      `Exact dst
    ] [ 
      (* no op *)
      [], [];
      let p = Var.make "p" 9 in 
      [p], Primitives.Action.[
        assign port @@ Expr.var p
      ]
    ]
  in
  let annotated =
    track_assigns port simpletable
    |> encode_tables
  in
  Qe.cegqe annotated
  |> Alcotest.(check (neg smt_equiv)) "satisfiable" BExpr.false_

   

let tests =
  [
    Alcotest.test_case "determined fwding infer" `Quick df_infer;
  ]
