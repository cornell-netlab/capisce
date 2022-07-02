open Pbench
open Equivalences   

   
let get_vars () =
  let open BExpr in
  let cvar = Var.make "_symb$t2$action$_$0" 1 in
  let dvar = Var.make "hdr.ipv4_2.is_valid$_$1" 1 in
  let one = Expr.bvi 1 1 in
  let exp = ([dvar], [cvar]) in
  let test = Alcotest.(check (pair (list var) (list var))) "vars equivalent" exp in
  vars Expr.(or_ (eq_ (var dvar) one) (eq_ (var cvar) one))
  |> test
  
  
let tests =
  [
    Alcotest.test_case "correctly_get_variables" `Quick get_vars;
  ]

  
                   
