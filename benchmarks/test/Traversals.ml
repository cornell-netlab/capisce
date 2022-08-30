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
  

let count_paths () =
  let open Cmd in
  let one = Expr.bvi 1 1 in
  let var x = Var.make x 1 in
  let c = Cmd.(sequence [
      assign (var "a") one;
      choice (assign (var "b") one) (assign (var "c") one);
      assign (var "e") one;
      assign (var "f") one;
      assign (var "g") one;
      assign (var "h") one;
      assign (var "i") one;
      choice (assign (var "j") one) (assign (var "k") one);
      assign (var "l") one
    ]) in
  Alcotest.(check bigint) "num paths is 4" (count_paths c) (Bigint.of_int 4)


let tests =
  [
    Alcotest.test_case "correctly_get_variables" `Quick get_vars;
    Alcotest.test_case "a;(b[]c);e;f;g;h;i;(j [] k);l" `Quick count_paths;
  ]

  
                   
