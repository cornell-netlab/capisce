open Capiscelib
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

let sanf_test () =
  let open ASTs in
  let open GCL in
  let open BExpr in
  let open Expr in
  let ipv4_protocol = Var.make "hdr.ipv4.protocol" 8 in
  let udp_isValid = Var.make "hdr.udp.isValid" 1 in
  let udp_dstPort = Var.make "hdr.udp.dstPort" 16 in
  let lr_msg_type_isValid = Var.make "hdr.lr_msg_type.isValid" 1 in
  let pos_report_isValid = Var.make "hdr.pos_report.isValid" 1 in
  let program =
    sequence [
      assume @@ eq_ (bvi 17 8) @@ var ipv4_protocol;
      assign udp_isValid @@ bvi 1 1;
      assert_ @@ eq_ (bvi 1 1) @@ var udp_isValid;
      assume @@ eq_ (bvi 4660 16) @@ var udp_dstPort;
      assign lr_msg_type_isValid @@ bvi 1 1;
      assert_ @@ eq_ (bvi 1 1) @@ var lr_msg_type_isValid;
      assign pos_report_isValid @@ bvi 1 1;
    ]
  in
  single_assert_nf program
  |> Alcotest.(check @@ list Equivalences.gcl) "lists equivalent"
    [ sequence [
          assume @@ eq_ (bvi 17 8) @@ var ipv4_protocol;
          assign udp_isValid @@ bvi 1 1;
          assert_ @@ eq_ (bvi 1 1) @@ var udp_isValid];
      sequence [
        assume @@ eq_ (bvi 17 8) @@ var ipv4_protocol;
        assign udp_isValid @@ bvi 1 1;
        assume @@ eq_ (bvi 1 1) @@ var udp_isValid;
        assume @@ eq_ (bvi 4660 16) @@ var udp_dstPort;
        assign lr_msg_type_isValid @@ bvi 1 1;
        assert_ @@ eq_ (bvi 1 1) @@ var lr_msg_type_isValid;
      ];
      sequence [
        assume @@ eq_ (bvi 17 8) @@ var ipv4_protocol;
        assign udp_isValid @@ bvi 1 1;
        assume @@ eq_ (bvi 1 1) @@ var udp_isValid;
        assume @@ eq_ (bvi 4660 16) @@ var udp_dstPort;
        assign lr_msg_type_isValid @@ bvi 1 1;
        assume @@ eq_ (bvi 1 1) @@ var lr_msg_type_isValid;
        assign pos_report_isValid @@ bvi 1 1;
      ]
    ]


let tests =
  [
    Alcotest.test_case "correctly_get_variables" `Quick get_vars;
    Alcotest.test_case "single_assign_normal_form" `Quick sanf_test;
  ]
