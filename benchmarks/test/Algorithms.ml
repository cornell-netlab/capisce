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
  Pbench.BExpr.enable_smart_constructors := `Off;
  let phi = BExpr.(or_ (and_ a b) (and_ c d)) in
  let exp = BExpr.(and_ (and_ (and_ (or_ c a) (or_ c b)) (or_ a d)) (or_ b d)) in
  let cphi = cnf phi in 
  Pbench.BExpr.enable_smart_constructors := `On;
  Alcotest.(check smt_equiv) "logically equivalent" exp cphi

let cnf_equiv () =
  Test.run_exn
    (module struct
       type t = BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         BExpr.qf_quickcheck_generator
    end)
    ~config:{z3_config with test_count = 100}
    ~f:(fun b ->
      [%test_pred: BExpr.t] (log_eq b) (BExpr.cnf b))

let vc_egress_spec () =
  let open BExpr in
  let open Expr in
  let open Cmd in
  let out = Var.make "standard_metadata.egress_spec" 9 in
  let port = Var.make "_symb$fwd$ipv4_fwd$arg$port$_$0" 9 in
  let ethertype = Var.make "hdr.ethernet.etherType" 16 in
  let ipv4_is_next = Var.make "_state$parse_ipv4$next" 1 in
  let ipv4_is_valid = Var.make "hdr.ipv4.is_valid" 1 in
  let ethernet_match_0 = Var.make "_symb$ethernet$match_0" 9 in
  let fwd_match_0 = Var.make "_symb$fwd$match_0" 9 in
  let fwd_action = Var.make "_symb$fwd$action" 1 in
  let ethernet_action = Var.make " _symb$ethernet$action" 1 in
  let packet_type = Var.make "meta.ing_metadata.packet_type" 4 in
  let c =
    sequence [
        choice_seqs [
          [assume (eq_ (var ethertype) (bvi 2048 16));
           assign ipv4_is_next (bvi 1 1)];
          [assume (not_ (eq_ (var ethertype) (bvi 2048 16)))]];

        choice_seqs [
          [assume (eq_ (var ipv4_is_next) (bvi 1 1));
           assign ipv4_is_valid (bvi 1 1)];
          [assume (not_ (eq_ (var ipv4_is_next) (bvi 1 1))) ]];          
        assume (eq_ (var ethernet_match_0) (var ethertype));
        choice_seqs [
            [assume (eq_ (var ethernet_action) (bvi 1 1));
             assign packet_type (bvi 1 4)];
            [assume (eq_ (var ethernet_action) (bvi 0 1));
             assign packet_type (bvi 0 4)]];
        assume (eq_ (var fwd_match_0) (var packet_type));
        choice_seqs [
          [assume (eq_ (var fwd_action) (bvi 1 1));
           assert_ (eq_ (var ipv4_is_valid) (bvi 1 1));
           assert_ (eq_ (var ipv4_is_valid) (bvi 1 1));
           assign out (var port)];
          [assume (eq_ (var fwd_action) (bvi 0 1));
           assign out (bvi 511 9)]];
        assert_ (not_ (eq_ (var out) (bvi 0 9)))] in
  (* let dvs, _ = BExpr.vars (vc cmd) in *)
  Alcotest.(check cmd) "literal equivalence" skip c
                  
  
let tests =
  [
    Alcotest.test_case "cnf foils" `Quick cnf_foils;
    Alcotest.test_case "qc cnf_equiv" `Slow cnf_equiv;
    Alcotest.test_case "egress_spec vc" `Quick vc_egress_spec;   
  ]

  
                   
