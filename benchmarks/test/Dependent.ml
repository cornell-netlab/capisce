open Core
open Pbench
open Equivalences
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
      ~pre:(Some BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ~post:(Some BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ("vlan", [key], [
          ([], [Action.assign_ (egress, Expr.bvi 511 9)]);
          ([], [Action.assign_ (egress, Expr.bvi 11  9)])
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
      ~pre:(Some BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ~post:(Some BExpr.(eq_ (Expr.var vlan) (Expr.var ghost_vlan)))
      ("vlan", [key], [
          ([], [Action.assign_ (egress, Expr.bvi 511 9)]);
          ([], [Action.assign_ (vlan, Expr.bvi 11 9)])
        ])
  ]
  |> check
  |> Alcotest.(check bool) "fails" false

let safe_p4_validity_inference () =
  let open Primitives in
  let vlan = Var.make "hdr.vlan.id" 9 in
  let egress = Var.make "egress" 9 in
  let validity = Var.make "h.valid" 1 in
  let read = Var.make "h.x" 8 in
  let dont_care = Var.make "_symb$t$match_1$DONTCARE" 1 in
  let symbolic_validity = Var.make "_symb$t$match_0" 1 in
  let symbolic_read     = Var.make "_symb$t$match_1" 8 in
  let t =
    let open ASTs.GPL in
    sequence [
      assume (BExpr.eq_ (Expr.var symbolic_validity) (Expr.var validity));
      choice_seqs [
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 1 1))];
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 0 1));
         assert_ (BExpr.eq_ (Expr.var validity) (Expr.bvi 1 1));
         assume (BExpr.eq_ (Expr.var symbolic_read) (Expr.var read));
        ]
      ];
      table "t"
        [symbolic_validity; symbolic_read]
        [
          ([], [Action.assign_ (egress, Expr.bvi 511 9)]);
          ([], [Action.assign_ (vlan, Expr.bvi 11 9)])
        ]
    ]
  in
  let prog =
    HoareNet.prim ( { precondition = Some BExpr.true_;
            cmd = t;
            postcondition = Some BExpr.true_;
           } )

  in
  HoareNet.infer prog None None
  |> Alcotest.(check smt_equiv) "produces equivalent CPF"
    BExpr.(
      (or_
         (eq_ (Expr.var (Var.make "_symb$t$match_1$DONTCARE$_$0" 1)) (Expr.bvi 1 1))
         (eq_ (Expr.var (Var.make "_symb$t$match_0$_$0" 1)) (Expr.bvi 1 1)))
    )

let bf4_heuristic_inference () =
  let open Primitives in
  let vlan = Var.make "hdr.vlan.id" 9 in
  let egress = Var.make "egress" 9 in
  let validity = Var.make "h.valid" 1 in
  let read = Var.make "h.x" 8 in
  let dont_care = Var.make "_symb$t2$match_0$DONTCARE" 1 in
  let symbolic_read     = Var.make "_symb$t2$match_0" 8 in
  let tables =
    let open ASTs.GPL in
    sequence [
      table "t1" [Var.make "_symb$t1$match_0" 8]
        [ ([], [Action.assign validity @@ Expr.bvi 1 1]);
          ([], [Action.assign validity @@ Expr.bvi 0 1])
       ];
      choice_seqs [
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 1 1))];
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 0 1));
         assert_ (BExpr.eq_ (Expr.var validity) (Expr.bvi 1 1));
         assume (BExpr.eq_ (Expr.var symbolic_read) (Expr.var read));
        ]
      ];
      table "t2"
        [symbolic_read]
        [ ([], [Action.assign_ (egress, Expr.bvi 511 9)]);
          ([], [Action.assign_ (vlan, Expr.bvi 11 9)])
        ]
    ]
  in
  let prog =
    HoareNet.prim ( { precondition = Some BExpr.true_;
            cmd = tables;
            postcondition = Some BExpr.true_;
           } )

  in
  HoareNet.infer prog None None
  |> Alcotest.(check smt_equiv) "produces equivalent CPF"
    BExpr.(
      (or_
         (eq_ (Expr.var (Var.make "_symb$t2$match_0$DONTCARE$_$0" 1)) (Expr.bvi 1 1))
         (ugt_ (Expr.bvi 1 2) (Expr.var (Var.make "_symb$t1$action$_$0" 2)) ))
    )


let modular_heuristic_inference () =
  let open Primitives in
  let vlan = Var.make "hdr.vlan.id" 9 in
  let egress = Var.make "egress" 9 in
  let validity = Var.make "h.valid" 1 in
  let read = Var.make "h.x" 8 in
  let dont_care = Var.make "_symb$t2$match_0$DONTCARE" 1 in
  let symbolic_read     = Var.make "_symb$t2$match_1" 8 in
  let t1 =
    let open ASTs.GPL in
      table "t1" [Var.make "_symb$t1$match_0" 8]
        [ ([], [Action.assign validity @@ Expr.bvi 1 1]);
          ([], [Action.assign validity @@ Expr.bvi 0 1])
       ]
  in
  let t2 =
    let open ASTs.GPL in
    sequence [
      choice_seqs [
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 1 1))];
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 0 1));
         assert_ (BExpr.eq_ (Expr.var validity) (Expr.bvi 1 1));
         assume (BExpr.eq_ (Expr.var symbolic_read) (Expr.var read));
        ]
      ];
      table "t2"
        [symbolic_read]
        [ ([], [Action.assign_ (egress, Expr.bvi 511 9)]);
          ([], [Action.assign_ (vlan, Expr.bvi 11 9)])
        ]
    ]
  in
  let prog =
    HoareNet.sequence [
      HoareNet.prim ( {
          precondition = Some BExpr.true_;
          cmd = t1;
          postcondition = Some BExpr.true_;
        } );
      HoareNet.prim ( {
          precondition = Some BExpr.true_;
          cmd = t2;
          postcondition = Some BExpr.true_
        } )
    ]
  in
  HoareNet.infer prog None None
  |> Alcotest.(check smt_equiv) "produces equivalent CPF"
    BExpr.(
      (eq_ (Expr.var (Var.make "_symb$t2$match_0$DONTCARE$_$0" 1)) (Expr.bvi 1 1))
    )

let annotated_inference () =
  let open Primitives in
  let vlan = Var.make "hdr.vlan.id" 9 in
  let egress = Var.make "egress" 9 in
  let validity = Var.make "h.valid" 1 in
  let read = Var.make "h.x" 8 in
  let dont_care = Var.make "_symb$t2$match_0$DONTCARE" 1 in
  let symbolic_read     = Var.make "_symb$t2$match_1" 8 in
  let t1 =
    let open ASTs.GPL in
      table "t1" [Var.make "_symb$t1$match_0" 8]
        [ ([], [Action.assign validity @@ Expr.bvi 1 1]);
          ([], [Action.assign validity @@ Expr.bvi 0 1])
       ]
  in
  let t2 =
    let open ASTs.GPL in
    sequence [
      choice_seqs [
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 1 1))];
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 0 1));
         assert_ (BExpr.eq_ (Expr.var validity) (Expr.bvi 1 1));
         assume (BExpr.eq_ (Expr.var symbolic_read) (Expr.var read));
        ]
      ];
      table "t2"
        [symbolic_read]
        [ ([], [Action.assign_ (egress, Expr.bvi 511 9)]);
          ([], [Action.assign_ (vlan, Expr.bvi 11 9)])
        ]
    ]
  in
  let prog =
    let phi =
      BExpr.(imp_
               (eq_ (Expr.var (Var.make "_symb$t1$action" 2)) (Expr.bvi 0 2))
               (eq_ (Expr.var validity) (Expr.bvi 1 1))
            )
    in
    HoareNet.sequence [
      HoareNet.prim ( {
          precondition = Some BExpr.true_;
          cmd = t1;
          postcondition = Some phi;
        } );
      HoareNet.prim ( {
          precondition = Some phi;
          cmd = t2;
          postcondition = Some BExpr.true_
        } )
    ]
  in
  HoareNet.infer prog None None
  |> Alcotest.(check smt_equiv) "produces equivalent CPF"
    BExpr.(
      (or_
         (eq_ (Expr.var (Var.make "_symb$t2$match_0$DONTCARE$_$0" 1)) (Expr.bvi 1 1))
         (ugt_ (Expr.bvi 1 2) (Expr.var (Var.make "_symb$t1$action$_$0" 2)) ))
    )

let infer_annotations () =
  let open Primitives in
  let vlan = Var.make "hdr.vlan.id" 8 in
  let egress = Var.make "egress" 9 in
  let validity = Var.make "h.valid" 1 in
  let read = Var.make "h.x" 8 in
  let dont_care = Var.make "_symb$t2$match_0$DONTCARE" 1 in
  let symbolic_read     = Var.make "_symb$t2$match_1" 8 in
  let t2 =
    let open ASTs.GPL in
    sequence [
      choice_seqs [
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 1 1))];
        [assume (BExpr.eq_ (Expr.var dont_care) (Expr.bvi 0 1));
         assert_ (BExpr.eq_ (Expr.var validity) (Expr.bvi 1 1));
         assume (BExpr.eq_ (Expr.var symbolic_read) (Expr.var read));
        ]
      ];
      table "t2"
        [symbolic_read]
        [ ([], [Action.assign_ (egress, Expr.bvi 511 9)]);
          ([], [Action.assign_ (vlan, Expr.bvi 11 8)])
        ]
    ]
  in
  let prog =
    let phi =
      BExpr.(
        imps_ [
          (eq_ (Expr.var @@ Var.make "_symb$t1$match_0" 8) (Expr.var vlan) );
          ands_ [
            imps_ [(eq_
                      (Expr.var @@ Var.make "_symb$t1$action" 2)
                      (Expr.bvi 0 2));
                    (eq_
                       (Expr.var @@ Var.make "h.valid" 1)
                       (Expr.bvi 1 1))
                  ];
            imps_ [(ugt_
                      (Expr.var @@ Var.make "_symb$t1$action" 2)
                      (Expr.bvi 0 2));
                    (eq_
                       (Expr.var @@ Var.make "h.valid" 1)
                       (Expr.bvi 0 1))]]]) in
    let qf_phi =
      phi
      |> BExpr.forall [Var.make "_symb$t1$match_0" 8; vlan]
      |> BottomUpQe.optimistic_qe (Qe.solve_wto `Z3)
      |> Option.value_exn ~message:"QE FAILED"
    in
    HoareNet.prim ( {
        precondition = Some qf_phi;
        cmd = t2;
        postcondition = Some BExpr.true_
      } )
  in
  HoareNet.infer prog None None
  |> Alcotest.(check smt_equiv) "produces equivalent CPF"
    BExpr.(
      (or_
         (eq_ (Expr.var (Var.make "_symb$t2$match_0$DONTCARE$_$0" 1)) (Expr.bvi 1 1))
         (ugt_ (Expr.bvi 1 2) (Expr.var (Var.make "_symb$t1$action$_$0" 2)) ))
    )

let check_out_of_scope () =
  let x = Var.make "x" 8 in
  let y = Var.make "y" 8 in
  let pre =
    HoareNet.assign x @@ Expr.bvi 4 8
  in
  let post =
    HoareNet.assert_ BExpr.(not_ (eq_ (Expr.var y) @@ Expr.bvi 5 8))
  in
  let cond =
    HoareNet.prim ( {
        precondition = Some BExpr.(uge_ (Expr.var x) (Expr.bvi 0 8));
        cmd = ASTs.GPL.skip;
        postcondition = Some BExpr.(eq_ (Expr.var y) (Expr.bvi 5 8));
      } )
  in
  let prog =
    HoareNet.sequence [
      pre;
      cond;
      post;
    ]
  in
  HoareNet.check_annotations prog
  |> Alcotest.(check bool) "annotation check passes" true

let tests =
  [
    Alcotest.test_case "Modular Safe Example from Pi4 paper" `Quick passing_table_example;
    Alcotest.test_case "Modular Unsafe Example from Pi4 paper" `Quick failing_table_example;
    Alcotest.test_case "Table from SafeP4" `Quick safe_p4_validity_inference;
    Alcotest.test_case "Bf4 multitable heuristic" `Quick bf4_heuristic_inference;
    Alcotest.test_case "Single-table-only produces too-strong conditions" `Quick modular_heuristic_inference;
    Alcotest.test_case "annotations recover weaker conditions" `Quick annotated_inference;
    Alcotest.test_case "infer annotations of preceeding WP" `Quick infer_annotations;
    Alcotest.test_case "check between annotations" `Quick check_out_of_scope;
  ]
