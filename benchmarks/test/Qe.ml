let dur st nd = Time.(Span.(diff nd st |> to_ms))

let format_print num p4 program vc =
  let (data_plane_vars, control_plane_vars) = BExpr.vars vc in
  let quantified_vc = BExpr.forall data_plane_vars vc in
  let frees = Var.list_to_smtlib_decls control_plane_vars in
  let smtlib = Printf.sprintf "%s\n%!" (BExpr.to_smtlib quantified_vc) in
  Printf.printf "======================================\n\n%!";
  Printf.printf "               Example %d \n\n%!" num;
  Printf.printf "======================================\n%!";
  Printf.printf "%s\n%!" p4;
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "               GCL\n%!";
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "%s\n%!" (Cmd.to_string program);
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "                 VC\n%!";
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "%s\n%!" smtlib;
  let t0 = Time.now() in
  let simplified_smtlib = Printf.sprintf "%s\n%!" (BExpr.to_smtlib (BExpr.simplify quantified_vc)) in
  let t1 = Time.now() in
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "              Heuristics(%fms)\n%!" (dur t0 t1);
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "%s\n%!" simplified_smtlib;
  let result = Printf.sprintf "%s\n(assert %s)\n(check-sat)" frees smtlib |> Solver.run_z3 in
  let t2 = Time.now() in
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "            Result (%fms)\n%!" (dur t1 t2);
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "%s\n%!" result;
  let t3 = Time.now() in
  let cvc4_qe = Printf.sprintf "(set-logic UFBV)%s\n(simplify %s)\n%!" frees smtlib |> Solver.run_cvc4 in
  let t4 = Time.now() in
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "            CVC4 (%fms)\n%!" (dur t3 t4);
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "%s\n%!" cvc4_qe;
  let t5 = Time.now() in
  let p_qe = Printf.sprintf "%s\n(simplify %s)\n%!" frees smtlib |> Solver.run_princess in
  let t6 = Time.now() in
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "            Princess QE (%fms)\n%!" (dur t5 t6);
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "%s\n%!" p_qe;
  let t7 = Time.now() in
  let z3_qe = Printf.sprintf "(set-option :timeout 5000)%s\n(assert %s)\n(apply qe)" frees smtlib |> Solver.run_z3 in
  let t8 = Time.now() in
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "             Z3 QE (%fms)\n%!" (dur t7 t8);
  Printf.printf "--------------------------------------\n%!";
  Printf.printf "%s\n%!" z3_qe;
  Printf.printf "======================================\n%!";
  Printf.printf "\n\n\n\n\n"

(** The goal is to examine the ways in which control-plane state and data plane
   state mix together In what follows I'll demonstrate some
   as-simple-as-possible situations. Then I'll describe some more complicated
   examples that show some more surprising ways in which the contents combine.
 *)

(** WARMUP
 **
 **   First lets look at examples that show how the CP
 **   influences assert validity
 **
 ** *)

(**
   WARM UP 1 (Action Data Only)

   Lets first consider a one-tablen no keys one-action program on one bit
   The p4 program looks like the following

   table t {
     keys {}
     action = {λ ?x. x := ?x}
   }
   control {
     t.apply();
     assert (x = 1)
   }

   In this example the assert statement can be enforced via
   the single variable ?x and the necessity that the rule is
   inserted.

   REALISM? This is evocative of a table adding a header. See below.

   Computing the weakest precondition of this is simple. we get
        ∀ x. action(t) = 0 ∧ ?x = 1 ∨ ¬hit(t) ∧ x = 1

   The x should be eliminated the heuristics I've already implemented, yielding
        hit(t) ∧ ?x = 1
 *)
let ex1 () =
  let act = Var.(make_symbRow 1 (make "action" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make_symbRow 1 x in
  let program =
    sequence [
        choice
          (sequence [
               assume (eq_ (var act) zero);
               assign x (var cp_x)
          ])
          (sequence [assume (eq_ (var act) one); skip]);
        assert_ (eq_ (var x) one)
      ]
  in
  let vc = wp program true_ in
  let p4 =
    Printf.sprintf
      "table t {\n  keys {} \n  action = {λ ?x. x := ?x}\n}\n%s"
      "control {\n  t.apply();\n  assert x = 1;\n}"
  in
  format_print 1 p4 program vc

(**
   WARM UP 2 (Action Choice Only)

   Lets first consider a one-tablen no keys one-action program on one bit
   The p4 program looks like the following
   table t {
     keys {}
     action = { x.setValid() } | { x.setInValid() }
   }
   control {
     t.apply();
     assert (x.isValid())
   }

   In this example the assert statement is enforced by ensuring
   table t has rule x.setValid().

   Computing the weakest precondition of this is simple. we get
        ∀ x__valid.
        action(t) = 0 ⇒ True
        ∧ action(t) = 1 ⇒ False
        ∧ action(t) > 1 ⇒ x__valid = 1
   which is equivalent to
        ¬(action(t) = 1)
        ∧ action(t) ≤ 1
   which is equivalent to
       action(t) = 0

   which says that the specification is satisfied iff
      every packet that reaches t executes action 0

 *)
let ex2 () =
  let act = Var.(make_symbRow 2 (make "action" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let valid = Var.make "x__is_valid" 1 in
  let program =
    sequence [
          choice
             (sequence [
                  assume (eq_ (var act) zero);
                  assign valid one])
             (sequence [
                  assume (eq_ (var act) one);
                  assign valid zero]);
        assert_ (eq_ (var valid) one)
      ]
  in
  let vc = wp program true_ in
  let p4 = {|
table t {
  keys {}
  action = { x.setValid() } | { x.setInValid() }
}
control {
  t.apply();
  assert (x.isValid())
}|}
  in
  format_print 2 p4 program vc

(** WARM UP 3 (Key and action data interfere)

    table t {
      keys {x : exact}
      action = {λ ?z. z := ?z}
    }
    control {
      t.apply();
      assert (x != z)
    }

    REALISM: Determined Forwarding
    ** ASIDE **
    Alternate version that follows bf4's determined forwarding:
        table t {
          keys {eg_spec : exact}
          action = {λ p. eg_spec := p}
        }
        control {
          $eg_spec := eg_spec;
          t.apply();
          assert ($eg_spec != eg_spec)
       }
    ** END ASIDE **


    In this example, we need a relationship between ?x and ?z.
    The WP is:
        ∀ x. (action(t) = 0 ⇒ (x = ?x ⇒ x != ?z)
              ∧ (action(t) = 1) ⇒ x != z)

    The x and z should be eliminated the heuristics
    I've already implemented, yielding
       action(t) = 0 ∧ ?x != ?z
 *)
let ex3 () =
  let act = Var.(make_symbRow 3 (make "action" 1))in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make_symbRow 3 x in
  let z = Var.make "z" 1 in
  let cp_z = Var.make_symbRow 3 z in
  let program =
    sequence [
        assume (eq_ (var x) (var cp_x));
        choice
          (sequence [
               assume (eq_ (var act) zero);
               assign z (var cp_z)
          ])
          (assume (eq_ (var act) one));
        assert_ (not_ (eq_ (var x) (var z)))
      ]
  in
  let vc = wp program true_ in
  let p4 ={|
table t {
  keys {x : exact}
  action = {λ ?z. z := ?z}
}
control {
  t.apply();
  assert (x != z)
}|}
  in
  format_print 3 p4 program vc


(** WARM UP 4 (Keys Alone cannot satisfy)

    table t {
      keys {x : exact}
      action = {skip}
    }
    control {
      t.apply();
      assert (x != 0)
    }

    REALISM (?????)

    In this example, x is not modified, so it may be 0
    The WP is:
        ∀ x. ((x = ?x ⇒ action(t) = 0 ⇒ x != 0)
              ∧ (x = ?x ⇒ action(t) = 1 ⇒ x != 0))

    Since action(t) is only 1 bit, this is equivalent to
      ∀ x. (x = ?x ⇒ x != 0)

    We can see that this is equivalent to
       ∀ x. (x = ?x ⇒ x != 0)

    The sat solver will tell us that this is satisfiable.
    In fact we can see this for ourselves.
    The one-point rule gives
       ?x != 0

    Which is certainly satisfiable.

    However, the totality assumption is important here.
    The keys ?x must capture ALL of the possible inputs
    In other words, they are universally quantified, while
    action and action data are existentially quantifed.

    Now this is valid
*)
let ex4 () =
  let act = Var.(make_symbRow 4 (make "action" 1))in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make_symbRow 4 x in
  let program =
    sequence [
        assume (eq_ (var x) (var cp_x));
        choice
          (sequence [
               assume (eq_ (var act) zero)
          ])
          (assume (eq_ (var act) one));
        assert_ (eq_ (var x) one)
      ]
  in
  let vc = wp program true_ in
  let p4 =
    Printf.sprintf
      "table t {\n  keys {x : exact} \n  action = {skip}\n}\n%s"
      "control {\n  t.apply();\n  assert x != 0;\n}"
  in
  format_print 4 p4 program vc



(**
 **     Part 2
 ** Two-Table combinations of these interatcions
 **
 ***)


(** Example 5   Join & Determined forwarding

    table t₁ {
      keys {x : exact}   #ip address
      action = {λ ?m→ m := ?m} ## set metadata
    }
    table t₂ {
      keys {m : exact}
      action = {λ ?p → p := p} ## egress spec
    }
    control {
      $p := p
      t₁.apply();
      t₂.apply();
      assert ($p != p)
    }

    REALISM. Simplified version of NAT/Switch etc

    The instrumented program is
       $p := p
       assume x = ?x;
         (assume action(t₁) = 0; m := ?m₁)
         []
         (assume action(t₁) = 1; skip);
       assume m = ?m₂;
         (assume action(t₂) = 0; p := ?p)
         []
         (assume action(t₂) = 1; skip);
       assert ($p != p)

    The verification condition is
    ∀ p $p x m.
        x = ?x ⇒
          action(t₁) = 0 ⇒
               ?m₁ = ?m₂ ⇒
                   action(t₂) = 0 ⇒ p != ?p
                   ∧
                   action(t₂) = 1 ⇒ p != p
          ∧
          action(t₁) = 1 ⇒
              m = ?m₂ ⇒
                 action(t₂) = 0 ⇒ p != ?p
                 ∧
                 action(t₂) = 1 ⇒ p != p

    which is, in fact equivalent to
        ∀ p.  action(t₂) = 0 ∧ p != ?p

    Which says "every value of m must be covered and a new value of ?p assigned"

    Note that this is unsatifiable if we don't know the intial value of p.
    This is architecture dependent, so in reality we would specify that
    p != INITIAL_VALUE at the end of the pipeline.
    In this case we would be just fine.
 *)
let join_ex () =
  let act1 = Var.(make_symbRow 1 (make "action" 1))in
  let act2 = Var.(make_symbRow 2 (make "action" 1))in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make_symbRow 1 x in
  let m = Var.make "m" 1 in
  let cp_m1 = Var.make_symbRow 1 m in
  let cp_m2 = Var.make_symbRow 2 m in
  let p = Var.make "p" 1 in
  let g_p = Var.make_ghost 0 p in
  let cp_p = Var.(make_symbRow 2 p) in
  let p4 = {|
table t₁ {
  keys {x : exact}   #ip address
  action = {λ ?m→ m := ?m} ## set metadata
}
table t₂ {
  keys {m : exact}
  action = {λ ?p → p := p} ## egress spec
}
control {
  $p := p
  t₁.apply();
  t₂.apply();
  assert ($p != p)
}|}
  in
  let program =
    sequence[
        assign g_p (var p);
        assume (eq_ (var x) (var cp_x));
        choice
          (sequence [assume (eq_ (var act1) zero);
                     assign m (var cp_m1)])
          (assume (eq_ (var act1) one));
        assume (eq_ (var m) (var cp_m2));
        choice
          (sequence [assume (eq_ (var act2) zero); assign p (var cp_p)])
          (assume (eq_ (var act2) one));
        assert_ (not_ (eq_ (var g_p) (var p)))
      ] in
  let vc = wp program true_ in
  format_print 5 p4 program vc


(** Example 5   Header Validity

    table t₁ {
      keys {x : exact}   #ip address
      action = {λ ?m→ m := ?m} ## set metadata
    }
    table t₂ {
      keys {y : exact} ### ensure y is valid
      action = {skip)
    }
    control {
      t₁.apply();
      if (m = x) {y.setValid()} {y.setInvalid()}
      t₂.apply();
    }

    REALISM (???)

    The instrumented program is

       assume x = ?x;
         (assume action(t₁) = 0; m := ?m₁)
         []
         (assume action(t₁) = 1; skip);
         (assume (m = x); y.v = 1)
         [] {assume (m ≠ x); y.v = 0)
       assert y.v =1
       assume y = ?y₂;
         (skip) [] (skip)

    The verification condition is
        ∀ x m.
          x = ?x ⇒
            action(t₁) = 0 ⇒ x = ?m₁
            ∧
            action(t₂) = 1 ⇒ x = m

    which is, in fact equivalent to
       action(t₁) = 0 ∧ ?x = ?m₁

    Which says "every value of m must be covered and a new value of ?p assigned"

    Note that this is unsatifiable if we don't know the intial value of p.
    This is architecture dependent, so in reality we would specify that
    p != INITIAL_VALUE at the end of the pipeline.
    In this case we would be just fine.
 *)
let hv_ex () =
  let act1 = Var.(make_symbRow 1 (make "action" 1)) in
  let act2 = Var.(make_symbRow 2 (make "action" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make_symbRow 1 x in
  let m = Var.make "m" 1 in
  let cp_m1 = Var.(make_symbRow 1 m) in
  let yv = Var.make "yv" 1 in
  let p4 = {|
table t₁ {
  keys {x : exact}   #ip address
  action = {λ ?m→ m := ?m} ## set metadata
}
table t₂ {
  keys {y : exact} ### ensure y is valid
  action = {skip)
}
control {
  t₁.apply();
  if (m = x) {y.setValid()} {y.setInvalid()}
  t₂.apply();
}|}
  in
  let program =
    sequence[
        assume (eq_ (var x) (var cp_x));
        (* assign x (var cp_x); *)
        choice
          (sequence [assume (eq_ (var act1) zero);
                     assign m (var cp_m1)])
          (assume (eq_ (var act1) one));
        choice (sequence [assume (eq_ (var x) (var m)); assign yv one])
          (sequence [assume (eq_ (var x) (var m)); assign yv zero]);
        assert_ (eq_ (var yv) one);
        choice
          (assume (eq_ (var act2) zero))
          (assume (eq_ (var act2) one));
      ] in
  let vc = wp program true_ in
  format_print 6 p4 program vc

(** Example 6   simple_nat ingress

    A simplified version of the simple_nat program from the bf4 paper.
 *)
let simplest_nat () =
  let one = bvi 1 in
  let zero = bvi 0 in
  let ipv4_addr_width = 32 in
  let tcp_port_width = 32 in
  let port_width = 9 in
  let inst_type_width = 32 in

  let nat_id = 0 in
  let nat__action = Var.make_symbRow nat_id (Var.make "action" 2) in

  let ipv4_lpm_id = 1 in
  let ipv4_lpm__action = Var.make_symbRow ipv4_lpm_id (Var.make "action" 2) in

  let ipv4__valid = Var.make "ipv4__valid" 1 in
  let nat_ipv4__valid = Var.make_symbRow nat_id ipv4__valid in
  let tcp__valid = Var.make "tcp__valid" 1 in
  let nat_tcp__valid = Var.make_symbRow nat_id ipv4__valid in
  let ipv4__srcAddr = Var.make "ipv4__srcAddr" ipv4_addr_width in
  let nat_ipv4__srcAddr = Var.make_symbRow nat_id ipv4__srcAddr in
  let ipv4__dstAddr = Var.make "ipv4__dstAddr" ipv4_addr_width in
  let nat_ipv4__dstAddr = Var.make_symbRow nat_id ipv4__dstAddr in

  let tcp__srcPort = Var.make "tcp__srcPort" tcp_port_width in
  let nat_tcp__srcPort = Var.make_symbRow nat_id tcp__srcPort in
  let tcp__dstPort = Var.make "tcp__dstPort" tcp_port_width in
  let nat_tcp__dstPort = Var.make_symbRow nat_id tcp__dstPort in
  let stdmeta__egress = Var.make "standard_metadata__egress_spec"  port_width in
  let stdmeta__inst_typ = Var.make "standard_metadata__instance_type" inst_type_width in

  let meta__ipv4_da = Var.make "meta__ipv4_da" ipv4_addr_width in
  (* let meta__ipv4_sa = Var.make "meta__ipv4_sa" ipv4_addr_width in *)
  (* let meta__tcp_dp = Var.make "meta__tcp_dp" tcp_port_width in
   * let meta__tcp_sa = Var.make "meta__tcp_sp" tcp_port_width in *)

  let ipv4_lpm__meta__ipv4_da = Var.make_symbRow ipv4_lpm_id meta__ipv4_da in
  (* let ipv4_lpm__meta__ipv4_sa = Var.make_symbRow ipv4_lpm_id meta__ipv4_sa in *)
  let ipv4_lpm__port = Var.make_symbRow ipv4_lpm_id (Var.make "port" port_width) in

  let drop = Expr.bvi 511 port_width in
  let clone = Expr.bvi 999 inst_type_width in
  let program =
    [ assume (eq_ (var ipv4__valid) (var nat_ipv4__valid));
      assume (eq_ (var tcp__valid) (var nat_tcp__valid));
      assume (eq_ (var ipv4__srcAddr) (var nat_ipv4__srcAddr));
      assume (eq_ (var ipv4__dstAddr) (var  nat_ipv4__dstAddr));
      assume (eq_ (var tcp__srcPort) (var nat_tcp__srcPort));
      assume (eq_ (var tcp__dstPort) (var nat_tcp__dstPort));
      choice_seqs
        [[assume (eq_ (var nat__action) (zero 2));
          assign stdmeta__egress drop];

         [assume (eq_ (var nat__action) (one 2));
          assign stdmeta__inst_typ clone
         ];
         [assume (eq_ (var nat__action) (Expr.bvi 2 2)); skip];
         [assume (eq_ (var nat__action) (Expr.bvi 3 2)); skip]
        ];
      assume (eq_ (var meta__ipv4_da) (var ipv4_lpm__meta__ipv4_da));
      choice_seqs [
          [
            (* set_nhop *)
            assume (eq_ (var ipv4_lpm__action) (zero 2));
            (* copy "meta__nhop_ipv4" "row_ipv4_lpm__nhop_ipv4" 32;
             * setone "meta__nhop_ipv4__init"; *)
            assign stdmeta__egress (var ipv4_lpm__port);
            (* ast1 "ipv4__ttl__init" 1; *)
            (* decrement "ipv4__ttl" 8; *)
          ];
          [(* _drop *)
            assume (eq_ (var ipv4_lpm__action) (one 2));
            assign stdmeta__egress drop;
          ];
          [(*default (skip)*)
            assume (eq_ (var ipv4_lpm__action) (Expr.bvi 2 2));
            skip
          ];
          [(*default (skip)*)
            assume (eq_ (var ipv4_lpm__action) (Expr.bvi 3 2));
            skip
          ]
        ];
      assert_ BExpr.(not_ (eq_ (var stdmeta__egress) (zero 9)));
  ] |> sequence in
  let vc = wp program true_ in
  format_print 7 "" program vc

let multi_table_bf4_ex () =
  let p4 ={|
table t₁ {
  keys = {k₁};
  actions= {validate_H; nop}
}
table₂ {
  keys = {k₂};
  actions = {use_H;}
}
action validate_H(){
  H.setValid()
}
action use_H () {
  assert H.isValid();
  h.f := 55;
}
control {
  H.setInvalid();
  t1.apply();
  t2.apply()
}|} in
  let w = 8 in
  let k1 = Var.make "k1" w in
  let k2 = Var.make "k2" w in
  let t1 = 1 in
  let t2 = 2 in
  let zero = Expr.bvi 0 1 in
  let one = Expr.bvi 1 1 in
  let t1_k1 = Var.make_symbRow t1 k1 in
  let t2_k1 = Var.make_symbRow t2 k1 in
  let t2_k2 = Var.make_symbRow t2 k2 in
  let t1_act = Var.make_symbRow t1 (Var.make "action" 1) in
  let t2_act = Var.make_symbRow t2 (Var.make "action" 1) in
  let h__valid = Var.make "h__valid" 1 in
  let h__f = Var.make "h__f" w in
  let program =
    sequence [
        assign h__valid zero;
        assume (eq_ (var k1) (var t1_k1));
        choice_seqs [
            [assume (eq_ (var t1_act) zero);
             assign h__valid one;
            ];
            [assume (eq_ (var t1_act) one);
             skip]
          ];
        assume (eq_ (var k1) (var t2_k1));
        assume (eq_ (var k2) (var t2_k2));
        choice_seqs [
            [assume (eq_ (var t2_act) zero);
             assert_ (eq_ (var h__valid) one);
             assign h__f (Expr.bvi 16 w);
            ];
            [assume (eq_ (var t2_act) one);
             skip
            ]
          ]
      ]
  in
  let vc = wp program true_ in
  format_print 8 p4 program vc


let run_all _ =
  Printf.printf "+------------------------------------+\n%!";
  Printf.printf "|      WELCOME TO THE BEASTIARY      |\n%!";
  Printf.printf "|                                    |\n%!";
  Printf.printf "|   PLEASE do NOT feed the animals   |\n%!";
  Printf.printf "|        they are NOT friendly       |\n%!";
  Printf.printf "|                                    |\n%!";
  Printf.printf "|            ~-*~- for madmen only   |\n%!";
  Printf.printf " \\+--------------------------------+/\n\n\n%!";
  ex1 ();
  ex2 ();
  ex3 ();
  ex4 ();
  join_ex ();
  hv_ex ();
  simplest_nat ();
  multi_table_bf4_ex ();
