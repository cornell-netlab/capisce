open Cmd
open Expr
open BExpr   

let format_print num program vc =
  Printf.printf "-------------------------\n%!";
  Printf.printf "        Example %d \n%!" num;  
  Printf.printf "-------------------------\n%!";  
  Printf.printf "%s" (Cmd.to_string program);
  Printf.printf "-------------------------\n%!";
  Printf.printf "        VC\n%!";
  Printf.printf "-------------------------\n%!";
  Printf.printf "%s" (BExpr.to_smtlib vc);
  Printf.printf "=========================\n%!";
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
        ∀ x. hit(t) ∧ ?x = 1 ∨ ¬hit(t) ∧ x = 1
   
   The x should be eliminated the heuristics I've already implemented, yielding
        hit(t) ∧ ?x = 1
 *)
let ex1 () =
  let act = Var.(make_symbRow 0 (make "action" 1))in
  let hit = Var.(make_ghost 0 (make "hit" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make "?x" 1 in
  let program =
    sequence [      
        assume (eq_ (var act) zero); (* should reeally be act <= 1, but i dont have leq implemented*)
        choice 
          (sequence [
               assume (eq_ (var hit) one);
               assume (eq_ (var act) zero);
               assign x (var cp_x)
          ])
          (assume (eq_ (var hit) zero));
        assert_ (eq_ (var x) one)
      ]
  in
  let vc = wp program true_ in
  format_print 1 program vc

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
        hit(t) ∧ action(t) = 0 ⇒ True
        ∧ hit(t) ∧ action(t) = 1 ⇒ False
        ∧ ¬hit(t) ⇒ x__valid = 1
   which is equivalent to
        ¬(hit(t) ∧ action(t) = 1)
        ∧ ¬¬hit(t)
   which is equivalent to
       hit(t) ∧ action(t) = 0
   
   which says that the specification is satisfied iff
      every packet hits (t) and execute action (t)

   given a program p with table t
     〚hit(t)〛pkt ≜ ∀ pkt,pkt'.〚prefix(t,p)〛pkt = pkt' ⇒ ∃ ρ ∈ σ(t). t.matchrow(ρ,pkt).

 *)
let ex2 () =
  let act = Var.(make_symbRow 0 (make "action" 1))in
  let hit = Var.(make_ghost 0 (make "hit" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let valid = Var.make "x__is_valid" 1 in
  let program =
    sequence [      
        choice 
          (sequence [
               assume (eq_ (var hit) one);
               choice
                 (sequence [
                      assume (eq_ (var act) zero);
                      assign valid one])
                 (sequence [
                      assume (eq_ (var act) one);
                      assign valid zero])])
          (assume (eq_ (var hit) zero));
        assert_ (eq_ (var valid) one)
      ]
  in
  let vc = wp program true_ in
  format_print 1 program vc

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
        ∀ x. (hit(t) ⇒ (x = ?x ⇒ x != ?z)
              ∧ ¬hit(t) ⇒ x != z)
   
    The x and z should be eliminated the heuristics
    I've already implemented, yielding
       hit(t) ∧ ?x != ?z
 *)
let ex3 () =
  let act = Var.(make_symbRow 0 (make "action" 1))in
  let hit = Var.(make_ghost 0 (make "hit" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make "?x" 1 in
  let program =
    sequence [      
       assume (eq_ (var act) zero); (* should reeally be act <= 1, but no leq yet in bexpr module*)
        choice 
          (sequence [
               assume (eq_ (var hit) one);
               assume (eq_ (var x) (var cp_x));
               assume (eq_ (var act) zero);
               assign x (var cp_x)
          ])
          (assume (eq_ (var hit) zero));
        assert_ (eq_ (var x) one)
      ]
  in
  let vc = wp program true_ in
  format_print 1 program vc


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
        ∀ x. (hit(t) ⇒ (x = ?x ⇒ x != 0)
              ∧ ¬hit(t) ⇒ x != 0)
 
    The implemented heuristics should reduce this to 
       ∀ x. ((hit(t) ⇒ (x = ?x ⇒ x != 0)) ∧ hit(t))

    We can see that this is equivalent to
       ∀ x. (hit(t) ∧ (x = ?x ⇒ x != 0))

    Which is satisfied when hit(t) = TRUE and ?x = 2 (x could be anything except 0).
    
    The the math is actually also eliminating (hit(t)).
 
    but this seems very strong. See the Action Data example above.
*)
let ex3 () =
  let act = Var.(make_symbRow 0 (make "action" 1))in
  let hit = Var.(make_ghost 0 (make "hit" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make "?x" 1 in
  let program =
    sequence [      
       assume (eq_ (var act) zero); (* should reeally be act <= 1, but no leq yet in bexpr module*)
        choice 
          (sequence [
               assume (eq_ (var x) (var cp_x));
               assume (eq_ (var hit) one);
               assume (eq_ (var act) zero)
          ])
          (assume (eq_ (var hit) zero));
        assert_ (eq_ (var x) one)
      ]
  in
  let vc = wp program true_ in
  format_print 1 program vc

  
(** WARM UP 5 (Hit(t) has weird semantics in tables.)

    table t {
      keys {x : exact}
      action = {x := x - 1}
      default = {x = 3}
    }

    control {
      t.apply();
      assert (x >= 0)
    }
 
    REALISM (TTL) 

    The WP is:   
        ∀ x. (hit(t) ⇒ (x = ?x ⇒ x - 1 > 0)
              ∧ ¬hit(t) ⇒ 3 > 0)
    
*)

  
(** PATH CONSTRAINT

    two-table two-action program on four bits
    The p4 program looks like the following
    table t {
      keys {}
      action = {λ ?x. out := ?x}
    }
    table t {
      keys {}
      action = {λ ?x. out := ?x }  
    }
    control {
      t.apply();
      assert (x = 1)
    }
   
    Computing the weakest precondition of this is simple. we get
      ∀ x. hit(t) ∧ ?x = 1 ∨ miss(t) ∧ x = 1
   
    this is eliminated by our heuristics
*)
let ex1 () =
  let act = Var.(make_symbRow 0 (make "action" 1))in
  let hit = Var.(make_ghost 0 (make "hit" 1)) in
  let one = bvi 1 1 in
  let zero = bvi 0 1 in
  let x = Var.make "x" 1 in
  let cp_x = Var.make "?x" 1 in
  let program =
    sequence [      
        assume (eq_ (var act) zero); (* should reeally be act <= 1, but i dont have leq implemented*)
        choice 
          (sequence [
               assume (eq_ (var hit) one);
               assume (eq_ (var act) zero);
               assign x (var cp_x)
          ])
          (assume (eq_ (var hit) zero));
        assert_ (eq_ (var x) one)
      ]
  in
  let vc = wp program true_ in
  format_print 1 program vc  
    
