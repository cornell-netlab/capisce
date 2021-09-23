# First, A Bunch of Problems

I found a bug in my approach to this problem. 

In order to provide semantics to dataplane constructs like "hit", I've
instrumented the program with ghost state (a la p4v) and then I use that ghost
state in the encoding of the switch state σ. (see Figures 6 and 7) for
details. The ghost variables use γₜ.f, where γₜ indicates that the variable
is a ghost variable for table t, and f indicates the specific field. We
write Gᶜ for the set of ghost variables in a command c or just G when c
is obvious/irrelevant/inferrable.

I also use symbolic variables to represent the symbolic controller state, using
ρₜ.f as the prefix. We have also (following Avenir) used ?fₜ to represent
these variables. We write Rᶜ for the set of ghost variables in a command c,
or just R when c is obvious/irrelevant/inferrable.

Theorem 4 proves that if we quantifier-eliminate the dataplane variables we get
an equivalent formula, though it incorrectly claims to solve the Inference Problem.

The algorithm we suggest is the following
      
     Given 
         c   Command
         D   dataplane vars of c
         R   symbolic vars of c[?]
         G   ghost vars of c[?]
         σ   forwarding state of c
         
     Compute
         φ(D,R,G) = wp(c[?],⊤)
         ψ(R,G) = QE(D, φ(D,R,G))
         return ψ(R,G)
         
The "correctness" follows Lemma 20 which says that ψ(R,G) ⇒ ∀ D. φ(D,R,G), and
ψ(R,G) is weakest, and from Theorem 3, which says that wp(c[σ],⊤) = ⦇σ⦈ᶜ ⇒
wp(c[?], ⊤)
         
Here's the problem. ψ(R,G) is expressed in terms of symbolic variables R
(which is fine), and ghost variables G (which is not). The ghost variables,
including `hit` and `miss` need to be eliminated from ψ(R,G). The ghost
variables G cannot be interpreted by σ.

So why dont we just eliminate G? Currently, the problem is that ⦇σ⦈ᶜ uses the
ghost variables G in order to give semantics to `hit`, including taking
snapshots of packet values before table application (see the first line of the
`t.apply` case of Figure 6).

So let's go back in the git history to when ⦇σ⦈ᶜ, only described the control
plane interface, and didn't include these problematic ghost/dataplane variables
G. Then, the definition is
    
     ⦇σ⦈ᶜ ≜ ⋀{ ⋁{rᵢ = ρₜ | rᵢ ∈ σ(t)} | t in tables(c) }
     
*Sidenote*. Note that we need σ(t) to be non-empty for this definition to be
sensible. If σ(t) = [] then the the ρₜ variables are unconstrained, which
corresponds to any possible table instance, not the specific empty table
instance. Nonemptiness is a reasonable assumption since every table has a
default action (even if its the implicit `noop` action).

So now, we can modify our algorithm to the following 

     Given 
         c   Command
         D   dataplane vars of c
         R   symbolic vars of c[?]
         G   ghost vars of c[?]
         σ   forwarding state of c
         
     Compute
         φ(D,R,G) = wp(c[?],⊤)
         ψ(R) = QE(D ∪ G, φ(D,R,G))
         return ψ(R)

The proof will follow from a modified version of Lemma 20 and Theorem 3.

Now, here's another problem. `hit(t)` is no longer doing any work. Consider the
following example.

    table t { 
       keys {y}; 
       actions {x := 2}
    }
    control {
       t.apply();
       assert x = 2
    }
    
The instrumentation of this program is the following (omitting action selection,
since there's only one action)
   
    ((assume hit(t);
      assume y = ?y;
      x := 2)
     []
     assume ¬ hit(t));
    assert x = 2.

which results in the following VC:

    ∀ y. ∀ x. (hit(t) ⇒ y = ?y ⇒ (2 = 2)) ∧ (¬ hit(t) ⇒ x = 2)

which is equivalent to (since 2=2 = ⊤ and (φ ⇒ ⊤) = ⊤)
  
    ∀ y. ∀ x. (¬hit(t) ⇒ x = 2 )

Lets assume that x is 2 bits and y is 1 bit. At this
point we can actually eliminate y, because it doesnt occur in the body.

    ∀ x. (¬hit(t) ⇒ x = 2 )
    
Because x doesnt occur on the RHS of the implication we can rewrite this as

    (¬hit(t) ⇒ ∀ x. x = 2)
    
Since ∀x. x = 2 is clearly false, we get

    ¬ ¬ hit (t)
    ===
    hit(t)
    
Which is a sensible condition. It must be that we `hit` in table `t`.
This condition can even be interpreted the following condition on σ:

    ∀ b ∈ (BV 2). ∃ ρ ∈ σ(t). ρ.y = b.
    
However, `hit(t)` is, as we said, a dataplane predicate. Its implemented using a
1-bit ghost variable `γₜ.hit`, so it should be universally quantified:

    ∀ γₜ.hit. γₜ.hit = 1
    ===
    ⊥

which is clearly incorrect. We already saw that we _can_ write down a constraint
on σ that correctly identifies the condition on σ.

## Straw man solution: Interpret hit(t) has a Control plane predicate.

We just saw that hit(t) does have a relationship with σ(t), so lets try write
down a semantics that agrees with the dataplane behavior.

Informally the dataplane the semantics of hit(t) are:

    hit(t) ≜ every packet that reaches t matches some row in σ(t)
    
Formally we can define this using a reach predicate Reach(σ,t,pkt)

    prefix(c,t) ≜ <inductively computes prefix 
                    e.g. c₁;assume b;c₂ = prefix(c₁;if b {c₂;t;c₃} {c₄};c₅, t)>
    Reach(c,σ,t) ≜ { pkt' | pkt,pkt' ∈ Pkt, pkt' =〚prefix(c,t)[σ]〛pkt}

Then we can model the semantics of hit as
    
    σ ⊧ᶜ hit(t) ⇔ ∀ pkt ∈ Reach(c,σ,t). ∃ ρ ∈ σ(t). ρ.matches(pkt)
    
*Remark.* There's a more complicated condition that takes into account
non-`exact` matches. We can ignore this for now. Solutions include: (1) an extra
condition to ensure that pkt doesn't match any of the previous rules, (2) all
matches are exact.

Lets try to apply this definition of hit to a slightly modified program to the
one we saw previously:

    table t {
      keys = {y}
      action {x := 0} {x := 1}
    }
    control {
        x := 0;
        t.apply();
        assert x = 0 
    }
    
The instrumented version of this program is the following:

    ((assume hit(t);
      assume y = ρₜ.y;
       (assume ρₜ.action = 0; x := 0) 
       [] (assume ρₜ.action = 1; x := 1)
     )
    [] (assume ¬ hit(t)))
    assert x = 0
    
Which produces verification condition equivalent to

    ∀ x y.
       hit(t) ⇒ y = ρₜ.y ⇒ ρₜ.action = 0 ⇒ 0 = 0
       ∧
       hit(t) ⇒ y = ρₜ.y ⇒ ρₜ.action = 1 ⇒ 1 = 0
       ∧ 
       hit(t) ⇒ 0 = 0
       
Using the one-point rule and scoping distribution rules for x and y this is
equivalent to

       hit(t) ⇒ ρₜ.action = 0

This seems like the right condition. It says "packets that hit in table t should
execute action 0". However this is a _dataplane_ interpretation.

What happens when we interpret it as a control plane formula using the semantics
above?

First we need to write down what it means for σ to satisfy ρₜ.action = 0. 

    σ ⊧ᶜ ρₜ.action = n ⇔ ∀ r ∈ σ(t). r.action = n.
    
This again seems sensible. However, when we try to interpret the implication,
**everything goes awry**:

    σ ⊧ᶜ hit(t) ⇒ pₜ.action = 0
    ⇔
    ¬ ∀ pkt ∈ Reach(c,σ,t). ∃ ρ ∈ σ(t). ρ.matches(pkt)
    ∨
    ∀ r ∈ σ(t). r.action = n.
    ⇔
    ∃ pkt ∈ Reach(c,σ,t). ∀ ρ ∈ σ(t). ¬ ρ.matches(pkt)
    ∨
    ∀ r ∈ σ(t). r.action = 0.

Which means can be satisfied using the following table

| y | Action |
|---|--------|
| 1 |  1     |

Because there is a packet (with y = 0) that misses in the table. So, even though
the rule picks the CORRECT ACTION, this table satisfies the constraint.

However, applying this table to the program 

    table t {
      keys = {y}
      action {x := 0} {x := 1}
    }
    control {
        x := 0;
        t.apply();
        assert x = 0 
    }

Triggers an assertion violation, because a packet with y =1 will have x set to
1, which violates the assertion.

## A Solution: Returning to Totality

Going back in the git history we had a requirement that σ(t) had to be total.
This gets rid of `hit` and `miss`, because every packet _hits_ in a table,
default actions are just a special kind of hit. A table with no specified action
has an implicit default action, `Skip` (or sometimes `Drop` depending on the
architecture) that is executed when the packet misses.

The second observation is that we need to define the semantics on
per-tuple-of-rows basis.
    
    σ ⊧ᶜ φ ⇔ ∀ r₁,…,rₙ ∈ Πₜ σ(t). r₁,…,rₙ ⊧ᶜ φ

where ρ₁,…,ρₙ ⊧ᶜ φ is defined in the obvious way
after converting ρ₁,…, ρₙ to a single model:

    {ρₜ.f ↦ rₜ.f | t ∈ tables(c), f in Fields(ρₜ) }

Now, all of of these issues are eliminated.

Lets consider each of the examples in order, to demonstrate their resolution.

#### Example 1

    table t { 
       keys {y}; 
       actions {x := 2}
    }
    control {
       t.apply();
       assert x = 2
    }
    
In this new approach, we assume that there is an implicit default action, i.e.
we're really translating the following program assuming totality

    table t { 
       keys {y}; 
       actions {x := 2} {@defaultonly Skip}
       default_action = skip
    }
    control {
       t.apply();
       assert x = 2
    }

However the `default_action` clause is interpreted as part of σ already, not
part of the program text.

Now the GCL program we generate is

    assume y = ρₜ.y;
       (assume ρₜ.action = 0; x := 2)
    [] (assume ρₜ.action = 1);
    assert x = 2
    
And the verification condition becomes

    ∀ x y.
      y = ρₜ.y ⇒ ρₜ.action = 0 ⇒ 2 = 2 # "hit"
      ∧
      y = ρₜ.y ⇒ ρₜ.action = 1 ⇒ x = 1 # "miss"
    
Which is equivalent to

    ρₜ.action = 0
    
If we interpret this as a control plane formula we get

    σ ⊧ᶜ ρₜ.action = 0 
    ⇔
    ∀ rs ∈ Πₜσ(t). rs ⊧ ρₜ.action = 0
    ⇔
    ∀ r ∈ σ(t). r.action = 0

Which is exactly what we want. (note that this cannot be vacuously satisfied
because σ(t) is total and therefore non-empty. Notice also that this is
capturing the exact same intuitions as the formula `hit(t)` that we computed
above.

### Example 2

Consider the following program

    table t {
      keys = {y}
      action {x := 0} {x := 1}
    }
    control {
        x := 0;
        t.apply();
        assert x = 0 
    }


In our new model of tables, we understand table `t` to be "syntactic sugar" for

    table t {
      keys = {y}
      action {x := 0} {x := 1} {@defaultonly Skip}
      default_action = Skip
    }
    
Where the default_action represents the starting state of σ(t). Now we generate
the following GCL program:

    assume y = ρₜ.y;
      (assume ρₜ.action = 0; x := 0)
      []
      (assume ρₜ.action = 1; x := 1)
      []
      (assume ρₜ.action >= 2; Skip);
    assert x = 0

We compute the following VC:
    
    ∀ x y.
        y = ρₜ.y ⇒ (
            ρₜ.action = 0 ⇒ 0 = 0
            ∧
            ρₜ.action = 1 ⇒ 1 = 0
            ∧
            ρₜ.action ≥ 2 ⇒ x = 0
        )

which is equivalent to

    ρₜ.action ≠ 1 ∧ ρₜ.action < 2

Which equals

    ρₜ.action = 0

Notice that the condition here is actually identical to the one generated in the
previous program. Which is sensible. In both cases the first action must be
triggered for all packets that traverse the table.

The ρₜ.action field is now capturing all of the information that the hit/miss
predicates would otherwise have captured. "Miss" can be implemented as ρₜ.action
≥ 2 and "hit" can be implemented as ρₜ.action < 2. But now these are strictly
control-plane predicates, and say nothing about the dataplane.

The reason we can do this is totality.

## Instrumentation

We now only need to change the definition of instrumentation for tables

    (t.apply())[?] ≜
        assume t.keys = ρₜ.keys;
        [] { assume [ρₜ.action]ₙ = [i]ₙ; aᵢ(ρₜ.data) | ∀ i ≤ 2ⁿ-1}
    
    where aᵢ = t.actions[i]

Not only is this much cleaner, it solves our bugs too.

## Metatheory

With this setting we need to revise our Theorem 3 and polish theorem 4. Theorem
3 should be rephrased in terms of the new symbolic interpretation of σ, and
theorem 4 needs to merge G and D.
