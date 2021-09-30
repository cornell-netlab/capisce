# Interpreting Tables as functions

The most-correct approach we've seen so far. Uses a (second-order) function to
describe tables. This is dramatically more expressive and allows us to make cross-row comparisons in a way that we cannot do using FOL. P4v and Vera suggest that for DP verification we don't need this much power. In this document I sketch a way to use propositional quantifier elimination to compute a second-order condition.

First though I want to remind us _why_ we want to use functions at all

## Background
Given a program c, introduce uninterpreted functions 
            σₜ : K → A × D
for every table t. Assume that the tables read only a single key and set an
action identifier and a single action data variable. Notice that σₜ is a total
function.

A control plane condition is then some closed second-order formula φ(σ₁, …, σₙ).
There may need to be a secondary condition on the quantified variables. Only
variables representing table keys may be universally quantified? no existential
quantifiers?

Our instrumentation for a table t then becomes

    (t.apply)[?] ≜
         (a, d) := σₜ(k)
         [] {a = i; t.act[i](d)  | i ∈ |t.acts| }

Under this model, two ill-behaved examples from the past are now solved. Now the
weakest precondition is simply in terms of table σₜ.

## Fixing Problematic Example 1

The first problematic example is negative. The table has a single key, `x`, and
the only actions are no-ops. However, the assertion says that `x` must be `1`
The controller cannot ensure that the key (x) is one (1) via reads only. Our
verification condition should reflect this:

    table t {
        keys = x
        actions = {} {}
    }
    t.apply(); assert x = 1

Becomes the GCL sketch
    
    havoc σ
    assume ?φ(σₜ)   # ?φ is a hole 
    havoc a d x
    (a, d) := σₜ(x)
    {a = 0; skip} [] {a = 1; skip};
    assert x =1

Which is described by the formula 

    ∀ σ.
    φ(σₜ) ⇒ 
        ∀ a d x. 
            (fst(σₜ(x)) = 0 ⇒ x = 1) ∧
            (fst(σₜ(x)) = 1 ⇒ x = 1)

which is unsat. That is, there is no φ that validates the above formula.

### Where this broke down in our previous approach

Using symbolic rows rather than representing a function, we get the following
GCL sketch
    
    havoc $x $a
    assume ?φ($x, $a)     # ?φ is a hole
    havoc x
    assume x = $x
    {assume $a = 0; skip} [] {assume $a = 1; skip}
    assert x = 1

Which becomes the condition
    
    ∀ $x $a.
        ?φ ($x,$a) ⇒
            ∀x.
                x = $x ⇒ ($a = 0 ⇒ x = 1) ∧
                          ($a = 1 ⇒ x = 1)
                          
which _is_ sat, with `?φ($x,$a) = $x = 1`.

_Why does this go wrong?_ The computed formula describes the conditions that an
individual row must satisfy in order for assertions to pass. It is certainly the
case that all rows that match on 1 will satisfy the condition, but there's a
jump that we need to make from individual rows satisfying the condition to a
whole table.

## Fixing Example two, when the keys and actions interact 

This example is a positive one that shows we _do_ need some way to reason about
the keys in tables (i.e. its not enough to remove the `assume keys = symbolic
keys` from the previous example).

Consider a table with one key and two actions. The specification is the same as
the previous examples, i.e. that x = 1 at the end of ingress. The first action
decrements `x`, and the other just satisfies the specification. The
specification we want is that the key is `2`, we can pick either action,
otherwise we must pick the second action:

    table t {
        keys x
        actions = {x := x + 1} {x = 1}
    }
    t.apply; assert x = 1
    
which induces the following problem instance.

    havoc σₜ;
    assume ?φ(σₜ);  # compute ?φ
    havoc x a d;
    (a,d) := σₜ(x);
    {assume a = 0; x := x - 1} [] {assume a = 1; x := 1};
    assert x = 1
    
Translating this into a formula gives us

    ∀ σₜ. 
        ?φ (σₜ) ⇒
            ∀ x a d.
                (fst(σₜ(x)) = 0 ⇒ x - 1 = 1) ∧
                (fst(σₜ(x)) = 1 ⇒ 1 = 1)
                
Which is satsifiable, since setting

    ?φ(σₜ) ≜ ∀ x. x ≠ 2 ⇒ fst(σₜ(x)) = 1
    
makes the formula valid.

### Where this went wrong in the previous approach.
    
This actually isnt wrong in the previous approach. However, this example shows
that if we _remove_ the key-match assumption, we no longer get the weakest
condition, which is in tension with the previous example, which could have been
solved by removing it.

    havoc $x $a
    assume ?φ($x,$a);  # compute ?φ
    havoc x d;
    assume x = $x       #remove?
    {assume $a = 0; x := x - 1} [] {assume $a = 1; x := 1};
    assert x = 1
    
Translating this into a formula gives us

    ∀ $x $a. 
        ?φ ($x, $a) ⇒
            ∀ x d.
                x = $x ⇒ # remove?
                    ($a = 0 ⇒ x - 1 = 1) ∧
                    ($a = 1 ⇒ 1 = 1)

which is satisfiable via the formula

    ?φ ($x, $a) ≜ $a = 0 ⇒ $x = 2
    
However, if we remove the assume, the best condition we can compute is

    ?φ ($x, $a) ≜ $a = 1
    
Which is too strong.

## The Problem with the SO approach

The nice thing about our old approach is that we could frame the problem in
terms of FO-quantifier elimination. Now we are in the world of second-order QE,
and we don't want to be here. We're still in a decidable realm, but the space of
functions is exponentially larger than just bitvectors.

What if we can still frame the problem in terms of FO-QE?

The idea is to still do quantifier elimination on the FO-instrumentation (`$x`,
`$a`, etc), and then transform it into a formula on σ.

### The goal: 

Skolemization is a process by which functions can replace quantifier
alternations. Is there some way to instrument the programs such that
skolemization yields the correct program?

Observe. In a function, the outputs are computed based on the inputs. Let's
reflect this by `choose`-ing the table outputs based on `havoc`-ed inputs. 
Let's look at out examples.

#### Example 1, revisited

Lets instrument example 1 using this new strategy. The gcl sketch becomes 

    havoc $x;
    choose $a;
    assume ?φ($x, $a)  # compute ?φ
    havoc x d;
    assume x = $x;
    {assume $a = 0; skip} [] {assume $a = 1; skip};
    assert x = 1

The synthesis specification we compute from this is

    ∀ $x. ∃ $a.
        ?φ($x, $a) ⇒
            ∀ x d. x = $x ⇒
                    ($a = 0 ⇒ x = 1) ∧
                    ($a = 1 ⇒ x = 1)
                    
Which now has no solution! i.e. there is no non-vacuous way to instantiate ?φ.

#### Example 2, revisited
    
As an exercise, consider the following (alternate) instrumentation for the
second example

    havoc $x;
    choose $a;
    assume ?φ($x,$a);  # compute ?φ
    havoc x d;
    assume x = $x;
    {assume $a = 0; x := x - 1} [] {assume $a = 1; x := 1};
    assert x = 1
    
The synthesis sepcification we compute from this is
    
    ∀ $x. ∃ $a.
        ?φ($x,$a) ⇒ 
            ∀ x d.
                x = $x ⇒
                    ($a = 0 ⇒ x - 1 = 1) ∧
                    ($a = 1 ⇒ 1 = 1)
                    
Which is satisfiable! As desired! Observe this with
    
    φ($x, $a) ≜ $a = 0 ⇒ $x = 2
    
    
### Recovering an Abduction algorithm.

##### Hypothesis
> For single-table programs, the σ-instrumented program is valid with trivial ?φ 
> iff the havoc-choose program is valid with trivial ?φ

##### Algorithm to compute φ(σₜ)
    
    abduce(c):=
        Given single-table c on DP variables D.
        Let c[?] be the first-order instrumentation of c.
        Let (∀K. ∃A. ∀D. φ(K,A,D)) = wp(c[?], ⊤).
        Let ψ(K,A) = QE(D, φ(K,A,D))
        Return 
            skolemize(∀K. ∃A. ψ(K,A))
        
##### Proof idea

Let ∀ K. ψ₂(K,σ) = wp(c[??], ⊤), where c[??] is the second-order instrumentation of c, and ∀ K. ψ(K,σ) = abduce(c).

Show ∀ σ. (∀ K. ψ₂(K,σ) ⇔ ∀ K. ψ(K, σ)).

(⇒) Let σ be such that ∀ K. ψ₂(K,σ).
     Show that σ is a proof of (∀K. ∃A. ∀D. φ(K,A,D)) = wp(c[?], ⊤).
     By Skolem Correctness, 
            ∃ σ₀. ∀ K. ψ(K, σ₀) ⇔ ∀K. ∃A. QE(D, φ(K,A,D))
     Show that if σ is a proof of (∀K.∃A.∀D.φ(K,A,D)) then ∀K.ψ(K,σ) is true.
     Conclude by QE-equivalence. 
        
(⇒) sim.
     
#### Example 2

Returning to our previous example, 

    ∀ x. ∃ $a.
        ∀ x.
            x = $x ⇒
                ($a = 0 ⇒ x - 1 = 1) ∧
                ($a = 1 ⇒ 1 = 1)
            
Should yield (by the one-point rule) 

    ($a = 0 ⇒ $x - 1 = 1) ∧
    ($a = 1 ⇒ 1 = 1)

Now if we substitute `σₜ($x)` in for `$a`, we get

    (σₜ($x) = 0 ⇒ $x - 1 = 1) ∧
    (σₜ($x) = 1 ⇒ 1 = 1)
    
which is the condition we wanted.

Whats the quasi-formal argument for why this works.


## Generalizing

This algorithm seems to work for programs with single tables. However it gets
more complicated when we have programs with multiple tables. Lets assume there
are two tables, with keys K₁ and K₂ and actions A₁ and A₂. Now, the first-order
verification conditions we generate for this program will look like

    ∀ K₁, K₂. ∃ A₁, A₂. φ(K₁, K₂, A₁, A₂)
    
Now, we can no longer do standard skolemization. We would get functions f₁ and
f₂ with types fᵢ : K₁ × K₂ → Aᵢ. This is not good! This interpretation of these
fᵢs are that there are two tables that match on all of the keys of all the
tables. We need to restrict the domain of K₁ and K₂ when we skolemize.

We can do this using a choose operator, rather than an existential quantifier,
which lets you set the domain from which the output is comuted. In some sense we
have

    ∀ K₁, K₂. Ꜿ (A₁ ◁ K₁). Ꜿ (A₂ ◁ K₂). φ(K₁, K₂, A₁, A₂)

which we want to show is equivalent to 

    ∃ σ₁ : K₁ → A₁, σ₂ : K₂ → A₂.
      ∀ K₁, K₂. φ(K₁,K₂,σ₁(A₁),σ₂(A₂))


With ∃ instead of Ꜿ, its clear to see the implication from skolemized to unskolemized, but the reverse direction is not clear. How do we constrain the semantics of Ꜿ so that its value is dependent on the variables.

However. These choose operators have weird semantics, and I'm not sure what they
should be. It makes sense to model this as a two player game. If player-∀ picks
(5,4) and player-∃ picks (3) for A₁, player-∃ cannot change their move for
(5,6), and must again play (3).


