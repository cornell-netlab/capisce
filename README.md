# A new encoding idea

Here's a new encoding strategy for the CPI problem. The core idea is that we'll
decompose the problem into two phases, similar to Scythe, but less structurally
so.


## Stage 1
In the first stage, we model each table as an input-output function on the
variables it reads or writes. Cosnider the following table:

    action a(z){
        w := z
    }
    
    action b(){
        w := q
    }

    table t {
        keys = {x;y}
        actions = {a, b}
    }

Rather than understanding this table as a complicated if-statement that reads
the keys and selects and action and action data, we simply model this as an
input-output function on all of the variables. As a notational convenience,
we'll use ghost variables prefixed with the dollar sign to indicate that the
variable is a control plane variable, and ghost variables prefixed with a euro
sign € to indicate that theyre dataplane instrumentation. Here's the encoding of
table t:

    assume x = $x ∧ y = $y;
    t.action_run := $a;
    assume q = %q;
    assume z = $z;
    assume w = %w;
    
Now we can compute the VC for this table w.r.t some constraint on `w`, `φ(w)`.
This becomes:

    x = $x ∧ y = $y ⇒
    q = %q ⇒
    z = $z ⇒
    w = %w ⇒ 
    φ(w)
    
So now we want to eliminate all of the non-ghost variables from this term. To do
this we'll do QE on the variables:

    QE(∀x y z q w.
        x = $x ∧ y = $y ⇒
        q = %q ⇒
        z = $z ⇒
        w = %w ⇒ 
        φ(w))
        
This gives us simply
    
    φ(%w).
    
    
## Stage 2

In the second stage, we need to eliminate the variables that are not valid
control plane variables, namely the `%*` variables. To do this, we'll use our
original encoding of tables, using the percent-variables instead of the raw
dataplane variables:

    {assume $a = 0;
     %w := $z
    } [] {
     assume $a = 1;
     %w := %q
    }
    
And now we compute, just for this single table, the following VC:

    ∀ %w %q.
       $a = 0 ⇒ φ($z)
       ∧ $a = 1 ⇒ φ(%q)

Which is `$a = 0 ∧ φ($z)`.


The benefit here is that we can eliminate the tables in any order. We could even
give partial results if eliminating the expressions becomes too complicated.


# Optimizing Weakest Preconditions via Craig Interpolation

We propose Craig Interpolation as a way to to solve the CPI problem. This
optimization composes with the previous one.

Given two formulae `φ(x₁)` and `ψ(x₂)`, such that `φ(x₁) ⇒ ψ(x₂)`, compute an
interpolant `I(x₁∩x₂)` such that `φ(x₁) ⇒ I(x₁ ∩ x₂) ⇒ ψ(x₂)`.

> _Remark_. This looks similar to the abduction problem, but its slightly
> different. In Abduction, we have ¬φ(c,d) is sat and want to compute the
> weakest formula φ(c) such that φ(c) ⇒ φ(c, d). All this is to say that we're
> not going to be able to use craig interpolation to solve CPI.

We are going to attempt to use Craig Interpolants to do semantic formula
simplification. We'll call this simplification procedure, `SemanticSimpl :
Formula → Formula` at heuristically determined points in the computation of the
verification condition. For instance, we might try to semantically eliminate
disjunctions.

    wp'(c₁ [] c₂, φ) = SemanticSimpl(c₁ [] c₂ ,φ)
    wp'(c, φ) = wp(c,φ)
    
The way that we'll implement `SemanticSimpl(c, φ)` is using a craig interpolant.
We'd like it to be the case that `SemanticSimpl(c, φ) ⇔ wp (c,φ)`. To this end,
we define `SemanticSimpl(c,φ)` to be the first interpolant for the following
expression:

    wp'(c, φ) ⇒ (wp'(c, $) ⇒ φ($))
        
where `wp(c,$)` is the weakest precondition of `c` w.r.t a symbolic packet `$`,
and `φ($)` is φ where each variable `x` is substituted with its symbolic
analogue `$x`.

Why is `SemanticSimpl` equivalent to wp here? Here's an informal
argument. By the IH, we have that `wp'(c,φ) ⇔ wp(c, φ)` and `wp'(c, $) ⇔
wp(c,$)`, so long as we keep φ general in the IH. So, we know, `SemanticSimpl`
computes an interpolant `I` such that `wp(c,φ) ⇒ I` and `I ⇒ (wp(c, $) ⇒ φ($))`.
Since `(wp(c,$) ⇒ φ($)) ⇔ wp(c,φ)`, conclude `I ⇔ wp(c, φ)`. □

Why do we think this is useful? We can see that the interpolants will be
equivalent to the weakest precondition function, and hopefully they will be
syntactically simpler, perhaps ruling out dead branches or unnecessary
conditions. If an interpolant is somehow larger that provided expression, we can
simply treat it as a noop.

The proof will be in the evaluation.


# Simplifying Weakest Preconditions

We've been looking into the `Tracer` and the `Tracer-X` projects which have some
intense abstraction and simplification tools. Lets look at one which might apply here.


## Inspiration 

We're inspired by the following paragraph from the Tracer paper that tries to
eliminate infeasible paths and simplify conjunctions. The key point of context
is that they are doing a SE forward analysis of the program at each program
point ℓ. Let ℓ be a choice point on guard `C`. To detect that a path (guarded by
either `C` or `¬ C`) is feasible, check that the strongest postcondition `φₚₒₛₜ`
satisfies the respective guard `C`. If the guard is unsat, then the path is
infeasible, and we can use the Unsat Core (UC) " to avoid growing the wp formula unnecessarily". 

> _Remark_. For instance, the formula `C ⇒ wp(S1,Q)` can be replaced with
> `wp(S1, Q)` if C ∉ UC. Otherwise, we under-approximate `C ⇒ wp(S1, Q)` as
> follows. Let `d₁ ∨ … ∨ dₙ` be `¬wp(S1,Q)`, then we compute the [the
> conjunction of] `(¬ ∃x₁', …, xₘ'. (C ∧ dᵢ))` [for each `i ∈ [n]`], where
> existential quantifier elimination removes the post-state variables `x₁', …,
> xₘ'`. A very effective heuristic if the resulting formula is disjunctive is to
> delete those conjuncts that are not implied by `UC` because the are more
> likely to be irrelevant to the infeasibility reason.


This paragraph is a bit dense, and, in fact, incorrect when read at face value.
For instance, the last sentence is saying that we keep only the conjuncts `(¬
∃x₁', …, xₘ'. (C ∧ dᵢ))` from the big conjunction when `UC ⇒ (¬ ∃x₁', …, xₘ'. (C
∧ dᵢ))`, however this is _never_ going to be the case, because by definition `UC
= ⊥`, so _every_ conjunct will just be deleted. 

To fix this confusion, we surmise that the authors meant the following:

>  A very effective heuristic if the resulting formula is disjunctive is to
> delete those conjuncts that are not implied by any `C ∈ UC` because the are
> more likely to be irrelevant to the infeasibility reason.

So at a high level what are Joffar et al doing? They are eliminating the guards
`C` if the guard can be satisfied, since there is then path that will execute
S1. Otherwise, via distributivity laws they locally scope the output variables
over the disjuncts of the negated wp (i.e. d₁, …, dₙ), and keep only the ones
that are likely to maintain the infeasibility.
 
 
## Pivoting to Inference

There are three challenges in pivoting these ideas to the CPI problem:
1. Framing – verification v.s. synthesis
2. Domain Challenges – Few infeasible paths
3. Abstraction – we want the _weakest_ CPI

### Framing
The biggest challenge in trying to use these techniques is that our setting is
different. Tracer(X) is a verification tool. Their goal is to prove validity. If
they do not prove validity, i.e. if they find a true counterexample, they can
terminate. We, however, are _explicitly_ interested in counterexamples. In fact,
our _entire goal_ is to synthesize a condition whose negation precisely
describes the set of counterexamples. When Tracer finds a counterexample, they
are done, when we find one, we're just getting started.

### Domain Challenges

The other challenge is that in the domain of P4 programs, we do not expect to
have many infeasible paths. Why is that? Since our starting precondition in any
SP-style VCGen will be`⊤`, and most of the guards in the program are in tables
(which means they controller-specified and will be feasible), or they are
if-statements that are processing data set by the controller or read from the
input packet (in which case they should also be feasible).


### Abstraction

The disjunct-deletion heuristic described above is an under-approximation. From
the outset our goal for the CPI project has been to generate weakest CPFs. We
need to take these observations and potentially make them sound.
 
## Minimizing WP

We want to generate a VC for a GCL program that has been instrumented in some
way. For example, let's say we have the following action-less table that either
sets the egress port value `port` or sets a drop bit `drop`, we want to ensure
that the program only sets the `port` value to the drop value `511` if the drop
value is also `1`. So we have the following program

    { assume $a = 0; port := $port  } 
      []
    { assume $a = 1; drop := 1 };
    assert (port = 511 ⇒ drop = 1);

The standard weakest precondition of this code is

    $a = 0 ⇒ $port = 511 ⇒ drop = 1
    ∧
    $a = 1 ⇒ port = 511 ⇒ ⊤
    
or equivalently

    $a = 0 ⇒ $port = 511 ⇒ drop = 1
    

This is pretty-well optimized, but should clearly just be `$a = 0 ⇒ $port ≠ 511`. This fact
will be discovered by our smart constructors without a call to Z3. However, in
practice, we don't use the standard WP, because it blows up. Instead, we use the
Flanagan & Saxe passified normal execution function. We can passify the program
to the following (`assume`s are implied by the use of `=` instead of `:=`)

    { $a = 0; port₁ = $port; drop₁ = drop₀  } 
      []
    { $a = 1; drop₁ := 1; port₁ = port₀ };
    assert (port₁ = 511 ⇒ drop₁ = 1)
    
And we compute the following VC:

    ($a = 0 ∧ port₁ = $port ∧ drop₁ = drop₀
     ∨
     $a = 1 ∧ drop₁ = 1 ∧ port₁ = port₀)
    ⇒
    port₁ = 511 ⇒ drop₁ = 1
    
which is actually much bigger. Not that our standard off the shelf optimizations
(expression propagation, constant folding, one-point rule) fail here. (we could
distribute the assertion, but again that's an exponential explosion.)

What we want to do instead is to perform a bidirectional (sp & wp) semantic
analysis of the program at each AST node to determine how to proceed. In doing
so, we will temporarily explode the complexity of the program, but this is okay,
because in this exploration we will solve sat problems for formula
simplification rather than QE ones for synthesis.

In this analysis we will compute a WP and a SP simultaneously, for instance the
case for `;` is _something like_ the following:

```ocaml
    let VC(c₁; c₂, φₚᵣₑ) : Formula.t option =
      let      ψ₁ = N(c₁) in       (* "SP" *)
      let%bind ψ₂ = VC(c₂, φₚᵣₑ) in (* "WP" *)
      match ∃ $. ∀ x. ψ₁ ⇒ ψ₂ with
      | UNSAT → None
      | SAT → 
         let d₁ ∨ d₂ ∨ ⋯ ∨ dₙ = ψ₂ in 
         let ψ₂' = ⋁ { dᵢ | i ∈ [n], ⊧ ∀ x. ψ₁ ⇒ dᵢ} in
         VC(c₁, ψ₂')
```


The basic idea is that at any node in the ast, we can check that the strongest
postcondition up to that point (`ψ₂` on line 3) implies the weakest precondition
after that point (`ψ₁` on line 4) with the control plane variables (`$`)
existentially quantified and the dataplane variables (`x`) existentially
quantified—i.e. the following condition on line 5

    ∃ $. ∀ x. ψ₁ ⇒ ψ₂

Assuming we're only exploring reachable paths, if the above query is unsat,
there is no CPF, because there is a reachable path whose bug cannot be avoided
by _any_ verification condition. However, if it is SAT, then we want to
eliminate any unnecessary elements of the proof obligation space we can. By
eliminating the disjuncts that have no proof. I.e. we only keep the disjuncts
`dᵢ` of `ψ₂` such that the following formula holds (line 8):

    ∃ $. ∀ x. ψ₁ ⇒ dᵢ
    
We then pass that formula recursively to compute the VC for `c₁`

*Example*. Let's consider the `$a = 0` branch of our running example, and add an
implicit `skip` at the end to trigger this analysis. 

    port₁ = $port; 
    drop₁ = drop₀; (* Lets call the program up to this point `c` *)
    skip
    
If we were to compute `VC(c;skip, port₁ ≠ 511 ∨ drop₁ = 1)`, we check that the
following is satisfiable:

    ∃ $port. ∀ port₁, drop₁, drop₀.
       port₁ = $port ∧
       drop₁ = drop₀
       ⇒
       port₁ ≠ 511 ∨ drop₁ = 1
       
Which it is with, say `$port = 0`. So now we check the satisfiability of each disjunct. First,

    ∃ $port. ∀ port₁, drop₁, drop₀.
       port₁ = $port ∧
       drop₁ = drop₀
       ⇒
       port₁ ≠ 511
       
Which is sat using the same model (`$port = 0`). Now we check

    ∃ $port. ∀ port₁, drop₁, drop₀.
       port₁ = $port ∧
       drop₁ = drop₀
       ⇒
       drop₁ = 1
       
So the VC for the rest of this branch is simply `port₁ ≠ 511`. Pushing it back
over the formula `drop₁ = drop₀` gives the following constraint:

       $a = 0  ⇒
       port₁ = $port ⇒
       drop₁ = drop₀ ⇒
       port₁ ≠ 511
       
The one point rule lets us conclude our final constraint:

    $a = 0  ⇒ $port ≠ 511

*Remark* Notice that the assumption `$a = 0` is missing from the assumptions in
our formulae. I'm not sure how to justify this, but it seems similar to the
guard-deletion that Tracer is doing. Morally, it seems right because you only
want to consider the _effect_ of choosing an action, not the action itself. Is
there a robust way to propagate this observation? Resolving this will tie into
how we analyze choices and assumes. It may actually be convenient here to
discard the passive form and the nondeterministic binary operator for
if-then-else and SSA, to distinguish between true assignments and choices.

*Remark* We haven't yet figured out how to completely close the gap between the
Flanagan and Saxe techniques and the path-based analysis above (which still
worst-case exponential WPs). It would be nice to maintain the quadratic-size
Flanagan & Saxe approach while employing some of these path-based simplification
techniques. The next section explores what to do if we don't have a way to
dramatically simplify the size of the formulae.

## Path-based WP

Barring some way to close the gap, lets explore what would happen if we computed
the WP as the optimized conjunction of all path-wps. This is logically
equivalent to Dijkstra's normal wp-algorithm (since all of our branch-points in
the original program are total). For our running example, the formula is the
following:

    $a = 0 ⇒  $port ≠ 511
    ∧
    $a = 1 ⇒ ⊤

We would like to consider these as separate formulae and eliminate the
quantified variables from each of them. This example is quite trivial, because
we've already eliminated the dataplane variables in the previous step, but in
general that may not be the case.

The benefit of doing this is that since we can eliminate quantifiers from each
branch separately, we can show that our tool actually makes progress through the
program.

*Remark.* Another idea is that we could use create more coarse-grained "slices"
depending on which actions we select through the program (e.g. enumerate the
crossproduct of action choices) which will create O(Nᴹ) paths, where N is the
number of tables and M is the max number of actions in the table this will be
approx (10⁵ = 10,000).

### The Problem (Size)

The problem is that for our larger programs (switch .p4), the program has too
many different branches. For instance, switch.p4 has something like 10 million
paths. 

Presenting this formula with 10 million conjuncts to a user is a completely
ridiculous proposition. Even monitoring it will be challenging. if each table
has 1024 rules in it and there are 20 tables, thats 10,000,000 × 1024 × 20,
which is way too big to check on every rule insertion.

### A Database Of Formulae

There are a few pieces of redeeming information:
1. We only need to compute the 10million formulae once
2. When we insert an exact-match rule, we only need to check it's interaction
with all of the other rules in the _other tables_.
   
   
The proposal is that we store the statically computed path-formulae in a
database indexed by the actions taken by that path. For instance, in our running
example, we'd have the following table (with key `(Action,Formulae)` to allow
associating multiple `Formulae` with the same `Action`)

| Action   |     Formulae    |
|----------|-----------------|
| `$a = 0` | `$port ≠ 511`   |
| `$a = 1` | `⊥`             |

Then whenever we insert a row into the P4 table, we can check only the formulae
that correspond to the affected vector of actions. This should reduce the
checking time by orders of magnitude.

We could also present an interactive tool that allows a developer to explore the
constraints required for different collections of actions.

## Variable scoping
 
A smaller potential optimization in generating the VCs is to do QE while we're
generating the VC (though this may make things if we e.g. bitblast). In the
passive form, we can attempt QE on the formula this is by eliminating the output
variables when the variable index changes. This analysis only works when
traversing the tree in the backwards direction. This may only be sound at "phi
nodes" when the indices are synchronized.

