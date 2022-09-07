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

# Variable scoping
 
A smaller potential optimization in generating the VCs is to do QE while we're
generating the VC (though this may make things if we e.g. bitblast). In the
passive form, we can attempt QE on the formula this is by eliminating the output
variables when the variable index changes. This analysis only works when
traversing the tree in the backwards direction. This may only be sound at "phi
nodes" when the indices are synchronized.

# Path-based WP

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

## The Problem (Size)

The problem is that for our larger programs (switch .p4), the program has too
many paths. For instance, switch.p4 has something like 75 quadrillion paths (6
quadrillion with a constant parser).

Presenting this formula with 10 million conjuncts to a user is a completely
ridiculous proposition. Even monitoring it will be challenging. if each table
has 1024 rules in it and there are 20 tables, thats 10,000,000 × 1024 × 20,
which is way too big to check on every rule insertion.

## A Database Of Formulae

There are a few pieces of redeeming information:
1. We only need to compute the 4quadrillion formulae once
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

## Tackling path explosion

Switch.p4 has 75 quadrillion paths..

The problem with a database of formulae is that it needs to house all
75quadrillion paths, which is way too many. We need some way to reduce the number
of formulae that we generate.

One heuristic is to eliminate unfeasible paths as soon as we observe that they
are infeasible using an SMT solver. Then we can use the UNSAT-core to eliminate
other paths that are infeasible for the same reason. Hopefully this can tame the
search space into the realm of the feasible. Lets look at an example.

    {x:= 6} [] {x := 5};
    {assume x = 5; y := 5} [] {assume x ≠ 5; y := 0}
    
In this program, we would naively explore 4 different paths:

    {x := 6; assume x = 5; y := 5} []  (×)
    {x := 6; assume x ≠ 5; y := 0 } []
    {x := 5; assume x = 5; y := 5} [] 
    {x := 5; assume x ≠ 5; y := 5}    (×)
    
Note that while in the path version we can immediately see that the branches
marked with an `×` are infeasible because `6 = 5` is false and `5 ≠ 5`is false,
this information is not obvious to us in the original program, because at the
end of the branch point, all we know is that `x ∈ {5,6}`. So we need to do
something smarter. One option is to compute the weakest precondition of each
path, which would let us immediately observe that these paths are infeasible:

    ¬ (x = 5) ∨ ... ∧
    ...
    ¬ (5 ≠ 5) ∨ ... 

However, we want to be able to _learn_ from the infeasible paths and generalize
so that we dont have to compute the full path again. The basic idea is to keep a
knowledge base Ω of sub-paths that are infeasible. 

The algorithm proceeds in three steps: (1) Do QE on the path constraint (2) if
false, compute unsat-core, and (3) add paths that traverse unsat core to
knowledge base. Then when we start to generate new paths, we can avoid
generating the infeasible prefixes.

For our sanity, lets assign each AST node a numerical value indicated between
angle brackets, e.g. `⟨i⟩`. This will allows us to uniquely identify paths
through the program.
    
    {⟨1⟩ x := 6} [] {⟨2⟩ x:= 5};
    {⟨3⟩ assume x = 5; ⟨4⟩y := 5 } [] {⟨5⟩ assume x ≠ 5; ⟨6⟩ y := 0 }
    
So now we'll compute the path condition for the first path, `⟨1,3,4⟩`,
which is

    (assert (! (= x₁ 6) :named point_1))
    (assert (! (= x₁ 5) :named point_3))
    (assert (! (= y₁ 5) :named point_4))
    (get-unsat-core)

Which gives the unsat core of `(point_1 point_3)`. From this unsat-core, we can
generalize and add to our knowledge base the fact that means that any path that
traverses both `⟨1⟩` and `⟨3⟩` will be infeasible.

The current example is not sufficienly large enough to realize the gains.
However, if we add two disjunctions to the program, one between the two
branches, and one after the two branches, then we'll see the power:

    {⟨1⟩ x := 6} [] {⟨2⟩ x:= 5};
    {⟨3⟩ z := 6} [] {⟨4⟩ z:= 5} [] {⟨5⟩ z := 99};
    {⟨6⟩ assume x = 5; ⟨7⟩y := 5 } [] {⟨8⟩ assume x ≠ 5; ⟨9⟩ y := 0 };
    {⟨10⟩ w := 6} [] {⟨11⟩ w := 5} [] {⟨12⟩ w := 99}
    
Now we have many many more paths:

    ⟨1,3,6,7,10⟩ ⟨2,3,6,7,10⟩ 
    ⟨1,3,6,7,11⟩ ⟨2,3,6,7,11⟩
    ⟨1,3,6,7,12⟩ ⟨2,3,6,7,12⟩
    ⟨1,3,8,9,10⟩ ⟨2,3,8,9,10⟩
    ⟨1,3,8,9,11⟩ ⟨2,3,8,9,11⟩
    ⟨1,3,8,9,12⟩ ⟨2,3,8,9,12⟩
    ⟨1,4,6,7,10⟩ ⟨2,4,6,7,10⟩
    ⟨1,4,6,7,11⟩ ⟨2,4,6,7,11⟩
    ⟨1,4,6,7,12⟩ ⟨2,4,6,7,12⟩
    ⟨1,4,8,9,10⟩ ⟨2,4,8,9,10⟩
    ⟨1,4,8,9,11⟩ ⟨2,4,8,9,11⟩
    ⟨1,4,8,9,12⟩ ⟨2,4,8,9,12⟩
    ⟨1,5,6,7,10⟩ ⟨2,5,6,7,10⟩
    ⟨1,5,6,7,11⟩ ⟨2,5,6,7,11⟩
    ⟨1,5,6,7,12⟩ ⟨2,5,6,7,12⟩
    ⟨1,5,8,9,10⟩ ⟨2,5,8,9,10⟩
    ⟨1,5,8,9,11⟩ ⟨2,5,8,9,11⟩
    ⟨1,5,8,9,12⟩ ⟨2,5,8,9,12⟩

And the interactions betweeen 1 and 6 and 1 and 8 will greatly reduce the number
that we have to explore.

So let's assume we're lazily generating these paths in column-order. So we'll
start with the path ⟨1,3,6,7,10⟩ which corresponds to the following trace:

    x:=6; z:=6; assume x=5; y:=7; w:=6
    
and the following path constraint:

    (assert (! (= x₁ 6) :named point_1))
    (assert (! (= z₁ 6) :named point_3))
    (assert (! (= x₁ 5) :named point_6))
    (assert (! (= y₁ 7) :named point_7))
    (assert (! (= w₁ 6) :named point_10))

which we can use to get the `unsat-core`:

    (check-sat)
    (get-unsat-core)
    
Which is
    
    unsat
    (point1 point6)

Now we're cooking with gas! We can add `⟨…,1,…,6,…⟩` to our knowledge base,
which means that any time we see a path that goes through `⟨1⟩` and through
`⟨6⟩`, we know to stop generating paths.

Now, we don't need to generate the paths, `⟨1,3,6,7,11⟩`, or `⟨1,3,6,7,12⟩`,
because we know they'll all be infeasible. Our savings here comes from the fact
that we are checking the feasibility of prefixes, so we dont have to generate
the full path.

We'll then backtrack to path prefix `⟨1,3⟩` and generate the feasible paths
`⟨1,3,8,9,10⟩`, `⟨1,3,8,9,11⟩`, and `⟨1,3,8,9,12⟩`, because we must. Then we'll
backtrack again to `⟨1,4⟩`, which is so far a feasible prefix.

Now, as we explore the children of `⟨1,4⟩`, namely `⟨1,4,{6|8}⟩`, we'll observe
that `⟨…,1,…,6,…⟩∈ Ω`, so we skip the 3 paths that begin with prefix `⟨1,4,6⟩`
and just check the following:

    ⟨1,4,8,9,10⟩
    ⟨1,4,8,9,11⟩
    ⟨1,4,8,9,12⟩

A similar process lets us rule out the `⟨1,5,6,...⟩` paths, at which point we
backtrack all the way back up to the root and start with `⟨2⟩`. Now, we accept
the following paths as feasible following calls to Z3:

    ⟨2,3,6,7,10⟩
    ⟨2,3,6,7,11⟩
    ⟨2,3,6,7,12⟩
    
Then we backtrack to `⟨2,3⟩` and call Z3 on path `⟨2,3,8,9,10⟩`, which is similarly infeasible:
    
    (assert (! (= x₁ 5) :named point_2))
    (assert (! (= z₁ 6) :named point_3))
    (assert (! (≠ x₁ 5) :named point_8))
    (assert (! (= y₁ 0) :named point_9))
    (assert (! (= w₁ 6) :named point_10))
    (check-sat)
    ;; unsat
    (unsat-core)
    ;; (point_2 point_8)
    
And now we update our knowledge base `Ω` to be such that `⟨…,2,…,8,…⟩ ∈ Ω`.
Which lets us rule out the remaining infeasible paths. So rather than making
`36` QE-calls to Z3, we're making the following `18` calls for the feasible
paths and the `2` unsat-core Z3 calls described above.

    ⟨2,3,6,7,10⟩ ⟨1,4,8,9,11⟩ 
    ⟨2,3,6,7,11⟩ ⟨1,4,8,9,12⟩
    ⟨2,3,6,7,12⟩ ⟨2,5,6,7,10⟩
    ⟨1,3,8,9,10⟩ ⟨2,5,6,7,11⟩
    ⟨1,3,8,9,11⟩ ⟨2,5,6,7,12⟩
    ⟨1,3,8,9,12⟩ ⟨1,5,8,9,10⟩
    ⟨2,4,6,7,10⟩ ⟨1,5,8,9,11⟩
    ⟨2,4,6,7,11⟩ ⟨1,5,8,9,12⟩
    ⟨2,4,6,7,12⟩ ⟨1,4,8,9,10⟩
    
Hopefully this will reduce the number of paths that we need to explore to solve
a program like `switch.p4`.


### Implementation

In implementing this idea we have two important goals related to efficiency.
First, since we have 4 quadrillion paths, simply avoiding the calls to Z3 will
not be sufficient; we need to avoid _generating them in the first place_.
Second, we want to avoid scanning the knowledge base of learned infeasible
paths, since this will be too much overhead to do 4quadrillion times.

To do this, we'll lazily generate paths guarded with membership checks for the
knowledge base, which will be represented as a trie. This should allow us
constant time pruning of branches with a logarithmic insertion cost for paths.
See __Structuring Data__ for more details.

To fully explore the data structures, we need to first write down the core
algorithm.

### Algorithm

    φ ← ⊤
    S ← ⊤
    while S ≠ ∅:
        π ← get_next S
        ψ₀(D,$) ← wp(π, ⊤)
        ψ($) ← QE(∀D. ψ₀(D,$))
        if ψ($) = ⊥ then
           κ₁,…,κₙ ← unsat-cores(ψ₀(D,$))
           χ₁,…,χₙ ← map path_constraint [k₁;⋯;kₙ]
           S ← S ∖ χ₁ ∖ ⋯ ∖ χₙ
       else:
           φ ← φ ∧ ψ
    return φ

The algorithm proceeds as follows. Initialize `φ` to be `⊤`. This variable
represents the CPF to compute. Initialize `S` to `⊤` as well. This variable is
the (abstract) path generation structure. Then we'll loop untill `S` has no more
paths to generate `S = ∅`, and return φ. Inside the body of the loop, we first
compute the next path `π` from S. THen we compute the weakest precondition of
that path with respect to `⊤`, calling this formula `ψ₀(D,$)` to notationally
indicate that the free variables are the dataplane variables D and the symbolic
control plane variables `$`. Then we run QE on this formula to compute `ψ($)`,
which is equivalent to `∀ D. ψ₀(D,*)`. If QE returns a non-absurd formula, we
conjoin the results to `φ`. Otherwise, we try to understand why this path is
infeasible, so we can learn from our mistakes, by computing all of the unsat
cores `κ₁,…, κₙ` of `ψ₀(D,$)`. Then we convert theses to path constraints `χ₁,
…, χₙ`, and remove them from the set of things to generate. Of course this
set-minus operation is not really set difference, but it will be semantically
equivalent to the setminus operation. The next section discusses how we'll
structure the data to avoid this average case `O(M₀ × … × Mₙ)` removal, where
`Mᵢ` is the number of paths in the set denoted by `χᵢ`.


#### An early termination heuristic

One way that we can potentially end early is to optimistically check that we
have explored enough paths, i.e. that `φ ⇒ vc(p,⊤)`. This would change the way
that we explore the paths, in a way thats slightly unclear.

Do we try to randomly sample paths? how do we know that we have explored a
representative sample of paths? What heuristics can we use to increase the
likelihood of this early termination check succeeding?

#### An Abstraction Domain.

One way to do abstract interpretation here is to reason about tables. Rather
than reasoning on the granularity of paths, we can reason on the granularity of
table-paths. That is, what are the valid sequences of tables that can occur. The
idea here is that we can Once we have these, we can potentially abstract over
the tables themselves.

This is related to the monolithic table-abstraction idea, above, where we first
analyze the relationship between tables and then we analyze the implementation
of those tables. With our path-based analysis, however, we hope that by
analyzing a few paths through the tables we can generalize to a condition that
will handle all of the paths.

#### Structuring Data
 
 So how should we structure `S`? We need some way to generate paths, and another
 way to keep track of the paths that we generate. To generate paths, we'll run a
 DFS over a CFG `Gₚ` derived from the syntax of our program in question `p`.
 We'll also maintain a Trie `Ω` to represent the illegal paths in the knowledge
 base. The idea is that as we generate paths in CFP the `Gₚ` we will
 simultanously explore the corresponding path prefix in `Ω`. Then when we find a
 path constraint `χ`, we can add it to `Ω`, which may trigger some backtracking
 if a prefix of the current path is disallowed.
 
 To instantiate our algorithm with these data structures we need to provide
 three routines, (1) an emptiness check on `S`, a (2) `get_next` function, and
 (3) a set-minus function.
 
 Lets start easy. The emptiness check simply needs to check whether we have
 finished exploring the `Gₚ`. Once all of the paths have been explored, we'll
 declare the set `S` empty.
 
 The `get_next S` function is a bit more complicated. Here's how it works. `S`
 needs to maintain some search state: the current path `π`, and a worklist of
 children to try next `c`. These search states are maintained in a (stateful)
 stack of triples `w`. The following invariants hold:
 1.`∀ ⟨π,_⟩ ∈ w.  |π| > 0`
 2. `set(c) ⊆ Succ(ν)` --- that is, the elements in `c` are children of ν.
 3. `Ω.current() = fst(last(w.peek()))`
 
 Its possible that between calls of `get_next`, we have invalidated our current
 path. So the first thing we need to do is restore our search state `w` to
 correspond to a path prefix permitted by `Ω`. To do this, we may need to
 backtrack. The `backtrack` routine is defined below:
 
    if not w.is_empty():
        ⟨π, c⟩ ← w.peek()
        match Ω.get_ok_prefix(π) with
        | None → skip 
        | Some π → w.pop(|π| - |π'|)

The `Ω.get_ok_prefix(π)` returns the longest prefix of π that is not ruled out
by `Ω`.
 
 Then we can define `get_next S` as the following:
 
     backtrack(w, Ω)
     until is_empty w:
        ⟨π, c⟩ ← w.pop() 
        match c with
        | [] →
            Ω.parent()
            if ν.is_leaf() then
               return π
        | ν₀::c₀ →
            w.push(⟨π,c₀⟩)
            if Ω.step_to_child(ν):
                w.push(⟨π;ν, Succ(ν)⟩)

The loop maintains the search state using `w`, when `w` is empty, there are no
more paths to explore. The first thing the loop does is to pop off the top of
the stack, which is a node `ν` and the unexplored children `c`. Because of
invariant 2, we know that Ω is "focused" on the node `ν`. So the function
`Ω.check_prefix()` checks the predecessor chain in the tree to see whether a new
path-constraint has been added to the prefix. If not then we call `Ω.parent()`
to backtrack to `ν`'s parent node. Otherwise, if the prefix has not been
ruled-out, we try to step to the child `ν₀`. If thats successful, we push `⟨π;ν,
Succ(ν)⟩` onto the stack again and continue looping.

Note that when an invalid prefix has been discovered this algorithm will
automatically backtrack until the syntactically left-most path-choice in χ was
is removed. There's probably a micro-optimization here where we jump multiple
steps at once by getting more information from the unsat core, but this suffices
for now. Observe that checking takes time `O(d)` where is the depth of the DAG,
whereas checking successors is constant time. There's probably some way to
reduce some redundant `O(d)` checks here, but its not clear yet.

The last piece here is removing the path constraints χ, written `S ∖ χ`. This
operation is construed as insertion into the trie `Ω`, so to describe how it
works we need to provide more intuition about how Ω is strcutured. Each node in
`Ω` has two possible labels: `×` (infeasible) and `?` (unknown). If any node is
infeasible than all of its children are infeasible. Each edge is labeled with
the ID of a choice-point in the program. When we add a path prefix to the trie,
we are adding an infeasible path. 

The knowledge base `Ω` has an additional piece of state beyond the trie. Itself,
and a pointer to the current node. `Ω.parent()` moves the current node to the a
parent, and `Ω.child(c)` moves the pointer to the `c`th child.
`Ω.get_ok_prefix(π)` starts at the root of `π` and walks forward on nodes
labeled with `?` until either the nodes in `π` are exhausted, in which case it
returns `None`, or until an infeasible (`×`) node `π[i]` has been found, at
which point it returns the preceeding path of feasible nodes `π[:i]`
(noninclusive). 

Now, insertion simply adds the path constraints χ to `Ω` by recursively
descending `χ` on all matching paths and marking the leaves infeasible.

    let rec add χ Ω ν =
        match χ with
        | [] → mark_infeasible Ω ν
        | None::χ →
            Ω ← fill_unknown_succs Ω ν
            fold (succs Ω ν) ~init:Ω ~f:(add χ)
        | Some choice::χ →
            Ω ← fill_unknown_succs Ω ν
            Ω ← step Ω choice
            add χ Ω ν


#### Thoughts about concurrency

One way we could get several orders of magnitude of speedup is to use the 1k
cores in the Pronto/Atlas servers to give us a few orders of magnitude speedup
(assuming no-cost synchronization). 

To implement this algorithm concurrently, we can use a Director/Worker paradigm,
where a director assigns batches of paths to each worker. The challenges are
coordinating the infeasible path constraints χ₁,…, χₙ, and 

### Remarks

__All Unsat Cores__. One way we can make this better is to collect all of the
unsatisfiable cores from a single unsatisfiable path, then we can get more bang
per infeasible path.

__Necessity of Passivisation__. One important aspect that's elided from the
above notes is that our programs must be in the passive form. We need the phi
nodes for our path-elimination to be complete. For instance, consider the
following program:

    ⟨0⟩ x := 5;
    { ⟨1⟩ x := 0 } [] { ⟨2⟩ skip };
    { ⟨3⟩ assume x = 5} [] { ⟨4⟩ assume x ≠ 5 }

So if we start with `⟨0,2,4⟩`, without passifization, we'll get the following path constraint:

    x₁ = 5 ∧ true ∧ x₁ = 5
    
This path is definitely infeasible, and a call to Z3's unsat-core will give us
the sub-path `⟨0, …, 4⟩` to add to the knowledge base. The problem is that there
_are_ feasible subpaths that have `⟨0,…,4⟩` as a subpath, namely `⟨0,1,4⟩`,
because `⟨1⟩` assigns `x` to `0`:

    x₁ = 5 ∧ x₂ = 0 ∧ x₂ ≠ 5
    
which is feasible!

The mistake that we made was in not observing the implicit phi node in the first
disjunction. To do this we have to update the indices in both paths
corresponding to the modifications in the other. So our original path constraint
for `⟨0,2,4⟩` should have been 

    x₁ = 5 ∧ x₂ = x₁ ∧ x₂ = 5
    
In which case, the unsat-core will identify the sub-path as `⟨0,2,4⟩`, which
correctly allows `⟨0,1,4⟩` to be generated.
