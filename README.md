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


