# Quantifiers

I'm very confused.




## Problem Statement

    Given 
       φ(C,D) formula
       D      set of first-order dataplane variables
       C      set of second-order control plane variables (functions?)
       
    Compute the weakest ψ(C) such that
       ∀ C. ∀ D. ψ(C) ⇒ ψ(C,D)
       
## Proposal 1

Quantifier elimination

    ∀ D, φ(D,C) sat
    iff
    ∀ ?X. ∃ ?Y. unskolem(C, ∀ D. φ(D,C)) sat
    iff
    ∀ ?X. ∃ ?Y. QE(D, unskolem(C, ∀ D. φ(D,C))) sat
    iff
    QE(D, ∀ D. φ(D,C)) sat




