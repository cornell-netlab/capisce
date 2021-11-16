# A Hierarchy of Control Plane Logics

Here's the hierarchy of control plane logics we discussed last week.
For each we describe the following components:
- a grammar of formulae φ
- a grammar of expressions e
- the satisfaction relation σ ⊧ φ
- Upper bound on complexity of checking σ ⊧ φ 
- a list of existing tools that live in this space 

## Preliminaries
A control plane σ is a function of type

    σ : (t : Table) -> Keys(t) -> (Σ a : action(t). data(a,t))

Often, we write σ(t) as σₜ, and interpret it as a relation (e.g. by writing `r ∈ σₜ`).

We use r as a variable referring to a row in a table σₜ, and we use ρ to refer
to a concrete row in σₜ.

## Single-Table, Single-Row

### Grammar 

    φ ::= ⊥ | φ ⇒ φ | e < e
    e ::= x | e ⊕ e | [n]ₘ |
    ⊕ ∈ { +, ×, -, @, <<, …}
    x ∈ {keys, action, data}

Define syntactic sugar (∧, ∨, ¬, =, ≠, ≤, ≥) in the standard way.
    
### Satisfaction

The satisfaction relation here is only defined for a the control plane for a
single row, that is for a single ρ ∈ σₜ. We construct the model 
    
    μ(ρ) = {keys ↦ keys(ρ); action ↦ action(ρ); data ↦ data(ρ) }
    
Then we define satisfaction in the standard way (omitted).

    μ(ρ) ⊧ φ
    ...

To lift this to constrain a whole program, we have formulae tᵢ associated with each table φᵢ, i.e.

    (t₁,φ₁), (t₂,φ₂), …, (tₙ, φₘ)
    
Given a control plane σ, we check, for every pair (tᵢ, φ), that
    
    ∀ ρ ∈ σ(tᵢ), μ(ρ) ⊧ φᵢ
    
## Complexity of Monitoring 

Checking μ(ρ) ⊧ φ is linear in the size of φ. Simply substitute μ(ρ) and reduce.

Monolithic monitoring has complexity O(N·M) where N is the number of rows in the
largest table and M is the size of the largest φᵢ. 

Assuming nothing about the implementation of the (total) function σ, N = 2ʷ,
where w is the width of the largest table.

Incremental monitoring, only needs to check the row that has changed so it has
complexity O(M).

## Tools that live in this space

- p4constraints
- bf4 (*)

## Single-Table, Multiple Rows

### Grammar 

    φ ::= ⊥ | φ ⇒ φ | e < e
    e ::= P(r) | e ⊕ e | [n]ₘ |
    ⊕ ∈ { +, ×, -, @, <<, …}
    P ∈ {keys, action, data}

Define syntactic sugar (∧, ∨, ¬, =, ≠, ≤, ≥) in the standard way.
    
### Satisfaction

The satisfaction relation here is defined for a single-table control plane, i.e.
σₜ. For a formula φ, there are a collection of symbolic rows r₁, … , rₙ. We
define satisfaction in the standard way:

    {r₁ ↦ ρ₁, …, rₙ ↦ ρₙ} ⊧ φ
    ...

To lift this to constrain a whole program, we have formulae tᵢ associated with each table φᵢ, i.e.

    (t₁,φ₁), (t₂,φ₂), …, (tₙ, φₘ)

Now, given a σₜ, we construct the set of all combinations of n rows Cₙ(σₜ) and
construct the following set of models
    
    Μₙ(σₜ) = {{ r₁ ↦ ρ₁, … , rₙ ↦ ρₙ } | (ρ₁,…,ρₙ) ∈ Cₙ(σₜ) }
    
Given a control plane σ, we check, for every pair (tᵢ, φᵢ), where |fvs(φᵢ)| = n,
that
    
    ∀ μ ∈ M(σ(tᵢ)), μ ⊧ φᵢ
    
## Complexity of Monitoring 

Checking μ ⊧ φ is O(n·m), where n is the size of φ and m is the number of free
variables in φ. Since m is O(n), we can write O(n²). 

Is there a tighter bound?
- I'm thinking O(n · log n) if you use a binary tree map for μ. 
- We could also call the number of variables a constant and claim O(n).

Monolithic monitoring has complexity O(Choose N m · n²) where N is the number of rows in the
largest table, m is as above and n is the size of the largest φᵢ. 

Assuming nothing about the implementation of the (total) function σ, N = 2ʷ,
where w is the width of the largest table. 

Incremental monitoring only needs to check the rule that has changed. So we get
O(Choose (N -1) m · n²), where N is the number of rows in the changed table and
n is the width of the changed table.


## Tools in this space

None


## Multiple-Table, Single-Row

### Grammar 

    φ ::= ⊥ | φ ⇒ φ | e < e
    e ::= P(t) | e ⊕ e | [n]ₘ |
    ⊕ ∈ { +, ×, -, @, <<, …}
    P ∈ {keys, action, data}

Define syntactic sugar (∧, ∨, ¬, =, ≠, ≤, ≥) in the standard way.
    
### Satisfaction

The satisfaction relation here is only defined for the control plane for a
single row in a collection of tables. Here we fix a set of tables T = {t₁,…tₙ}.
We construct a model from a set of rows ρ₁, …, ρₙ, where ρᵢ ∈ σ(tᵢ) for all i ∈ {1,…,n}""
    
    μ(ρ₁, …, ρₙ) = {t₁ ↦ ρ₁, … , tₙ ↦ ρₙ}
    
Then we define satisfaction in the standard way (omitted).

    μ(ρ₁, …, ρₙ) ⊧ φ
    ...

To lift this to constrain a full control-plane state, σ we check, 
    
    ∀ ρ₁ ∈ σ(t₁),…, ρₙ ∈ σ(tₙ). μ(ρ₁,…,ρₙ) ⊧ φ
    
## Complexity of Monitoring 

Checking μ(ρ₁, …, ρₙ) ⊧ φ is O(n·m) where m is the size of φ. Simply substitute
each table in μ(ρ₁, …, ρₙ) and reduce.

Monolithic monitoring has complexity O(Nᵀ·M) where N is the number of rows in the
largest table, T is the number of tables and M is the size of φ. 

Assuming nothing about the implementation of the (total) function σ, N = 2ʷ,
where w is the width of the largest table.

Incremental monitoring, only needs to check the rows that have changed i.e. the
changed row and any affected by the changed row (which could be all of them). so
we get complexity O(Nᵀ⁻¹·M) where N is the number of rows in the largest table
(excluding the just-added table), and M is the size of φ

## Tools that live in this space

- p4v (*)
- bf4 (*)

Both of these tools live in this space if you exclude complex predicates like
`hit` and `miss`.

# Multiple Tables, Multiple Rows

### Grammar 

    φ ::= ⊥ | φ ⇒ φ | e < e
    e ::= t($kᵗ₁,…,$kᵗₙ) | e ⊕ e | [n]ₘ |  fst e | snd e | $kᵗᵢ
    ⊕ ∈ { +; ×; -; @; <<; (,); …}
    
Define syntactic sugar (∧, ∨, ¬, =, ≠, ≤, ≥) in the standard way.
    
### Satisfaction

Here we get full satisfaction. For simplicity we treat μ : Var → BV as a total
function. We write

    σ ⊧ φ
    iff
     ∀ μ,  ⟨μ, σ⟩ ⊧ φ

(okay now the satisfaction relation looks funky so I'll write it down)

    ⟨μ, σ⟩ ⊧ ⊥  ⇔ never
    ⟨μ, σ⟩ ⊧ φ₁ ⇒ φ₂  ⇔  NOT(⟨μ, σ⟩ ⊧ φ₁) or  ⟨μ, σ⟩ ⊧ φ₂
    ⟨μ, σ⟩ ⊧ e₁ < e₂  ⇔ 〚e₁〛⟨μ, σ⟩ < 〚e₁〛⟨μ, σ⟩
    
    〚[n]ₘ〛_ ≜ [n]ₘ
    〚σₜ($kᵗ₁,…,$kᵗₙ)〛⟨μ, σ⟩ ≜ σₜ(μ($kᵗ₁), … , μ($kᵗₙ))
    〚$kᵗᵢ〛⟨μ,σ⟩ ≜ μ($kᵗ₁)
    〚e₁ ⊕ e₁〛⟨μ, σ⟩ ≜ 〚e₁〛⟨μ, σ⟩ ⊕ 〚e₁〛⟨μ, σ⟩
    〚fst e〛⟨μ, σ⟩ ≜ fst(〚e〛⟨μ, σ⟩ )
    〚snd e〛⟨μ, σ⟩ ≜ snd(〚e〛⟨μ, σ⟩ )
    
    
## Complexity of Monitoring 

Checking σ ⊧ φ is.....? the size of the domain of the $ks (lets call this K)
times the size of φ (lets call this M) and again times the size of running σ,
which is bounded by the number of rows in the largest σₜ (we'll call this number
N). That is O(K· N · M).

Notice that K is O((2ʷ)ᵀ) where w is the width of the largest table and T is the number of tables.
Further, assuming nothing about the implementation of the (total) function σ, N = 2ʷ. So the complexity is
O((2ʷ⁺ʷᵀ) · M), or equivalently O(Nᵀ⁺¹ · M).

I'm not sure how to think about incremental monitoring here.

## Tools that live in this space

- p4v (*)
- bf4 (*)
- vera
- cpi (us)

p4v and bf4 edge into this space with complex predicates like `hit` and `miss`.

Vera lets you reason about different rows in a table (corresponding to the
number of actions in each table). Along with an (unverified?) claim that this
this sufficient to reason about all control plane states.
