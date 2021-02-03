# Problem with Generated Conditions

Consider an example table:
```
table t
  keys = z
  action = λ d. x := d
  default = x := 4
```
Applied in the following control block:
```
control {
    t.apply();
    assert x ≠ z
}
```

What condition can we imagine for the control plane such that this never
occurs?
```
∃ ρ ∈ t. ρ.key[0] = 4
 ∧ ∀ ρ ∈ t. ρ.key[0] ≠ ρ.data[0]
```

However, there is only one key and one action datum so we will omit the index
moving forward, i.e. we can write the condition as
```
∃ ρ ∈ t. ρ.key = 4
 ∧ ∀ ρ ∈ t. ρ.key ≠ ρ.data
```

As an example the instance
```
if (z = 4) {
   x := 3
} else {
   x := 4
}
assert x ≠ z ## never triggered.
```
Never triggers the assert statement.

So in our setting, this should be equivalent to or stronger than the condition
that we compute in the dataplane. The first step is to instrument the program,
which we do as follows:
```
{ assume ρ.key = z;
  x := ρ.data
} [] {
  assume ρ.key ≠ z;
  x := 4
}
assert x ≠ z
```
And then we compute the weakest precondition of the above program w.r.t `⊤`, which gives

```
(ρ.key = z ⇒ ρ.data ≠ z)
∧ (ρ.key ≠ z ⇒ z ≠ 4)
```

The question is, how do we interpret this condition? Currently its reasoning
about a bitvector variable `z` and a record `ρ` of type
```
type row = 
  { key : 2ⁿ;
    data : 2ⁿ;
    act : 2*
  }
```

And these are meant to stand in for an arbitrary row in the table.
So the condition we really mean is
```
∀ z. ∀ t ⊆ row. ∀ ρ ∈ t.
    (ρ.key = z ⇒ ρ.data ≠ z)
    ∧ (ρ.key ≠ z ⇒ z ≠ 4)
```

But this is not correct! Consider the following model `m`:
```
{t ↦ [{key = 4; data = 3; act = 0};
       {key = 3; data = 4; act = 0}];
 ρ ↦ {key = 3; data = 4; act = 0}
 z ↦ 4
}
```

This corresponds to the correct program
```
if (z = 4) {
  x := 3
} else if (z = 3) {
  x := 4
} else {
  x := 4
}
assert x ≠ z
```
which triggers no assertion error.

However this behavior _is not_ allowed by the computed condition
``````
((ρ.key = z ⇒ ρ.data ≠ z) ∧ (ρ.key ≠ z ⇒ z ≠ 4))[m]
= (3 = 4 ⇒ 4 ≠ 4) ∧ (3 ≠ 4 ⇒ 4 ≠ 4)
= ⊤ ∧ ⊥
= ⊥
``````

While it is allowed by the handwritten condition:
```
m ⊧ ∃ ρ ∈ t. ρ.key = 4       # with ρ = m[t][0]
m ⊧ ∀ ρ ∈ t. ρ.key ≠ ρ.data  # 3 ≠ 4 and 4 ≠ 3
```

# Solution?

I don't know what the solution is here. Here's the best idea I have so far.

We need to change the way that we generate VCs. Perhaps we need to use more
general assumptions.. Here I use `havoc ρ`, which picks an arbitrary value for `ρ`
and introduce universal quantification into the language of boolean expressions.
```
{ havoc ρ;
  assume ρ.key = z;
  x := ρ.data
} [] {
  assume ∀ ρ ∈ t. ρ.key ≠ z;
  x := 4
}
assert x ≠ z
```

which would give us the condition 
```
∀ z . ∀ t ⊆ row.
    (∀ ρ ∈ t. ρ.key = z ⇒ z ≠ ρ.data)
  ∧ ((∀ ρ ∈ t. ρ.key ≠ z) ⇒ z ≠ 4 )
==
∀ z. ∀ t ⊆ row.
    (∀ ρ ∈ t. ρ.key = z ⇒ z ≠ ρ.data)
  ∧ ((∃ ρ ∈ t. ρ.key = z) ∨ z ≠ 4 )
```

Which returns us to the problem of quantifier elimination for `z`.
