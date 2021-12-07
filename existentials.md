# Is the algorithm correct?

Consider the following P4 program:

```
action nop () {}
action a (_y) { y := _y }
action b (_o) { o := _o }

table t1 {
  keys = { x : exact }
  actions = { a; @defaultonly nop }
  default_action = {nop}
}

table t2 {
  keys = { y : exact }
  actions = { b; @defaultonly nop }
  default_action = {nop}
}

control {
  t1.apply();
  t2.apply();
  assert t1.action = a => t2.action = b
}
```

This becomes the following GCL program

```
assume x = key(r1);
   { assume act(r1) = a; 
     t1.action := a; 
     y := data(r1)  }
[] { assume act(r1) = nop; 
     t1.action := nop; 
     skip };

assume y = key(r2);
   { assume act(r2) = b; 
     t2.action := b; 
     o := data(r2) }
[] { assume act(r2) = nop; 
     t2.action := nop; 
     skip }

assert t1.action = a => t2.action = b
```

Computing the weakest precondition gives the following

```
φ₂ ≜ y = key(r2) ⇒ ( act(r2) = b ⇒ t1.action = a ⇒ b = b
               ∧ act(r2) = nop ⇒ t1.action = a ⇒ b = nop)
```
Notice that since b = b ⇔ ⊤ and b = nop ⇔ ⊥, φ₂ is equivalent to
```
y = key(r2) ⇒ act(r2) = nop ⇒ ¬ t1.action = a
```

Now the weakest precondition for table 1 and 2 is

```
φ ≜ x = key(r1) ⇒ (
      act(r1) = a ⇒ data(r1) = key(r2) ⇒ act(r2) = nop ⇒ ¬ a = a
    ∧ act(r1) = b ⇒ y = key(r2) ⇒ act(r2) = nop ⇒ ¬ nop = a
)
```

Now φ is equivalent to since ¬ a = a is ⊥ and ¬ nop = a is ⊤.
```
x = key(r1) ∧ act(r1) = a ∧ data(r1) = key(r2) ⇒ ¬ act(r2) = nop
```

Now with bounded quantifiaction we have

```
∀ r1 ∈ σ(1), r2 ∈ σ(2).
    ( x = key(r1) ∧
      a = act(r1) ∧
      data(r1) = key(r2)) ⇒
      act(r2) ≠ nop
```

And eliminating dataplane variable `x`, this becomes

```
∀ r1 ∈ σ(1), r2 ∈ σ(2).
    ( a = act(r1) ∧
      data(r1) = key(r2)) ⇒
      act(r2) ≠ nop
```

# Is the algorithm correct?

Consider the following P4 program:

```
action nop () {}
action a (_y) { y := _y }
action b (_o) { o := _o }

table t1 {
  keys = { x : exact }
  actions = { a; @defaultonly nop }
  default_action = {nop}
}

table t2 {
  keys = { y : exact }
  actions = { b; @defaultonly nop }
  default_action = {nop}
}

control {
  t1.apply();
  t2.apply();
  assert t1.action = a => t2.action = b
}
```

This becomes the following GCL program

```
assume x = key(r1);
   { assume act(r1) = a; 
     t1.action := a; 
     y := data(r1)  }
[] { assume act(r1) = nop; 
     t1.action := nop; 
     skip };

assume y = key(r2);
   { assume act(r2) = b; 
     t2.action := b; 
     o := data(r2) }
[] { assume act(r2) = nop; 
     t2.action := nop; 
     skip }

assert t1.action = a => t2.action = b
```

Computing the weakest precondition gives the following

```
φ₂ ≜ y = key(r2) ⇒ ( act(r2) = b ⇒ t1.action = a ⇒ b = b
               ∧ act(r2) = nop ⇒ t1.action = a ⇒ b = nop)
```
Notice that since b = b ⇔ ⊤ and b = nop ⇔ ⊥, φ₂ is equivalent to
```
y = key(r2) ⇒ act(r2) = nop ⇒ ¬ t1.action = a
```

Now the weakest precondition for table 1 and 2 is

```
φ ≜ x = key(r1) ⇒ (
      act(r1) = a ⇒ data(r1) = key(r2) ⇒ act(r2) = nop ⇒ ¬ a = a
    ∧ act(r1) = b ⇒ y = key(r2) ⇒ act(r2) = nop ⇒ ¬ nop = a
)
```

Now φ is equivalent to since ¬ a = a is ⊥ and ¬ nop = a is ⊤.
```
x = key(r1) ∧ act(r1) = a ∧ data(r1) = key(r2) ⇒ ¬ act(r2) = nop
```

Now with bounded quantifiaction we have

```
∀ r1 ∈ σ(1), r2 ∈ σ(2).
    ( x = key(r1) ∧
      a = act(r1) ∧
      data(r1) = key(r2)) ⇒
      act(r2) ≠ nop
```

And eliminating dataplane variable `x`, this becomes

```
∀ r1 ∈ σ(1), r2 ∈ σ(2).
    ( a = act(r1) ∧
      data(r1) = key(r2)) ⇒
      act(r2) ≠ nop
```

Heres the intuition that convinces me that this is what we wanted. An informal
english gloss of this formula is, for every pair of rows (r1,r2) in the join of
t1 and t2 (on r1's data and r2's key), if act(r1) = a then act(r2) cannot be
nop, i.e. act(r2) must be a.

This is actually sensible. My fears are unjustified.




This is actually sensible. My fears are unjustified.


