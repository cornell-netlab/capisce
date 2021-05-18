# Example intertwined multi-table example



Consider the following pipeline command `c`:

```
t₁.apply();
t₂.apply();
assert(t₁.action() == 1 ⇔ t₂.action() == 1); 
```

where table t₁ is defined to be the following:

```
table t₁ {
    keys = { h.x : exact; h.y : exact}
    actions = {
        {λ x → g.x := x};
        {λ y → g.y := y}
    }
}
```

and table t₂ is defined to be the following:

```
table t2 {
    keys = { g.x : exact; g.y : exact}
    actions = {
        {λ x → out.x := x};
        {λ y → out.y := y}
    }
}
```

Now this action says that whenever action 1 is hit in table 1, then action is
hit in table 2.

We instrument this program following c[?]:

```
c[?] ===

## table 1
assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.x;
{ assume ρ₁.action == 0;
  g.x := ρ₁.data.x
} [] {
  assume ρ₁.action == 1;
  g.y := ρ.data.y;
};

## table 2
assume g.x == ρ₂.key.x;
     ∧ g.y == ρ₂.key.y;
{ assume ρ₂.action == 0;
  out.x := ρ₂.data.x
} [] {
  assume ρ₂.action == 1;
  out.y := ρ₂.data.x
};

assert(ρ₁.action == 1 ⇔ ρ₂.action == 1)
```


Now we compute the weakest precondition:

```
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y;
{ assume ρ₁.action == 0;
  g.x := ρ₁.data.x
} [] {
  assume ρ₁.action == 1;
  g.y := ρ.data.y;
};
assume g.x == ρ₂.key.x;
     ∧ g.y == ρ₂.key.y;
{ assume ρ₂.action == 0;
  out.x := ρ₂.data.x
} [] {
  assume ρ₂.action == 1;
  out.y := ρ₂.data.x
}, ρ₁.action == 1 ⇔ ρ₂.action == 1)
===
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y;
{ assume ρ₁.action == 0;
  g.x := ρ₁.data.x
} [] {
  assume ρ₁.action == 1;
  g.y := ρ.data.y;
}, wp(assume g.x == ρ₂.key.x
           ∧ g.y == ρ₂.key.y;
       { assume ρ₂.action == 0;
         out.x := ρ₂.data.x
       } [] {
         assume ρ₂.action == 1;
         out.y := ρ₂.data.x
       }, ρ₁.action == 1 ⇔ ρ₂.action == 1))
===
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y;
{ assume ρ₁.action == 0;
  g.x := ρ₁.data.x
} [] {
  assume ρ₁.action == 1;
  g.y := ρ₁.data.y;
}, wp(assume g.x == ρ₂.key.x
           ∧ g.y == ρ₂.key.y,
      wp(assume ρ₂.action == 0;
         out.x := ρ₂.data.x,
         ρ₁.action == 1 ⇔ ρ₂.action == 1)
      ∧ wp(assume ρ₂.action == 1;
           out.y := ρ₂.data.x,
           ρ₁.action == 1 ⇔ ρ₂.action == 1)))
===
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y;
{ assume ρ₁.action == 0;
  g.x := ρ₁.data.x
} [] {
  assume ρ₁.action == 1;
  g.y := ρ₁.data.y;
}, wp(assume g.x == ρ₂.key.x
       ∧ g.y == ρ₂.key.y,
        (ρ₂.action == 0 ⇒
         ρ₁.action == 1 ⇔ ρ₂.action == 1)
      ∧ (ρ₂.action == 1 ⇒
         ρ₁.action == 1 ⇔ ρ₂.action == 1))))
===
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y;
{ assume ρ₁.action == 0;
  g.x := ρ₁.data.x
} [] {
  assume ρ₁.action == 1;
  g.y := ρ₁.data.y;
}, 
   (g.x == ρ₂.key.x ∧ g.y == ρ₂.key.y ⇒
    (ρ₂.action == 0 ⇒
     ρ₁.action == 1 ⇔ ρ₂.action == 1)
    ∧ (ρ₂.action == 1 ⇒
       ρ₁.action == 1 ⇔ ρ₂.action == 1)))
===
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y,
wp(
{ assume ρ₁.action == 0;
  g.x := ρ₁.data.x
} [] {
  assume ρ₁.action == 1;
  g.y := ρ₁.data.y;
}, 
   (g.x == ρ₂.key.x ∧ g.y == ρ₂.key.y ⇒
    (ρ₂.action == 0 ⇒
     ρ₁.action == 1 ⇔ ρ₂.action == 1)
    ∧ (ρ₂.action == 1 ⇒
       ρ₁.action == 1 ⇔ ρ₂.action == 1)))
)
===
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y,
wp(assume ρ₁.action == 0;
   g.x := ρ₁.data.x,
   (g.x == ρ₂.key.x ∧ g.y == ρ₂.key.y ⇒
    (ρ₂.action == 0 ⇒
     ρ₁.action == 1 ⇔ ρ₂.action == 1)
    ∧ (ρ₂.action == 1 ⇒
       ρ₁.action == 1 ⇔ ρ₂.action == 1)))
∧
wp(assume ρ₁.action == 1;
   g.y := ρ₁.data.y,
   (g.x == ρ₂.key.x ∧ g.y == ρ₂.key.y ⇒
    (ρ₂.action == 0 ⇒
     ρ₁.action == 1 ⇔ ρ₂.action == 1)
    ∧ (ρ₂.action == 1 ⇒
       ρ₁.action == 1 ⇔ ρ₂.action == 1)))   
)
===
wp(assume h.x == ρ₁.key.x;
     ∧ h.y == ρ₁.key.y,
(ρ₁.action == 0 ⇒
 (ρ₁.data.x == ρ₂.key.x ∧ g.y == ρ₂.key.y ⇒
  (ρ₂.action == 0 ⇒
   ρ₁.action == 1 ⇔ ρ₂.action == 1)
  ∧ (ρ₂.action == 1 ⇒
     ρ₁.action == 1 ⇔ ρ₂.action == 1)))
∧
(ρ₁.action == 1 ⇒
 (g.x == ρ₂.key.x ∧ ρ₁.data.y == ρ₂.key.y ⇒
  (ρ₂.action == 0 ⇒
   ρ₁.action == 1 ⇔ ρ₂.action == 1)
  ∧ (ρ₂.action == 1 ⇒
     ρ₁.action == 1 ⇔ ρ₂.action == 1)))
)
===
h.x == ρ₁.key.x ∧ h.y == ρ₁.key.y ⇒
((ρ₁.action == 0 ⇒
  (ρ₁.data.x == ρ₂.key.x ∧ g.y == ρ₂.key.y ⇒
   (ρ₂.action == 0 ⇒
    ρ₁.action == 1 ⇔ ρ₂.action == 1)
   ∧ (ρ₂.action == 1 ⇒
      ρ₁.action == 1 ⇔ ρ₂.action == 1)))
 ∧
 (ρ₁.action == 1 ⇒
  (g.x == ρ₂.key.x ∧ ρ₁.data.y == ρ₂.key.y ⇒
   (ρ₂.action == 0 ⇒
    ρ₁.action == 1 ⇔ ρ₂.action == 1)
   ∧ (ρ₂.action == 1 ⇒
      ρ₁.action == 1 ⇔ ρ₂.action == 1))))
```

And now we want to pass this to Princess to eliminate the quantifiers, which we do:

```
(set-logic UFBV)

(define-sort BV () (_ BitVec 32))
(declare-const rokx BV)
(declare-const roky BV)
(declare-const roa (_ BitVec 1))
(declare-const rody BV)
(declare-const rodx BV)
(declare-const rtkx BV)
(declare-const rtky BV)
(declare-const rta (_ BitVec 1))

(simplify (forall ((hx BV) (hy BV) (gx BV) (gy BV))
  (=> (= hx rokx) (= hy roky)
      (and
        (=> (= roa #b0)
            (=> (= rodx rtkx) (= gy rtky)
                (and (=> (= rta #b0) (= (= roa #b1) (= rta #b1)))
                     (=> (= rta #b1) (= (= roa #b1) (= rta #b1))))))


        (=> (= roa #b1)
            (=> (= gx rtkx) (= rody rtky)
                (and (=> (= rta #b0) (= (= roa #b1) (= rta #b1)))
                     (=> (= rta #b1) (= (= roa #b1) (= rta #b1))))))))))

```

The reported result is

```
(or (or (and (= rta (_ bv1 1)) (= roa (_ bv1 1))) (and (and (= rta (_ bv1 1)) (= roa (_ bv0 1))) (not (= rtkx rodx)))) (and (= rta (_ bv0 1)) (or (not (= rtky rody)) (not (= roa (_ bv1 1))))))
```

Which is 

```
(ρ₂.action = 1 ∧ ρ₁.action = 1)
∨
(ρ₂.action = 1 ∧ ρ₁.action = 0 ∧ ρ₂.key.x ≠ ρ₁.data x)
∨
(ρ₂.action = 0 ∧ (ρ₂.key.y ≠ ρ₁.data.y ∨ ρ₁.action ≠ 1))
```

which is equivalent to 

```
(ρ₂.action = 1 ∧ ρ₁.action = 1)
∨
(ρ₂.action = 1 ∧ ρ₁.action = 0 ∧ ρ₂.key.x ≠ ρ₁.data x)
∨
(ρ₂.action = 0 ∧ (ρ₂.key.y ≠ ρ₁.data.y ∧ ρ₁.action = 1 ∨ ρ₁.action ≠ 1))
===

(ρ₂.action = 1 ∧ ρ₁.action = 1)
∨
(ρ₂.action = 1 ∧ ρ₁.action = 0 ∧ ρ₂.key.x ≠ ρ₁.data x)
∨
(ρ₂.action = 0 ∧ ρ₂.key.y ≠ ρ₁.data.y ∧ ρ₁.action = 1)
∨
(ρ₂.action ∧ ρ₁.action ≠ 1)
```

There are 4 cases; let's examine each in turn.

For a pair of rows (ρ₁, ρ₂), one of the following must hold. lets examine each in turn.

1. ρ₂.action = 1 ∧ ρ₁.action = 1

This is great! then packets that hit both of these rows will both have hit both of the rows!.

2. (ρ₂.action = 1 ∧ ρ₁.action = 0 ∧ ρ₂.key.x ≠ ρ₁.data.x)

In this case, action 0 is executed in table 1, and action 1 is executed in
table 2. It's also the case that the action data assigned in table 1 doesn't
match the key in ρ₂. i.e. the following code snipped is executed. 

```
assume ρ₁.data.x ≠ ρ₂.key.x
h.x := ρ₁.data.x
assume h.x = ρ₂.key.x ## always violated!
h.y := ρ₂.data.x
```

This amounts to ``dead code''. There is no packet that will traverse both ρ₁ and
ρ₂.

3. (ρ₂.action = 0 ∧ ρ₂.key.y ≠ ρ₁.data.y ∧ ρ₁.action = 1)

This is symmetric to case 2.

4. (ρ₂.action = 0 ∧ ρ₁.action = 0)

Here both actions are 0, so they're equivalent.

-------------------------------------------------------

This ensures that the action requirements are satisfied. I have little intuition
to validate whether this is the weakest condition.
