# Q1461 (dm1/dm4): prove oddness via the descent, not before it

Yes: handle the even-`B` case by a **separate descent branch**.  Do **not** try to add `both_odd` as an inductive hypothesis.

The right strong-induction target is not

```text
all solutions have B odd
```

but rather

```text
there is no nontrivial primitive positive solution with this B.
```

Then both parity branches produce a smaller nontrivial primitive positive solution, contradicting the induction hypothesis.  Once the final theorem says every primitive positive solution has `B = 1`, oddness is an immediate corollary.

## Why `both_odd` as IH does not solve the problem

Suppose your induction hypothesis says “all smaller solutions have odd `B`.”  If the current solution has even `B`, the even descent below produces a smaller solution, but that smaller solution is **not guaranteed to have even denominator**.  The IH would only tell you the smaller `B'` is odd, which is not a contradiction.

So the induction predicate must be stronger:

```lean
P(B) := every primitive positive solution with denominator B is trivial
```

or equivalently

```lean
P(B) := no primitive positive solution with denominator B and B > 1 exists.
```

Then the even branch is enough, because it produces a smaller nontrivial solution.

## Even-`B` descent branch

Assume

```text
s^2 = r^4 + r^2*B^2 - B^4,
gcd(r,B)=1,
r>0,
B>0,
B even.
```

Write

```text
B = 2*C.
```

Since `gcd(r,B)=1`, `r` is odd.  Mod `2` in the equation gives `s` odd.

Let

```text
A = 2*r^2 + B^2,
U = A - 2*s,
V = A + 2*s.
```

Then

```text
U*V = A^2 - (2s)^2 = 5*B^4.
```

But in the even-`B` branch we have more divisibility:

```text
A = 2*r^2 + B^2 ≡ 2 (mod 4),
2*s ≡ 2 (mod 4),
```

so

```text
4 | U,
4 | V.
```

Define

```text
U₁ = U / 4,
V₁ = V / 4.
```

Then the product normalizes perfectly:

```text
U₁*V₁ = (U*V)/16 = 5*B^4/16 = 5*C^4.
```

Also

```text
U₁ + V₁ = r^2 + 2*C^2,
V₁ - U₁ = s.
```

So the even branch has the same `5 * fourth_power` product as the odd branch, but with `C = B/2` and the normalized factors `U₁,V₁`.

## Coprimality of the normalized factors

Prove

```text
gcd(U₁,V₁)=1.
```

A prime divisor `p` common to `U₁,V₁` divides both

```text
U₁ + V₁ = r^2 + 2*C^2,
V₁ - U₁ = s,
```

and also divides

```text
U₁*V₁ = 5*C^4.
```

Now split:

1. If `p | C`, then from `p | r^2 + 2*C^2` we get `p | r^2`, hence `p | r`, contradicting `gcd(r,B)=1` because `C | B`.

2. If `p ∤ C`, then from `p | 5*C^4` we get `p = 5`.  Since `p ∤ C`, divide the congruence by `C^2` mod `5`:

```text
(r/C)^2 ≡ -2 ≡ 3 (mod 5),
```

impossible because the nonzero square classes mod `5` are only `1` and `4`.

Therefore `gcd(U₁,V₁)=1`.

## Factorization and Pythagorean step

Apply the same coprime factorization lemma to

```text
U₁*V₁ = 5*C^4,
gcd(U₁,V₁)=1.
```

You get coprime positive `a,b` with

```text
a*b = C
```

and either

```text
U₁ = a^4,     V₁ = 5*b^4,
```

or

```text
U₁ = 5*a^4,   V₁ = b^4.
```

Consider the first case.  From the sum identity,

```text
r^2 + 2*C^2 = a^4 + 5*b^4,
C = a*b.
```

Thus

```text
r^2 = a^4 + 5*b^4 - 2*a^2*b^2
    = (a^2 - b^2)^2 + (2*b^2)^2.
```

This is a primitive Pythagorean triple with odd hypotenuse `r`.  Hence there are coprime positive `m,n`, opposite parity, with

```text
r = m^2 + n^2,
|a^2 - b^2| = m^2 - n^2,
b^2 = m*n.
```

Because `gcd(m,n)=1` and `m*n` is a square, write

```text
m = x^2,
n = y^2,
b = x*y.
```

Now there are two sign subcases.

If

```text
a^2 - b^2 = x^4 - y^4,
```

then

```text
a^2 = x^4 + x^2*y^2 - y^4.
```

So

```text
(r',B',s') = (x,y,a)
```

is a new solution of the original quartic equation.

If

```text
b^2 - a^2 = x^4 - y^4,
```

then

```text
a^2 = y^4 + x^2*y^2 - x^4,
```

so

```text
(r',B',s') = (y,x,a)
```

is a new solution.

In both cases the new denominator is smaller than the old one:

```text
B' ≤ max(x,y) ≤ x*y = b ≤ a*b = C = B/2 < B.
```

The second factorization case `U₁ = 5*a^4`, `V₁ = b^4` is the same with `a` and `b` interchanged; the even leg is `2*a^2` instead of `2*b^2`.

## The Lean theorem shape to add

This is the branch you want, not `both_odd`:

```lean
/-- Even-denominator descent for the quartic equation. -/
lemma quartic_plus_even_descent_step
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hB_even : B % 2 = 0)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    ∃ r' B' s' : ℤ,
      0 < r' ∧
      0 < B' ∧
      B' < B ∧
      Int.gcd r' B' = 1 ∧
      s' ^ 2 = r' ^ 4 + r' ^ 2 * B' ^ 2 - B' ^ 4 := by
  -- 1. Write B = 2*C.
  -- 2. Prove r and s odd.
  -- 3. Define U,V and prove 4 | U, 4 | V.
  -- 4. Set U₁=U/4, V₁=V/4 and prove U₁*V₁ = 5*C^4.
  -- 5. Prove gcd(U₁,V₁)=1 using the prime-divisor/mod-5 argument.
  -- 6. Apply the coprime factorization of 5*C^4.
  -- 7. Apply primitive Pythagorean parametrization.
  -- 8. Extract the smaller quartic solution as above.
  sorry
```

For the final proof, use two descent-step lemmas:

```lean
lemma quartic_plus_odd_descent_step ... :
  ∃ r' B' s', 0 < r' ∧ 0 < B' ∧ B' < B ∧ ...

lemma quartic_plus_even_descent_step ... :
  ∃ r' B' s', 0 < r' ∧ 0 < B' ∧ B' < B ∧ ...
```

Then strong induction is clean:

```lean
theorem quartic_plus_no_nontrivial_solution :
    ∀ r B s : ℤ,
      0 < r → 0 < B →
      Int.gcd r B = 1 →
      s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4 →
      r = 1 ∧ B = 1 := by
  -- strong induction on B.natAbs
  -- if B = 1: direct base case
  -- if B > 1 and B odd: odd_descent_step gives smaller solution, contradiction by IH
  -- if B > 1 and B even: even_descent_step gives smaller solution, contradiction by IH
  sorry
```

Strictly, the induction hypothesis should be phrased as “no nontrivial solution with smaller positive `B`.”  If your descent step only returns a smaller solution, also prove that the returned solution is nontrivial when the input has `B > 1`.  In the even branch this is automatic from the construction: if the smaller solution were `(r',B')=(1,1)`, then the Pythagorean parameters force `a=b=1` and hence `r^2=4`, contradicting `r` odd.

## Bottom line

You cannot safely make `both_odd` an assumption in the descent core unless an upstream theorem already proves the initial `B` is odd.  In the rational-point application, there is no obvious reason the initial square-root denominator must be odd.

So the robust architecture is:

```text
final descent theorem
  ├─ B odd  → old factor pair U,V
  └─ B even → normalized factor pair U/4,V/4 with B/2
```

After that theorem is proved, `B` odd is a corollary, not a prerequisite.