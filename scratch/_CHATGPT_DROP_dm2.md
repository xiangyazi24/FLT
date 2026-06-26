# Q814 (dm2): bypassing the even-cofactor separability branch

## Bottom line

Yes: for now, the right engineering move is to **bypass this branch by isolating it as one local theorem / axiom**, then close the other cases.

I would **not** try to prove

```text
C'(x) ≠ 0
```

by expanding

```text
C = preΨ(m+2)^2 · preΨ(m+5) - preΨ(m+1) · preΨ(m+4)^2.
```

That derivative expansion is exactly the wrong abstraction level.  It forces you into derivative identities for several neighboring EDS values, and the proof will likely grow into a differentiated EDS theory.  That is much larger than the local sub-problem deserves.

I would also **not** switch to the resultant formula right now.  Mathematically, yes, the global identity

```text
Res(preΨₙ, preΨₙ') = unit · Δ^A · n^B
```

would prove separability at once.  But formalizing that formula is much harder than the separability theorem itself.  It would bypass the cofactor branch only by replacing it with a deep global theorem.

The clean temporary solution is:

```text
finish the 3 EDS cases that are already tractable,
leave exactly one named cofactor-separability theorem as `sorry` / axiom,
and make the main proof depend on that theorem.
```

That keeps the remaining trust debt small, named, and mathematically meaningful.

---

## What the cofactor branch really means

Set

```text
k = m + 3.
```

Then the cofactor is

```text
C_k = preΨ(k-1)^2 · preΨ(k+2) - preΨ(k-2) · preΨ(k+1)^2.
```

In the indexing from the question this is

```text
C = preΨ(m+2)^2 · preΨ(m+5)
      - preΨ(m+1) · preΨ(m+4)^2.
```

The even recurrence has the shape

```text
preΨ(2k) = preΨ(k) · C_k.
```

So the difficult branch is:

```text
preΨ(k)(x) ≠ 0,
C_k(x) = 0.
```

Geometrically, this is the case where the point is not killed by `[k]`, but its `[k]`-multiple is killed by `[2]`.  In other words, the root lies in the new `2`-layer of the `2k`-torsion.

Since the final theorem assumes

```text
(2k : K) ≠ 0,
```

we are in characteristic not dividing `2k`.  Thus `[k]` is étale, and `E[2]` is étale.  The pullback

```text
[k]⁻¹(E[2] \ {O})
```

is reduced.  The polynomial `C_k` cuts out this reduced divisor on the x-line, away from the factor `preΨ(k)`.  Therefore its roots in this branch are simple.

That is the conceptual proof of

```text
C_k(x) = 0,
preΨ(k)(x) ≠ 0
    ⇒ C_k'(x) ≠ 0.
```

But formalizing this directly requires either the group-scheme / étale story or a carefully packaged dual-number argument.  It is not a small EDS manipulation.

---

## Why the dual-number idea is valid but not a small local patch

The dual-number proof would go like this.

If

```text
C_k(x) = 0
C_k'(x) = 0,
```

then in `K[ε]` one has

```text
C_k(x + ε) = 0.
```

Since

```text
preΨ(k)(x) ≠ 0,
```

the value `preΨ(k)(x + ε)` is a unit in `K[ε]`.  Therefore the recurrence

```text
preΨ(2k) = preΨ(k) · C_k
```

implies

```text
preΨ(2k)(x + ε) = 0
```

while the `k`-factor remains invertible.

Geometrically, this says there is a nontrivial infinitesimal deformation staying in the new `2`-layer of `E[2k]`.  But when `(2k : K) ≠ 0`, the torsion scheme `E[2k]` is étale, so it has no nonzero tangent vectors.  Contradiction.

This is a very good eventual proof.  But in Lean it is not just a one-line replacement for the derivative calculation.  You need enough infrastructure to say:

```text
polynomial double root
  ⇒ dual-number infinitesimal root
  ⇒ infinitesimal torsion point
  ⇒ impossible by étaleness of `[2k]`.
```

So the dual-number proof is a principled replacement, but not the quickest way to unblock the EDS proof.

---

## Recommended temporary theorem

Do not leave an anonymous `sorry` buried deep in the product-rule branch.  Create one named theorem whose statement matches exactly the missing branch.

For a Nat-indexed version, use something like:

```lean
noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/--
The even cofactor appearing in
`preΨ' (2 * (m + 3)) = preΨ' (m + 3) * evenCofactor m`,
up to whatever normalization is used in the local file.
-/
def evenCofactorNat (m : ℕ) : Polynomial K :=
  (W.preΨ' (m + 2)) ^ 2 * W.preΨ' (m + 5)
    - W.preΨ' (m + 1) * (W.preΨ' (m + 4)) ^ 2

/--
Temporary Q814 bridge lemma.

Geometric meaning: away from the `preΨ' (m + 3)` factor, the even cofactor
cuts out the new `2`-layer of `(2 * (m + 3))`-torsion.  Since `(2 * (m + 3))`
is invertible in `K`, that layer is reduced, so the cofactor has simple roots.
-/
theorem evenCofactorNat_derivative_eval_ne_zero_of_eval_eq_zero
    [W.IsElliptic] {m : ℕ} {x : K}
    (hn : ((2 * (m + 3) : ℕ) : K) ≠ 0)
    (hC : (W.evenCofactorNat m).eval x = 0)
    (hmiddle : (W.preΨ' (m + 3)).eval x ≠ 0) :
    (derivative (W.evenCofactorNat m)).eval x ≠ 0 := by
  -- TODO(Q814): prove using the dual-number / étale `[2 * (m + 3)]` argument,
  -- or later replace by a direct cofactor separability theorem.
  sorry

end WeierstrassCurve
```

If the current recurrence is integer-indexed, use the same theorem with

```lean
def evenCofactorInt (m : ℤ) : Polynomial K :=
  (W.preΨ (m + 2)) ^ 2 * W.preΨ (m + 5)
    - W.preΨ (m + 1) * (W.preΨ (m + 4)) ^ 2
```

and a hypothesis shaped like

```lean
(((2 : ℤ) * (m + 3) : ℤ) : K) ≠ 0
```

or whatever cast form is easiest in the local file.

The Nat-indexed version is usually easier if all indices in this cofactor are already nonnegative.

---

## How to use the bridge lemma in the product-rule branch

In the cofactor-root branch, the product is

```text
preΨ(2k) = preΨ(k) · C_k.
```

At `x`, you know

```text
preΨ(k)(x) ≠ 0,
C_k(x) = 0,
C_k'(x) ≠ 0.
```

Then the product derivative is immediate:

```text
(preΨ(k) · C_k)'(x)
  = preΨ(k)'(x) · C_k(x) + preΨ(k)(x) · C_k'(x)
  = preΨ(k)(x) · C_k'(x)
  ≠ 0.
```

In Lean, the local shape is:

```lean
have hCderiv : (derivative (W.evenCofactorNat m)).eval x ≠ 0 :=
  W.evenCofactorNat_derivative_eval_ne_zero_of_eval_eq_zero
    hn hC hmiddle

have hprod_deriv :
    (derivative (W.preΨ' (m + 3) * W.evenCofactorNat m)).eval x ≠ 0 := by
  rw [derivative_mul]
  simp [eval_add, eval_mul, hC]
  exact mul_ne_zero hmiddle hCderiv
```

The actual `simp` line may need local normalization lemmas, but the proof is just the product rule.

---

## Why this is better than an axiom for the whole theorem

Avoid an axiom like:

```lean
axiom preΨ'_separable_of_natCast_ne_zero : ...
```

That would swallow the whole theorem and make the rest of the EDS proof irrelevant.

Instead, the Q814 bridge theorem isolates only the genuinely hard missing branch:

```text
root of the even cofactor, away from the middle factor
  ⇒ simple root of the even cofactor.
```

Then the final separability proof still proves all the tractable cases:

1. roots coming from the middle factor `preΨ(k)`,
2. roots handled by adjacent nonvanishing,
3. odd-index recurrence cases,
4. product-rule cleanup for the even recurrence.

Only the reducedness of the new `2`-layer remains trusted.

That is the right size for the temporary axiom.

---

## Later replacement plan

When replacing the `sorry`, do **not** start by expanding `C_k'`.

The durable proof should be one of these two forms.

### Option A: local étaleness / dual numbers

Prove a general lemma:

```text
if (r : K) ≠ 0, then E[r] has no nontrivial dual-number tangent vectors.
```

Then specialize to `r = 2 * (m + 3)`.  The cofactor branch gives an infinitesimal point in the new `2`-layer, contradicting étaleness.

This is conceptually strongest and will probably help elsewhere.

### Option B: direct cofactor reducedness

Prove directly that the polynomial cutting out

```text
[k]⁻¹(E[2] \ {O})
```

on the x-line is squarefree when `(2k : K) ≠ 0`.

This is closer to the current EDS file, but still should use the geometry of `[k]` and `E[2]`, not a hand-expanded derivative of the five neighboring `preΨ` values.

---

## Final recommendation

For the current proof, bypass the case by introducing one theorem:

```lean
evenCofactorNat_derivative_eval_ne_zero_of_eval_eq_zero
```

or the integer-indexed equivalent.

Use it only in the branch

```text
C(x) = 0,
preΨ(m+3)(x) ≠ 0.
```

Then finish the other three branches.  This is mathematically honest, keeps the proof architecture intact, and avoids sinking time into a brittle derivative expansion or a very hard resultant formula.
