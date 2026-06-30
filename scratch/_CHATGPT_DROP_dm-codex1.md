# Q2533: four-square AP versus `not_fermat_42`

## Verdict

I would **not** try to prove `FourSquaresAPToFermat42Bridge` by a one-line algebraic construction of

```lean
a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2
```

from a nonconstant arithmetic progression

```lean
w^2, x^2, y^2, z^2.
```

The honest situation is:

* The AP hypotheses give several clean ring identities.
* The most useful identities are factor/product identities such as
  `(x*y - w*z) * (x*y + w*z) = 2 * (y^2 - x^2)^2`.
* Those identities do **not** directly say that either factor is a square, nor do they directly give a sum of two fourth powers.
* Turning them into a contradiction requires the classical Fermat descent for four squares in arithmetic progression, with primitive normalization, parity, gcd/factor extraction, and a smaller counterexample.

So the best Lean architecture is:

1. Prove and keep the ring identities below as local lemmas.
2. Do **not** pretend that `FourSquaresAPToFermat42Bridge` has a constructive polynomial substitution.
3. Add/use a classical descent theorem whose conclusion is directly
   `FourSqAPConst w x y z`.
4. If the existing file really needs the `FourSquaresAPToFermat42Bridge` Prop, close it **vacuously** from the no-four-square-AP theorem.

In other words, the correct mathematical bridge is not

```lean
nonconstant four-square AP → explicit Fermat42 solution
```

but rather

```lean
Fermat descent / no-four-square-AP → no nonconstant four-square AP
```

and then the existential bridge is only an ex-falso wrapper.

---

## Notation

Given

```lean
hAP : IntFourSqAP w x y z
```

the common difference can be taken as

```lean
Δ = y ^ 2 - x ^ 2
```

and the AP hypotheses imply

```text
x^2 - w^2 = Δ,
y^2 - x^2 = Δ,
z^2 - y^2 = Δ.
```

Thus

```text
x^2 = w^2 + Δ,
y^2 = w^2 + 2Δ,
z^2 = w^2 + 3Δ.
```

These are the identities that should drive the Lean proof scripts.

---

## Ring identities worth adding

The following snippets use only the local definitions from the question plus `nlinarith`/`ring`.

```lean
import Mathlib

/-- The first three squares in a four-square AP form a symmetric three-square AP. -/
theorem IntFourSqAP_left_three
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    w ^ 2 + y ^ 2 = 2 * x ^ 2 := by
  nlinarith [h.1]

/-- The last three squares in a four-square AP form a symmetric three-square AP. -/
theorem IntFourSqAP_right_three
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    x ^ 2 + z ^ 2 = 2 * y ^ 2 := by
  nlinarith [h.2]

/-- The outer-pair and middle-pair sums agree. -/
theorem IntFourSqAP_outer_sum
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    w ^ 2 + z ^ 2 = x ^ 2 + y ^ 2 := by
  nlinarith [h.1, h.2]

/-- The full outer difference is three times the common difference. -/
theorem IntFourSqAP_outer_diff
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    z ^ 2 - w ^ 2 = 3 * (y ^ 2 - x ^ 2) := by
  nlinarith [h.1, h.2]
```

The main useful factor identity is the `xy ± wz` one:

```lean
import Mathlib

/--
The clean square-product identity coming from four squares in AP.
This is often the first identity used in the descent route.
-/
theorem IntFourSqAP_xy_wz_factor
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    (x * y - w * z) * (x * y + w * z) =
      2 * (y ^ 2 - x ^ 2) ^ 2 := by
  let Δ : ℤ := y ^ 2 - x ^ 2
  have hx2 : x ^ 2 = w ^ 2 + Δ := by
    dsimp [Δ]
    nlinarith [h.1]
  have hy2 : y ^ 2 = w ^ 2 + 2 * Δ := by
    dsimp [Δ]
    nlinarith [h.1]
  have hz2 : z ^ 2 = w ^ 2 + 3 * Δ := by
    dsimp [Δ]
    nlinarith [h.1, h.2]
  calc
    (x * y - w * z) * (x * y + w * z)
        = x ^ 2 * y ^ 2 - w ^ 2 * z ^ 2 := by ring
    _ = (w ^ 2 + Δ) * (w ^ 2 + 2 * Δ)
          - w ^ 2 * (w ^ 2 + 3 * Δ) := by
        rw [hx2, hy2, hz2]
    _ = 2 * Δ ^ 2 := by ring
    _ = 2 * (y ^ 2 - x ^ 2) ^ 2 := by rfl
```

Two related identities are also useful for auditing candidate transformations:

```lean
import Mathlib

/-- Another factor identity: `xz ± wy`. -/
theorem IntFourSqAP_xz_wy_factor
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    (x * z - w * y) * (x * z + w * y) =
      (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
  let Δ : ℤ := y ^ 2 - x ^ 2
  have hx2 : x ^ 2 = w ^ 2 + Δ := by
    dsimp [Δ]
    nlinarith [h.1]
  have hy2 : y ^ 2 = w ^ 2 + 2 * Δ := by
    dsimp [Δ]
    nlinarith [h.1]
  have hz2 : z ^ 2 = w ^ 2 + 3 * Δ := by
    dsimp [Δ]
    nlinarith [h.1, h.2]
  calc
    (x * z - w * y) * (x * z + w * y)
        = x ^ 2 * z ^ 2 - w ^ 2 * y ^ 2 := by ring
    _ = (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
        rw [hx2, hy2, hz2]
        ring

/-- Another factor identity: `yz ± wx`. -/
theorem IntFourSqAP_yz_wx_factor
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    (y * z - w * x) * (y * z + w * x) =
      2 * (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
  let Δ : ℤ := y ^ 2 - x ^ 2
  have hx2 : x ^ 2 = w ^ 2 + Δ := by
    dsimp [Δ]
    nlinarith [h.1]
  have hy2 : y ^ 2 = w ^ 2 + 2 * Δ := by
    dsimp [Δ]
    nlinarith [h.1]
  have hz2 : z ^ 2 = w ^ 2 + 3 * Δ := by
    dsimp [Δ]
    nlinarith [h.1, h.2]
  calc
    (y * z - w * x) * (y * z + w * x)
        = y ^ 2 * z ^ 2 - w ^ 2 * x ^ 2 := by ring
    _ = 2 * (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
        rw [hx2, hy2, hz2]
        ring
```

These identities are sign-robust: no positivity assumptions are needed.

---

## Nonconstant means the common difference is nonzero

This is a useful small lemma. It is often better than repeatedly unpacking `¬ FourSqAPConst`.

```lean
import Mathlib

/-- If the common difference is zero, the AP is constant as squares. -/
theorem FourSqAPConst_of_IntFourSqAP_commonDiff_zero
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hΔ : y ^ 2 - x ^ 2 = 0) :
    FourSqAPConst w x y z := by
  have hwx : w ^ 2 = x ^ 2 := by nlinarith [hAP.1, hΔ]
  have hxy : x ^ 2 = y ^ 2 := by nlinarith [hΔ]
  have hyz : y ^ 2 = z ^ 2 := by nlinarith [hAP.2, hΔ]
  exact ⟨hwx, hxy, hyz⟩

/-- In a nonconstant four-square AP, the common difference is nonzero. -/
theorem IntFourSqAP_commonDiff_ne_zero_of_nonconst
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnon : ¬ FourSqAPConst w x y z) :
    y ^ 2 - x ^ 2 ≠ 0 := by
  intro hΔ
  exact hnon (FourSqAPConst_of_IntFourSqAP_commonDiff_zero hAP hΔ)
```

---

## Why the tempting candidates do not give `a^4 + b^4 = c^2`

The most tempting direct candidate is to use the two visible differences

```text
z^2 - w^2 = 3Δ,
y^2 - x^2 = Δ.
```

But then

```text
(z^2 - w^2)^4 + (y^2 - x^2)^4 = 82 * Δ^4,
```

not a square identity.

Lean form:

```lean
import Mathlib

/-- The obvious outer/middle-difference candidate gives coefficient `82`, not a square. -/
theorem IntFourSqAP_outer_middle_candidate_value
    {w x y z : ℤ}
    (h : IntFourSqAP w x y z) :
    (z ^ 2 - w ^ 2) ^ 4 + (y ^ 2 - x ^ 2) ^ 4 =
      82 * (y ^ 2 - x ^ 2) ^ 4 := by
  have hz : z ^ 2 - w ^ 2 = 3 * (y ^ 2 - x ^ 2) :=
    IntFourSqAP_outer_diff h
  rw [hz]
  ring
```

Equivalently, using products such as

```text
(z - w)(z + w) = z^2 - w^2,
(y - x)(y + x) = y^2 - x^2
```

does not change the obstruction: it is still the same `3Δ` and `Δ` pair.

The identity

```text
(x*y - w*z)(x*y + w*z) = 2Δ^2
```

is the useful one, but it is a **product** identity. To turn it into square roots one needs primitive normalization, gcd control, parity control, and then a descent/extraction lemma. That is exactly the classical Fermat four-squares descent, not a local ring calculation.

---

## Recommended theorem architecture

Use the following theorem as the real mathematical frontier/input:

```lean
import Mathlib

/-- Classical Fermat descent: four integral squares in AP are constant. -/
theorem fourSqAP_const_of_IntFourSqAP
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    FourSqAPConst w x y z := by
  -- This is the genuine Fermat descent theorem.
  -- It should not be replaced by a fake one-step `a^4 + b^4 = c^2` construction.
  sorry
```

If you specifically want to route through Mathlib's `not_fermat_42`, the missing theorem should be stated explicitly as a descent theorem:

```lean
import Mathlib

/--
Classical descent package connecting Mathlib's Fermat-4 theorem to no four-square AP.
This is not just a substitution lemma; it includes the primitive/gcd/parity/descent work.
-/
theorem fourSqAP_const_of_not_fermat_42
    (hF42 : ∀ {a b c : ℤ}, a ≠ 0 → b ≠ 0 → ¬ a ^ 4 + b ^ 4 = c ^ 2)
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    FourSqAPConst w x y z := by
  -- Classical descent proof goes here.
  -- The ring identities above are useful support lemmas, but are not sufficient alone.
  sorry
```

Then your existing bridge Prop can be closed as a vacuous wrapper:

```lean
import Mathlib

/--
If no nonconstant four-square AP exists, the existential Fermat42 bridge is vacuous.
This is the honest way to prove the current Prop-shaped bridge.
-/
theorem FourSquaresAPToFermat42Bridge_of_no_fourSqAP
    (hNoAP : ∀ {w x y z : ℤ},
      IntFourSqAP w x y z → FourSqAPConst w x y z) :
    FourSquaresAPToFermat42Bridge := by
  intro w x y z hAP hnon
  exact False.elim (hnon (hNoAP hAP))
```

If the file already imports Mathlib's theorem as

```lean
not_fermat_42 : a ≠ 0 → b ≠ 0 → ¬ a ^ 4 + b ^ 4 = c ^ 2
```

then the final shape should be:

```lean
import Mathlib

theorem FourSquaresAPToFermat42Bridge_of_fermat_descent :
    FourSquaresAPToFermat42Bridge := by
  apply FourSquaresAPToFermat42Bridge_of_no_fourSqAP
  intro w x y z hAP
  exact fourSqAP_const_of_not_fermat_42
    (fun {a b c} ha hb => not_fermat_42 ha hb)
    hAP
```

Depending on the actual implicit arguments of `not_fermat_42` in your Mathlib version, the last line may need one of these equivalent spellings:

```lean
  exact fourSqAP_const_of_not_fermat_42
    (fun {a b c : ℤ} ha hb => not_fermat_42 (a := a) (b := b) (c := c) ha hb)
    hAP
```

or, if `not_fermat_42` is already specialized to integers with explicit variables in context:

```lean
  exact fourSqAP_const_of_not_fermat_42
    (by
      intro a b c ha hb
      exact not_fermat_42 ha hb)
    hAP
```

---

## Minimal descent-frontier statement if you want to formalize it internally

A good internal frontier is a strict descent step on a primitive, parity-normalized counterexample. For example:

```lean
import Mathlib

def fourSqAPHeight (w x y z : ℤ) : ℕ :=
  w.natAbs + x.natAbs + y.natAbs + z.natAbs

/--
Primitive/parity-normalized Fermat descent step.
The exact construction of `w' x' y' z'` is the hard classical part.
-/
theorem primitive_fourSqAP_descent_step
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnon : ¬ FourSqAPConst w x y z)
    -- Replace these by the primitive/parity predicates already present in the file.
    (hprim : True)
    (hparity : True) :
    ∃ w' x' y' z' : ℤ,
      IntFourSqAP w' x' y' z' ∧
      ¬ FourSqAPConst w' x' y' z' ∧
      fourSqAPHeight w' x' y' z' < fourSqAPHeight w x y z := by
  -- Hard descent construction.
  -- The factor identity `(xy-wz)(xy+wz)=2Δ^2` is one of the inputs.
  sorry
```

Then the global no-AP theorem is a well-founded/minimal-counterexample wrapper around this descent step, plus normalization by root gcd and signs/parity.

This is the honest shape: the algebraic lemmas are small and buildable, while the descent theorem is the genuine mathematical frontier. The current existential bridge should not be used as if it contained a direct formula for `a,b,c`.
