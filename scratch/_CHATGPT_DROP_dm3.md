# Q797 (dm3): defining the missing y-coordinate numerator `ωₙ` / `Ωₙ`

## Bottom line

Do **not** define `ωₙ` merely as an arbitrary root of the cleared curve-equation quadratic.  In Lean this gives the wrong object: the root is not canonical in the polynomial ring, uniqueness is false in the cases where it matters most, and a `Classical.choose` definition will not have usable computation, map/naturality, or compatibility with the division-polynomial recurrences.

The best first definition is exactly your cleaner object:

```text
Qₙ := ψ₂ₙ / ψₙ.
```

This is already supported by Mathlib’s EDS infrastructure.  The helper sequence `complEDS₂` is specifically the quotient witnessing

```text
normEDS k · complEDS₂ k = normEDS (2*k).
```

Since Mathlib defines

```lean
W.ψ n = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n,
```

you can define

```text
Qₙ := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
```

and get the theorem

```text
ψₙ · Qₙ = ψ₂ₙ
```

by `simpa [WeierstrassCurve.ψ] using normEDS_mul_complEDS₂ ...`.

Then define the division-by-2-free y-numerator as

```text
twoωₙ := Qₙ - ψₙ · (a₁φₙ + a₃ψₙ²).
```

This is the char-free polynomial object satisfying

```text
twoωₙ = 2ωₙ
```

when the usual `ωₙ` exists.  For the separability identity, you can avoid `ωₙ` entirely at the differential-congruence stage:

```text
2 · φₙ · D(ψₙ) + n · Qₙ ≡ 0    mod ψₙ.
```

After reducing through Mathlib’s `Ψ`/`Φ` and `preΨ'`, this becomes

```text
2 · ηₙ · v · Φₙ · (preΨ'_n)' + n · Qₙ ≡ 0    mod preΨ'_n,
```

where

```text
v   = ψ₂ = 2Y + a₁X + a₃,
ηₙ = if Even n then v else 1.
```

This is the cleanest identity to formalize first.

---

## Important correction: use `φₙ`, not `Φₙ`, in the bivariate definition

The explicit formula is a bivariate-polynomial formula:

```text
2ωₙ = Qₙ - ψₙ · (a₁φₙ + a₃ψₙ²).
```

So in `R[X][Y]` it must use `W.φ n`, not `W.Φ n`.

You may replace `φₙ` by `Φₙ` only **after** mapping to the affine coordinate ring, using Mathlib’s existing congruence:

```lean
Affine.CoordinateRing.mk_φ (n : ℤ) :
  Affine.CoordinateRing.mk W (W.φ n) =
    Affine.CoordinateRing.mk W (C (W.Φ n))
```

Likewise, `ψₙ` is congruent to `Ψₙ` in the coordinate ring:

```lean
Affine.CoordinateRing.mk_ψ (n : ℤ) :
  Affine.CoordinateRing.mk W (W.ψ n) =
    Affine.CoordinateRing.mk W (W.Ψ n)
```

---

## Lean core definition

Here is the Lean core I would add near the division-polynomial development, or locally in your scratch file first.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- The polynomial quotient `Qₙ = ψ₂ₙ / ψₙ`.

This is the EDS 2-complement specialized to the division-polynomial EDS.  It is a genuine
polynomial over any commutative ring, with no localization and no division by `2`. -/
protected noncomputable def divisionQuot (n : ℤ) : R[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

/-- Defining property of `divisionQuot`: it witnesses `ψₙ ∣ ψ₂ₙ`. -/
theorem ψ_mul_divisionQuot (n : ℤ) :
    W.ψ n * W.divisionQuot n = W.ψ (2 * n) := by
  simpa [WeierstrassCurve.ψ, WeierstrassCurve.divisionQuot] using
    (normEDS_mul_complEDS₂
      (b := W.ψ₂)
      (c := C W.Ψ₃)
      (d := C W.preΨ₄)
      n)

/-- Divisibility form of `ψ_mul_divisionQuot`. -/
theorem ψ_dvd_ψ_two_mul (n : ℤ) :
    W.ψ n ∣ W.ψ (2 * n) := by
  exact ⟨W.divisionQuot n, (W.ψ_mul_divisionQuot n).symm⟩

/-- The bivariate constant polynomial attached to a curve coefficient. -/
private abbrev coeffBiv (r : R) : R[X][Y] :=
  C (C r)

/-- The division-by-2-free y-coordinate numerator.

Mathematically:

`twoωₙ = Qₙ - ψₙ · (a₁φₙ + a₃ψₙ²) = 2ωₙ`.

This is the preferred char-free object. -/
protected noncomputable def twoω (n : ℤ) : R[X][Y] :=
  W.divisionQuot n -
    W.ψ n * (coeffBiv W.a₁ * W.φ n + coeffBiv W.a₃ * W.ψ n ^ 2)

/-- Rearranged defining equation, often the most convenient rewrite form. -/
theorem divisionQuot_eq_twoω_add (n : ℤ) :
    W.divisionQuot n =
      W.twoω n + W.ψ n * (coeffBiv W.a₁ * W.φ n + coeffBiv W.a₃ * W.ψ n ^ 2) := by
  rw [WeierstrassCurve.twoω]
  abel

/-- Modulo `ψₙ`, the quotient `Qₙ` and `twoωₙ` have the same class. -/
theorem divisionQuot_sub_twoω_mem_span_ψ (n : ℤ) :
    W.divisionQuot n - W.twoω n ∈ Ideal.span ({W.ψ n} : Set R[X][Y]) := by
  refine Ideal.mem_span_singleton.mpr ?_
  refine ⟨coeffBiv W.a₁ * W.φ n + coeffBiv W.a₃ * W.ψ n ^ 2, ?_⟩
  rw [divisionQuot_eq_twoω_add]
  ring

end WeierstrassCurve
```

The theorem `divisionQuot_eq_twoω_add` is deliberately oriented as a rewrite away from `divisionQuot`.  For the differential identity modulo `ψₙ`, the last lemma lets you replace `twoωₙ` by `Qₙ` or vice versa.

---

## If `2` is invertible

If you only need characteristic not `2`, you can define `ωₙ` from `twoωₙ` by multiplying coefficients by `1/2`.

Do **not** try to invert `(2 : K[X][Y])`; the polynomial ring is not a field.  Inject the inverse scalar from `K` into the bivariate polynomial ring.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

private abbrev coeffBivK (r : K) : K[X][Y] :=
  C (C r)

/-- The usual y-coordinate numerator when `2` is invertible. -/
protected noncomputable def ωOfTwoInvertible (n : ℤ) : K[X][Y] :=
  coeffBivK ((2 : K)⁻¹) * W.twoω n

/-- Expected normalization lemma.  The proof is a one-line `field_simp`/`ring` argument
under the hypothesis `(2 : K) ≠ 0`. -/
theorem two_mul_ωOfTwoInvertible (n : ℤ) (h2 : (2 : K) ≠ 0) :
    coeffBivK (2 : K) * W.ωOfTwoInvertible n = W.twoω n := by
  rw [WeierstrassCurve.ωOfTwoInvertible]
  -- `coeffBivK` is a ring hom, so this reduces to `2 * 2⁻¹ = 1` in `K`.
  simp [coeffBivK, h2]

end WeierstrassCurve
```

This is enough for the usual separability proof over fields of characteristic not dividing `2n`.

---

## Why the implicit quadratic definition is a bad Lean definition

The cleared curve equation is

```text
ωₙ² + a₁Φₙωₙψₙ + a₃ωₙψₙ³
  = Φₙ³ + a₂Φₙ²ψₙ² + a₄Φₙψₙ⁴ + a₆ψₙ⁶.
```

This is useful as a theorem, but not as a definition.

Reasons:

1. **It does not select the branch.**  The quadratic equation encodes the curve equation for the point `[n]P`; a quadratic equation generally has two branches, geometrically corresponding to a point and its negation.  The division-polynomial recurrence selects one branch; the equation alone does not.

2. **Uniqueness fails badly in characteristic `2`.**  In characteristic `2`, the quadratic can become inseparable or partially linear, and the usual “two roots” intuition degenerates.  This is exactly the setting where a root-by-choice definition is least informative.

3. **A `Classical.choose` root will not compute.**  Even if you prove existence of some polynomial satisfying the quadratic and then define `ωₙ` as a chosen root, Lean will not know its relationship to `ψ₂ₙ / ψₙ`, to base change, to the EDS recurrences, or to the differential identity unless you prove all of those separately.  That defeats the purpose.

4. **The quadratic alone is weaker than the quotient identity.**  The quotient identity

   ```text
   2ωₙ + ψₙ(a₁φₙ + a₃ψₙ²) = Qₙ
   ```

   is branch-selecting.  The quadratic relation is a compatibility theorem after the branch has already been chosen.

So the quadratic should be a theorem about `twoω`/`ω`, not the definition.

---

## The `Qₙ` identity for separability

Let `D` be the invariant derivation

```text
D = ψ₂ · ∂/∂X + (3X² + 2a₂X + a₄ - a₁Y) · ∂/∂Y.
```

The division-by-2-free differential congruence is

```text
2 · φₙ · D(ψₙ) + n · Qₙ ≡ 0    mod ψₙ.
```

This follows from the usual identity

```text
φₙ · D(ψₙ) + n · ωₙ ≡ 0    mod ψₙ
```

by multiplying by `2` and using

```text
2ωₙ ≡ Qₙ    mod ψₙ.
```

Equivalently, it can be proved without mentioning `ωₙ` at all, by differentiating the `x`-coordinate formula

```text
x([n]P) = φₙ / ψₙ²
```

and clearing denominators.

In reduced Mathlib notation, set

```text
pₙ = preΨ'_n,
ηₙ = if Even n then ψ₂ else 1,
Ψₙ = C(pₙ) · ηₙ.
```

Modulo `C(pₙ)`, the invariant derivation gives

```text
D(Ψₙ) ≡ ηₙ · ψ₂ · C(pₙ.derivative).
```

Using `mk_φ` to replace `φₙ` by `C(Φₙ)`, the reduced congruence becomes

```text
2 · ηₙ · ψ₂ · C(Φₙ · pₙ.derivative) + n · Qₙ ≡ 0    mod C(pₙ).
```

This is the exact Lean target I would use if you want to avoid `Ωₙ` initially.

A schematic theorem statement:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

private abbrev coeffBivK (r : K) : K[X][Y] :=
  C (C r)

/-- Parity factor in `Ψₙ = C(preΨ'_n) * reducedPsiFactor n`. -/
def reducedPsiFactor (n : ℕ) : K[X][Y] :=
  if Even n then W.ψ₂ else 1

/-- The ideal generated by the reduced denominator in the affine coordinate ring. -/
def reducedPsiIdeal (n : ℕ) : Ideal W.toAffine.CoordinateRing :=
  Ideal.span
    ({Affine.CoordinateRing.mk W (C (W.preΨ' n))} : Set W.toAffine.CoordinateRing)

/-- Target reduced quotient congruence, avoiding `ωₙ` entirely. -/
theorem reduced_divisionQuot_differential_congruence (n : ℕ) :
    Affine.CoordinateRing.mk W
      ((coeffBivK (2 : K)) *
          (W.reducedPsiFactor n * W.ψ₂ * C (W.Φ (n : ℤ) * (W.preΨ' n).derivative))
        + coeffBivK (n : K) * W.divisionQuot (n : ℤ))
      ∈ W.reducedPsiIdeal n := by
  sorry

end WeierstrassCurve
```

The important feature is that this theorem has no `/ 2` and no `Ωₙ`.

---

## Does `Qₙ` alone finish separability?

It depends on whether characteristic `2` is in scope.

### If `char K ≠ 2`

Yes.  At a double root of `preΨ'_n`, the reduced quotient congruence gives

```text
n · Qₙ(P) = 0.
```

If `(n : K) ≠ 0`, then

```text
Qₙ(P) = 0.
```

Since `ψₙ(P) = 0`, the defining relation gives

```text
Qₙ(P) = 2ωₙ(P).
```

If `2 ≠ 0`, this implies

```text
ωₙ(P) = 0.
```

Then the cleared curve equation reduces to

```text
ωₙ(P)^2 = Φₙ(P)^3,
```

so `ωₙ(P) = 0` implies `Φₙ(P) = 0`, contradicting adjacent coprimality as planned.

So for `char K ∤ 2n`, `Qₙ` is enough and is the best Lean route.

### If `char K = 2` and `n` is odd

`Qₙ` alone is **not enough**.

At a root of `ψₙ`, the relation

```text
Qₙ = 2ωₙ + ψₙ(a₁φₙ + a₃ψₙ²)
```

specializes to

```text
Qₙ(P) = 2ωₙ(P).
```

In characteristic `2`, this says simply

```text
Qₙ(P) = 0,
```

regardless of `ωₙ(P)`.  Thus the quotient congruence will only prove something automatic; it loses exactly the y-coordinate information needed for the final contradiction.

For characteristic `2`, you need either:

1. a genuine `ωₙ` defined by universal integral construction and then reduced mod `2`, or
2. a different formal-group/differential argument that avoids extracting `ωₙ` from `Qₙ`.

The universal construction is the mathematically correct char-free way to define `ωₙ`: prove over the universal ring

```text
Qₙ - ψₙ(a₁φₙ + a₃ψₙ²)
```

has all coefficients divisible by `2`, divide those integer coefficients by `2`, and then map the resulting universal polynomial to any base ring.  This is precisely what Mathlib’s doc comment hints at.

---

## Recommended implementation path

### Phase 1: add `divisionQuot` and `twoω`

This is immediate from existing Mathlib APIs:

```lean
protected noncomputable def divisionQuot (W : WeierstrassCurve R) (n : ℤ) : R[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

protected noncomputable def twoω (W : WeierstrassCurve R) (n : ℤ) : R[X][Y] :=
  W.divisionQuot n -
    W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2)
```

Prove:

```text
ψₙ · Qₙ = ψ₂ₙ,
Qₙ = twoωₙ + ψₙ(a₁φₙ + a₃ψₙ²),
Qₙ ≡ twoωₙ mod ψₙ.
```

### Phase 2: prove the quotient differential identity

Avoid `ωₙ`:

```text
2φₙDψₙ + nQₙ ≡ 0 mod ψₙ.
```

Then reduce to `preΨ'`:

```text
2ηₙψ₂Φₙ(preΨ'_n)' + nQₙ ≡ 0 mod preΨ'_n.
```

### Phase 3: finish separability in characteristic not `2`

Define

```lean
ωOfTwoInvertible := (1/2) • twoω
```

as coefficient scaling, and use the curve equation theorem for `ω`.

### Phase 4: handle characteristic `2` only if needed

Do not rely on `Qₙ` for this.  Either define `ωₙ` universally, or prove separability through the formal group without converting `Qₙ` to `ωₙ`.

---

## Final recommendation

For the current Lean project, I would **not** try the implicit quadratic definition.  I would implement:

```text
Qₙ       := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n,
twoωₙ   := Qₙ - ψₙ(a₁φₙ + a₃ψₙ²).
```

Then prove the differential congruence using `Qₙ`:

```text
2 · ηₙ · ψ₂ · Φₙ · (preΨ'_n)' + n · Qₙ ≡ 0  mod preΨ'_n.
```

This is clean, char-free, and uses Mathlib’s existing EDS quotient machinery.  It proves the desired separability contradiction immediately under `char K ≠ 2` and `(n : K) ≠ 0`.  For characteristic `2`, `Qₙ` is still definable and useful, but it cannot replace `ωₙ`; the missing information is exactly the reduction of `ωₙ` modulo `2`, which must come from a universal construction or a separate formal-group argument.
