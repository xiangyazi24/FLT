# Q847 (dm3): `Ωₙ`, the quotient `Qₙ = ψ₂ₙ / ψₙ`, and the separability identity

## Bottom line

Yes: for the **division-by-2-free differential congruence**, you can avoid defining `Ωₙ` entirely.  Define

```text
Qₙ := ψ₂ₙ / ψₙ.
```

Then the useful congruence is

```text
2 · φₙ · D(ψₙ) + n · Qₙ ≡ 0  mod ψₙ,
```

where `D` is the invariant derivation

```text
D = ψ₂ · ∂/∂X + (3X² + 2a₂X + a₄ - a₁Y) · ∂/∂Y.
```

For **odd** `n`, using `ψₙ ≡ C(preΨ'_n)` and `φₙ ≡ C(Φₙ)` in the affine coordinate ring, this reduces to

```text
2 · ψ₂ · Φₙ · (preΨ'_n)' + n · Qₙ ≡ 0  mod preΨ'_n.
```

This is the cleanest Lean target if the final separability theorem assumes `2 ≠ 0` in the base field.

However, if the target theorem includes characteristic `2`, `Qₙ` does **not** replace `Ωₙ`.  In characteristic `2`, the congruence above loses exactly the y-coordinate information needed for the contradiction.  For characteristic `2`, one needs either a genuine char-free `Ωₙ` from the universal integral construction, or a separate formal-group/invariant-differential proof that gives the `Ωₙ` conclusion directly.

The answer to the last question is:

* `Qₙ` being a polynomial is proved by the EDS quotient/complement sequence.
* the derivative identity

  ```text
  2 · ψ₂ · Φₙ · (preΨ'_n)' + n · Qₙ ≡ 0 mod preΨ'_n
  ```

  is **not** a plain consequence of the EDS recurrence.  It is the invariant-differential identity `[n]^*ω = nω`, or equivalently the tangent action of multiplication by `n`.  You can prove it by induction through addition formulas, but that is essentially reproving the invariant differential identity in formula/EDS clothing.

---

## Do not define `Ωₙ` as an arbitrary quadratic root

The cleared curve equation is

```text
Ωₙ² + a₁ · Φₙ · Ωₙ · ψₙ + a₃ · Ωₙ · ψₙ³
  = Φₙ³ + a₂ · Φₙ² · ψₙ² + a₄ · Φₙ · ψₙ⁴ + a₆ · ψₙ⁶.
```

This is an important theorem, but it is a bad definition of `Ωₙ` in Lean.

Reasons:

1. The quadratic equation does not select the branch.  The two branches correspond to the two points over a given x-coordinate.

2. In characteristic `2`, the quadratic can become inseparable, and uniqueness from the equation is exactly what fails.

3. A `Classical.choose` root will not compute and will not automatically satisfy the EDS quotient identity, naturality under base change, or the differential identity.

4. A branch condition such as

   ```text
   2Ωₙ + a₁Φₙψₙ + a₃ψₙ³ = Qₙ
   ```

   is excellent in characteristic not `2`, but in characteristic `2` it does not determine `Ωₙ`.

So the quadratic equation should be proved **after** defining `Ωₙ`; it should not be the primary definition.

---

## Define `Qₙ` directly from Mathlib's EDS complement

Mathlib's EDS file already has the quotient sequence needed for `ψ₂ₙ / ψₙ`:

```text
normEDS b c d k · complEDS₂ b c d k = normEDS b c d (2*k).
```

Since Mathlib defines

```lean
W.ψ n = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n,
```

the Lean definition should be:

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
bivariate polynomial over any commutative ring. -/
protected noncomputable def divisionQuot (n : ℤ) : R[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

/-- `divisionQuot` witnesses `ψₙ ∣ ψ₂ₙ`. -/
theorem ψ_mul_divisionQuot (n : ℤ) :
    W.ψ n * W.divisionQuot n = W.ψ (2 * n) := by
  simpa [WeierstrassCurve.ψ, WeierstrassCurve.divisionQuot] using
    (normEDS_mul_complEDS₂
      (b := W.ψ₂)
      (c := C W.Ψ₃)
      (d := C W.preΨ₄)
      n)

/-- Divisibility form. -/
theorem ψ_dvd_ψ_two_mul (n : ℤ) :
    W.ψ n ∣ W.ψ (2 * n) := by
  exact ⟨W.divisionQuot n, (W.ψ_mul_divisionQuot n).symm⟩

end WeierstrassCurve
```

This definition is char-free and should be the first piece to add.

---

## Important correction: `Qₙ` is the full bivariate quotient

For odd `n`, one has

```text
Ψₙ = C(preΨ'_n),
Ψ₂ₙ = C(preΨ'_{2n}) · ψ₂.
```

So if you introduce a univariate quotient `qₙ` satisfying

```text
preΨ'_n · qₙ = preΨ'_{2n},
```

then the full bivariate quotient is

```text
Qₙ = C(qₙ) · ψ₂.
```

Thus writing

```text
Qₙ = preΨ(2n) / preΨ(n)
```

silently omits the extra `ψ₂` factor if `Qₙ` is meant to be `ψ₂ₙ / ψₙ`.  The safest Lean definition is the bivariate `W.divisionQuot n` above.  Then reduce it modulo `preΨ'_n` only when needed.

---

## The char-free `twoΩₙ` object

Even if you do not define `Ωₙ`, it is useful to define

```text
twoΩₙ := Qₙ - ψₙ · (a₁φₙ + a₃ψₙ²).
```

This satisfies

```text
twoΩₙ = 2Ωₙ
```

when the usual y-coordinate numerator exists.

Lean shape:

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

private abbrev coeffBiv (r : R) : R[X][Y] :=
  C (C r)

/-- Division-by-2-free y-coordinate numerator: `twoΩₙ = 2Ωₙ`. -/
protected noncomputable def twoΩ (n : ℤ) : R[X][Y] :=
  W.divisionQuot n -
    W.ψ n * (coeffBiv W.a₁ * W.φ n + coeffBiv W.a₃ * W.ψ n ^ 2)

/-- Branch-selecting equation for `twoΩₙ`. -/
theorem divisionQuot_eq_twoΩ_add (n : ℤ) :
    W.divisionQuot n =
      W.twoΩ n + W.ψ n * (coeffBiv W.a₁ * W.φ n + coeffBiv W.a₃ * W.ψ n ^ 2) := by
  rw [WeierstrassCurve.twoΩ]
  abel

/-- Modulo `ψₙ`, the quotient `Qₙ` and `twoΩₙ` have the same class. -/
theorem divisionQuot_sub_twoΩ_mem_span_ψ (n : ℤ) :
    W.divisionQuot n - W.twoΩ n ∈ Ideal.span ({W.ψ n} : Set R[X][Y]) := by
  refine Ideal.mem_span_singleton.mpr ?_
  refine ⟨coeffBiv W.a₁ * W.φ n + coeffBiv W.a₃ * W.ψ n ^ 2, ?_⟩
  rw [divisionQuot_eq_twoΩ_add]
  ring

end WeierstrassCurve
```

This is the correct char-free replacement for the formula with `/ 2`.

---

## If `2` is invertible, define `Ωₙ` from `twoΩₙ`

Over a field of characteristic not `2`, define the usual numerator by scalar multiplication with `1/2`:

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
protected noncomputable def ΩOfTwoInvertible (n : ℤ) : K[X][Y] :=
  coeffBivK ((2 : K)⁻¹) * W.twoΩ n

theorem two_mul_ΩOfTwoInvertible (n : ℤ) (h2 : (2 : K) ≠ 0) :
    coeffBivK (2 : K) * W.ΩOfTwoInvertible n = W.twoΩ n := by
  rw [WeierstrassCurve.ΩOfTwoInvertible]
  simp [coeffBivK, h2]

end WeierstrassCurve
```

This is enough for separability over fields with `CharP K p` and `p ∤ 2*n`.

---

## The quotient differential identity

Let `D` be the invariant derivation on the affine coordinate ring:

```text
D = ψ₂ · ∂/∂X + (3X² + 2a₂X + a₄ - a₁Y) · ∂/∂Y.
```

Then the full bivariate identity is:

```text
2 · φₙ · D(ψₙ) + n · Qₙ ≡ 0  mod ψₙ.
```

More precisely, one expects a stronger coordinate-ring identity of the form

```text
ψₙ · D(φₙ) - 2 · φₙ · D(ψₙ) = n · Qₙ,
```

or equivalently

```text
2 · φₙ · D(ψₙ) + n · Qₙ = ψₙ · D(φₙ).
```

The congruence modulo `ψₙ` is immediate from this equality.

The derivation is straightforward once `[n]^*ω = nω` is available.  Since

```text
x([n]P) = φₙ / ψₙ²,
v([n]P) = Qₙ / ψₙ³,
```

and `D` is dual to the invariant differential, we get

```text
D(x([n]P)) = n · v([n]P).
```

But

```text
D(φₙ / ψₙ²)
  = (ψₙ · D(φₙ) - 2φₙ · D(ψₙ)) / ψₙ³.
```

Comparing numerators gives

```text
ψₙ · D(φₙ) - 2φₙ · D(ψₙ) = nQₙ.
```

So the sign in

```text
2φₙDψₙ + nQₙ ≡ 0 mod ψₙ
```

is correct.

---

## Reduced odd-index theorem statement

For odd `n`, Mathlib's reduced denominator is simply

```text
Ψₙ = C(preΨ'_n).
```

Also, in the coordinate ring,

```text
φₙ ≡ C(Φₙ),
D(C f) = ψ₂ · C(f.derivative).
```

So the full quotient congruence reduces to:

```text
2 · ψ₂ · C(Φₙ · (preΨ'_n)') + n · Qₙ ≡ 0  mod C(preΨ'_n).
```

Lean target:

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

private abbrev coeffBiv (r : K) : K[X][Y] :=
  C (C r)

/-- Ideal generated by the reduced denominator `preΨ'_n` in the affine coordinate ring. -/
def reducedPsiIdeal (n : ℕ) : Ideal W.toAffine.CoordinateRing :=
  Ideal.span
    ({Affine.CoordinateRing.mk W (C (W.preΨ' n))} : Set W.toAffine.CoordinateRing)

/-- Odd-index reduced quotient congruence, avoiding `Ωₙ` entirely. -/
theorem odd_reduced_divisionQuot_differential_congruence
    (n : ℕ) (hn : Odd n) :
    Affine.CoordinateRing.mk W
      (coeffBiv (2 : K) *
          (W.ψ₂ * C (W.Φ (n : ℤ) * (W.preΨ' n).derivative))
        + coeffBiv (n : K) * W.divisionQuot (n : ℤ))
      ∈ W.reducedPsiIdeal n := by
  sorry

end WeierstrassCurve
```

This is the theorem I would prove before attempting any universal construction of `Ωₙ`.

---

## Does this prove separability by itself?

### In characteristic not `2`: yes

At a double root of `preΨ'_n`, the reduced quotient congruence gives

```text
n · Qₙ(P) = 0.
```

If `(n : K) ≠ 0`, then

```text
Qₙ(P) = 0.
```

At a root of `ψₙ`, the correction terms in

```text
Qₙ = 2Ωₙ + ψₙ(a₁φₙ + a₃ψₙ²)
```

vanish, so

```text
Qₙ(P) = 2Ωₙ(P).
```

If `2 ≠ 0`, this gives

```text
Ωₙ(P) = 0.
```

Then the cleared curve equation gives

```text
Ωₙ(P)^2 = Φₙ(P)^3.
```

Thus `Φₙ(P) = 0`, contradicting the odd-index coprimality package

```text
gcd(preΨ'_n, preΨ'_{n+1}) = 1,
gcd(preΨ'_n, preΨ'_{n-1}) = 1,
gcd(preΨ'_n, Ψ₂Sq) = 1.
```

So, if `2` is invertible, `Qₙ` is enough.

### In characteristic `2`: no

If `char K = 2` and `n` is odd, then `(n : K) ≠ 0`, but the quotient congruence becomes

```text
Qₙ ≡ 0  mod ψₙ.
```

At a root of `ψₙ`, this only says

```text
Qₙ(P) = 0.
```

But in characteristic `2`, the branch equation gives

```text
Qₙ(P) = 2Ωₙ(P) = 0
```

automatically.  It gives no information about `Ωₙ(P)`.  Therefore the final contradiction cannot be obtained from `Qₙ` alone in characteristic `2`.

This is exactly where the genuine `Ωₙ` identity

```text
ψ₂ · Φₙ · (preΨ'_n)' + n · Ωₙ ≡ 0 mod preΨ'_n
```

is stronger than the doubled quotient identity.

---

## If characteristic `2` is required: how to define genuine `Ωₙ`

The char-free way is the universal integral construction, not the quadratic-root construction.

Plan:

1. Work over the universal coefficient ring

   ```text
   𝓡 = ℤ[A₁,A₂,A₃,A₄,A₆].
   ```

2. Define the universal curve `𝓦`.

3. Define

   ```text
   universalTwoΩₙ := Qₙ - ψₙ(a₁φₙ + a₃ψₙ²)
   ```

   over `𝓡[X,Y]`.

4. Prove every coefficient of `universalTwoΩₙ` is divisible by `2` as an integer coefficient.

5. Define `universalΩₙ` by coefficientwise halving.

6. For any curve `W` over any commutative ring `R`, define `W.Ω n` by specializing

   ```text
   Aᵢ ↦ W.aᵢ.
   ```

7. Prove

   ```text
   2 · W.Ω n = W.twoΩ n
   ```

   by specialization from the universal theorem.

Schematic Lean shape:

```lean
-- schematic only: names/types depend on the universal curve setup you choose
abbrev UnivCoeff := MvPolynomial (Fin 5) ℤ

noncomputable def universalW : WeierstrassCurve UnivCoeff :=
  { a₁ := MvPolynomial.X 0,
    a₂ := MvPolynomial.X 1,
    a₃ := MvPolynomial.X 2,
    a₄ := MvPolynomial.X 3,
    a₆ := MvPolynomial.X 4 }

noncomputable def universalTwoΩ (n : ℤ) : UnivCoeff[X][Y] :=
  universalW.twoΩ n

-- hard theorem: coefficientwise evenness
theorem universalTwoΩ_even_coeff (n : ℤ) :
    ∀ m, Even ((universalTwoΩ n).coeff m) := by
  sorry

-- define by coefficientwise halving, then specialize to any base ring
noncomputable def universalΩ (n : ℤ) : UnivCoeff[X][Y] :=
  sorry
```

The hard part is the coefficientwise-evenness theorem.  This is what Mathlib's documentation alludes to when it says the usual `ωₙ` is well-defined by first proving divisibility by `2` in the characteristic-zero universal ring and then specializing.

Once `Ωₙ` is defined this way, the quadratic curve equation becomes a theorem about `Ωₙ`, not the definition.

---

## Can the quotient identity be proved from the EDS recurrence?

There are two different statements here.

### 1. `Qₙ` exists as a polynomial

Yes.  This is exactly EDS divisibility:

```text
ψₙ · Qₙ = ψ₂ₙ.
```

In Lean, this is `normEDS_mul_complEDS₂` specialized to `W.ψ`.

### 2. The derivative congruence

```text
2 · φₙ · D(ψₙ) + n · Qₙ ≡ 0 mod ψₙ
```

No, not from the plain EDS recurrence alone.

The recurrence defines the values of the sequence.  It does not know about:

* the derivation `D`,
* the invariant differential `dx / ψ₂`,
* the x-coordinate formula `x([n]P) = φₙ / ψₙ²`,
* the tangent action `[n]^*ω = nω`.

You could try to prove the derivative congruence by induction on the EDS recurrences, differentiating every recurrence and carrying many compatibility lemmas for `φₙ`, `Qₙ`, and `ψₙ`.  But that proof would be a disguised proof of the invariant-differential identity.  It is not simpler, and the odd recurrence will again produce cancellation cases rather than product-rule descent.

The Lean-friendly route is:

1. define the invariant derivation `D`,
2. prove `D` descends to the affine coordinate ring,
3. prove the x-coordinate differential identity

   ```text
   ψₙDφₙ - 2φₙDψₙ = nQₙ,
   ```

4. reduce it to the odd `preΨ'` congruence using `mk_ψ`, `mk_φ`, and `D(C f) = ψ₂ · C(f.derivative)`.

---

## Recommended implementation order

1. Add `divisionQuot`:

   ```lean
   W.divisionQuot n := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
   ```

2. Prove:

   ```lean
   W.ψ n * W.divisionQuot n = W.ψ (2*n)
   ```

3. Add `twoΩ`:

   ```lean
   W.twoΩ n := W.divisionQuot n - W.ψ n * (C(C W.a₁)*W.φ n + C(C W.a₃)*W.ψ n^2)
   ```

4. Prove the quotient differential identity:

   ```text
   2φₙDψₙ + nQₙ ≡ 0 mod ψₙ.
   ```

5. For odd `n`, reduce it to:

   ```text
   2ψ₂Φₙ(preΨ'_n)' + nQₙ ≡ 0 mod preΨ'_n.
   ```

6. If your separability theorem assumes `2 ≠ 0`, finish with `Qₙ` and `ΩOfTwoInvertible`.

7. If characteristic `2` is in scope, do not stop at `Qₙ`; build genuine `Ωₙ` by universal coefficientwise halving or use a formal-group proof that gives the undoubled identity directly.

---

## Final answer

The identity

```text
2 · v · Φ · ψ' + n · Q ≡ 0 mod ψ
```

is exactly the right way to avoid defining `Ωₙ` **when `2` is invertible**.  Define `Qₙ` via `complEDS₂`; this part is supplied by Mathlib's EDS infrastructure.

But the identity with the derivative is not just an EDS recurrence theorem.  It is the invariant-differential/tangent identity for multiplication by `n`.  In Lean, prove it through the invariant derivation or through formula-level multiplication and then reduce to `preΨ'`.  A recurrence-only proof would amount to reproving the same geometry in a much more painful form.

For characteristic `2`, `Qₙ` is still useful but insufficient for odd separability: the doubled identity collapses and does not determine `Ωₙ`.  There the right definition of `Ωₙ` is the universal integral one, not a chosen quadratic root.
