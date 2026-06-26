# Q776 (dm3): exact polynomial identity for separability of `preΨ'`

## Bottom line

The identity you wrote is the right **odd-`n` reduced identity**, but it is not quite the uniform Mathlib-compatible identity for all `n : ℕ`.

Mathlib currently has `preΨ'`, `Ψ`, `Φ`, `ψ`, and `φ`; it does **not** currently define the y-coordinate numerator `ωₙ`/`Ωₙ` as a declaration. The file comment in `DivisionPolynomial/Basic.lean` still lists:

```text
TODO: the bivariate polynomials `ωₙ`.
```

So the clean Lean plan is to first add either `ω` or, better, a division-by-2-free `twoω`.

The exact reduced congruence is:

```text
ηₙ · v · Φₙ · (preΨ'_n)' + n · Ωₙ ≡ 0  mod preΨ'_n,
```

where

```text
v   = ψ₂ = 2Y + a₁X + a₃,
ηₙ = if Even n then v else 1.
```

Thus:

* if `n` is odd, `ηₙ = 1`, and the identity is exactly

  ```text
  v · Φₙ · (preΨ'_n)' + n · Ωₙ ≡ 0  mod preΨ'_n;
  ```

* if `n` is even, the exact reduced identity has one extra factor of `v`:

  ```text
  v^2 · Φₙ · (preΨ'_n)' + n · Ωₙ ≡ 0  mod preΨ'_n.
  ```

That extra factor is not cosmetic. It comes from Mathlib's reduced/full relation

```lean
W.Ψ (n : ℤ) = C (W.preΨ' n) * if Even n then W.ψ₂ else 1
```

because, in the coordinate ring, the invariant derivation satisfies

```text
D(C f) = v · C(f.derivative).
```

So when `n` is even,

```text
D(Ψₙ) ≡ D(C(preΨ'_n) · v)
      ≡ v · D(C(preΨ'_n))
      ≡ v² · C((preΨ'_n)')       mod preΨ'_n.
```

For the contradiction argument, the distinction usually does not hurt: if `(preΨ'_n)'(x) = 0`, then both `v · Φₙ · (preΨ'_n)'` and `v² · Φₙ · (preΨ'_n)'` vanish after evaluation. But for an exact theorem statement, the parity factor must be present.

---

## Recommended notation

In Mathlib notation, use `W.ψ₂` for `v`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- The invariant-differential denominator `v = 2Y + a₁X + a₃`.

In Mathlib this is already the second division polynomial. -/
abbrev vPoly : R[X][Y] :=
  W.ψ₂

/-- The parity factor relating the reduced univariate `preΨ' n` to the full bivariate `Ψ n`.

For odd `n`, the full denominator is just `C (preΨ' n)`.
For even `n`, it is `C (preΨ' n) * ψ₂`. -/
def reducedPsiFactor (n : ℕ) : R[X][Y] :=
  if Even n then W.ψ₂ else 1

lemma Ψ_ofNat_eq_preΨ'_mul_reducedPsiFactor (n : ℕ) :
    W.Ψ (n : ℤ) = C (W.preΨ' n) * W.reducedPsiFactor n := by
  -- This should be a `simpa` wrapper around Mathlib's `WeierstrassCurve.Ψ_ofNat`.
  -- Depending on the local simp set, one may need to normalize `Even (n : ℤ)` vs `Even n`.
  simpa [reducedPsiFactor] using (WeierstrassCurve.Ψ_ofNat (W := W) n)

end WeierstrassCurve
```

The last lemma is the key bookkeeping lemma: it explains exactly why the odd and even reduced identities differ.

---

## The identity I would formalize first: avoid division by `2`

Since Mathlib does not yet define `ωₙ`, do **not** start by trying to define `Ωₙ` over an arbitrary `CommRing` using `/ 2`. Define the doubled numerator first.

Mathematically:

```text
twoΩₙ = ψ₂ₙ / ψₙ - ψₙ · (a₁φₙ + a₃ψₙ²).
```

Then `twoΩₙ = 2Ωₙ` when `Ωₙ` is available.

The full bivariate congruence is:

```text
2 · φₙ · D(ψₙ) + n · twoΩₙ ≡ 0  mod ψₙ,
```

where `D` is the invariant derivation on the affine coordinate ring:

```text
D = v · ∂/∂X + (3X² + 2a₂X + a₄ - a₁Y) · ∂/∂Y.
```

After passing through Mathlib's coordinate-ring congruences

```lean
Affine.CoordinateRing.mk_ψ : mk W (W.ψ n) = mk W (W.Ψ n)
Affine.CoordinateRing.mk_φ : mk W (W.φ n) = mk W (C (W.Φ n))
```

and then reducing modulo `C (W.preΨ' n)`, this becomes the reduced identity:

```text
2 · ηₙ · v · Φₙ · (preΨ'_n)' + n · twoΩₙ ≡ 0  mod preΨ'_n.
```

If you work over a ring/field where `2` is invertible and define `Ωₙ = twoΩₙ / 2`, then divide by `2` to get:

```text
ηₙ · v · Φₙ · (preΨ'_n)' + n · Ωₙ ≡ 0  mod preΨ'_n.
```

That is the exact identity to aim for.

---

## Lean target statement

The most robust Lean target is an ideal-membership statement in the affine coordinate ring, not a raw syntactic `%` statement.

Here is the shape I would use once `twoΩ` exists.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Placeholder for the doubled y-coordinate numerator.

This is not in Mathlib yet.  The desired defining relation is
`twoΩ n = ψ (2*n) / ψ n - ψ n * (a₁φ n + a₃ψ n^2)`, avoiding division by `2`.
In the actual implementation, define this using a divisibility theorem
`ψ n ∣ ψ (2*n)` or by the universal construction. -/
noncomputable def twoΩ (_n : ℤ) : K[X][Y] :=
  sorry

/-- The parity factor relating reduced and full division denominators. -/
def reducedPsiFactor (n : ℕ) : K[X][Y] :=
  if Even n then W.ψ₂ else 1

/-- The ideal in the affine coordinate ring generated by the reduced univariate denominator. -/
def reducedPsiIdeal (n : ℕ) : Ideal W.toAffine.CoordinateRing :=
  Ideal.span
    ({Affine.CoordinateRing.mk W (C (W.preΨ' n))} : Set W.toAffine.CoordinateRing)

/-- Exact reduced differential congruence, stated without dividing by `2`.

This is the theorem to prove first.  It specializes to the user's displayed identity after
assuming `2` is invertible and setting `Ω = twoΩ / 2`. -/
theorem reduced_twoΩ_differential_congruence (n : ℕ) :
    Affine.CoordinateRing.mk W
      ((2 : K[X][Y]) *
          (W.reducedPsiFactor n * W.ψ₂ *
            C (W.Φ (n : ℤ) * (W.preΨ' n).derivative))
        + (n : K[X][Y]) * W.twoΩ (n : ℤ))
      ∈ W.reducedPsiIdeal n := by
  sorry

/-- If `Ω` is available and `2` is invertible, this is the divided-by-2 statement. -/
noncomputable def Ω (_n : ℤ) : K[X][Y] :=
  sorry

theorem reduced_Ω_differential_congruence (n : ℕ) :
    Affine.CoordinateRing.mk W
      (W.reducedPsiFactor n * W.ψ₂ *
          C (W.Φ (n : ℤ) * (W.preΨ' n).derivative)
        + (n : K[X][Y]) * W.Ω (n : ℤ))
      ∈ W.reducedPsiIdeal n := by
  sorry

end WeierstrassCurve
```

Notes on the syntax:

* `C (W.preΨ' n)` lifts the univariate polynomial `K[X]` to the bivariate polynomial ring `K[X][Y]`.
* `W.ψ₂` is the bivariate polynomial `2Y + a₁X + a₃`.
* `W.Φ (n : ℤ)` is univariate, so `C (W.Φ (n : ℤ) * (W.preΨ' n).derivative)` is bivariate.
* The scalar `(n : K[X][Y])` is the natural-number coefficient inside the bivariate polynomial ring.
* If Lean has trouble with `W.toAffine.CoordinateRing` versus `Affine.CoordinateRing W`, follow the style already used in Mathlib's division-polynomial file: its lemmas are stated as `Affine.CoordinateRing.mk_ψ` and `Affine.CoordinateRing.mk_φ`, with `mk W`/`Affine.CoordinateRing.mk W` applied to bivariate polynomials.

---

## Why the sign is `+ n · Ωₙ`

Use the local parameter at infinity

```text
t = -x/y.
```

For multiplication by `n`, the affine formulas are

```text
x([n]P) = φₙ / ψₙ²,
y([n]P) = Ωₙ / ψₙ³.
```

Hence

```text
t([n]P) = -x([n]P) / y([n]P)
         = -φₙψₙ / Ωₙ.
```

At a point where `ψₙ = 0`, differentiating modulo `ψₙ` gives

```text
D(t([n]P)) ≡ -φₙ · D(ψₙ) / Ωₙ  mod ψₙ.
```

The invariant differential gives the tangent action of `[n]` as multiplication by `n`, so

```text
D(t([n]P)) ≡ n  mod ψₙ.
```

Therefore

```text
-φₙ · D(ψₙ) / Ωₙ ≡ n,
```

or equivalently

```text
φₙ · D(ψₙ) + n · Ωₙ ≡ 0  mod ψₙ.
```

So the sign in your proposed identity is correct for the standard convention
`Ωₙ =` y-coordinate numerator and `t = -x/y`. If someone instead uses `t = x/y`, the sign flips.

---

## How to prove the identity in Lean

The proof should not start from resultants.  It should start from a derivation on the coordinate ring.

### 1. Define the invariant derivation

On `K[X][Y]`, define

```text
D = v · ∂X + g · ∂Y,

g = 3X² + 2a₂X + a₄ - a₁Y.
```

The essential lemmas are:

```lean
-- schematic names
lemma invariantDeriv_C (f : K[X]) :
    D W (C f) = W.ψ₂ * C f.derivative := by
  ...

lemma invariantDeriv_Y :
    D W Y = C (3 * X^2 + C (2 * W.a₂) * X + C W.a₄) - C (C W.a₁) * Y := by
  ...

lemma invariantDeriv_curvePolynomial :
    D W W.toAffine.polynomial = 0 := by
  ring_nf [D, W.ψ₂, W.toAffine.polynomial]
```

The last lemma lets `D` descend to `W.toAffine.CoordinateRing`.

### 2. Prove the full differential congruence

Prove in the coordinate ring modulo `mk W (W.ψ n)`:

```text
2 · φₙ · D(ψₙ) + n · twoΩₙ ≡ 0.
```

A good derivation is through the invariant differential identity for the `x`-coordinate:

```text
D(φₙ / ψₙ²) = n · v([n]P).
```

After clearing denominators:

```text
D(φₙ) · ψₙ - 2φₙ · D(ψₙ) = n · (ψ₂ₙ / ψₙ).
```

Reduce modulo `ψₙ` and use

```text
twoΩₙ ≡ ψ₂ₙ / ψₙ  mod ψₙ.
```

This gives

```text
2φₙD(ψₙ) + n·twoΩₙ ≡ 0  mod ψₙ.
```

This route avoids having to reason directly with the local parameter `t`, although conceptually it is the same tangent calculation.

### 3. Replace `ψ`, `φ` by Mathlib's reduced `Ψ`, `Φ`

Use the existing coordinate-ring congruences:

```lean
Affine.CoordinateRing.mk_ψ (W := W) (n : ℤ) :
  Affine.CoordinateRing.mk W (W.ψ n) = Affine.CoordinateRing.mk W (W.Ψ n)

Affine.CoordinateRing.mk_φ (W := W) (n : ℤ) :
  Affine.CoordinateRing.mk W (W.φ n) = Affine.CoordinateRing.mk W (C (W.Φ n))
```

Then use:

```lean
W.Ψ (n : ℤ) = C (W.preΨ' n) * W.reducedPsiFactor n
```

and the derivation lemma

```text
D(C f) = v · C(f.derivative)
```

to reduce modulo `C (W.preΨ' n)`.

This produces the target reduced identity with the parity factor `ηₙ`.

---

## Separability contradiction using the identity

Assume:

```text
K is a field,
W is nonsingular,
(n : K) ≠ 0,
preΨ'_n(α) = 0,
(preΨ'_n)'(α) = 0.
```

Work over an algebraic closure and choose a point `P = (α, β)` on the curve lying above `α`.

The reduced identity gives, after evaluation at `P`:

```text
n · Ωₙ(P) = 0.
```

Since `(n : K) ≠ 0`, this implies

```text
Ωₙ(P) = 0.
```

To contradict this, use the weighted curve relation for multiplication:

```text
Ωₙ² + a₁ Φₙ Ψₙ Ωₙ + a₃ Ψₙ³ Ωₙ
  = Φₙ³ + a₂ Φₙ² Ψₙ² + a₄ Φₙ Ψₙ⁴ + a₆ Ψₙ⁶.
```

Modulo `preΨ'_n`, the full denominator `Ψₙ` vanishes, so this reduces to

```text
Ωₙ² = Φₙ³.
```

Thus it is enough to prove

```text
Φₙ(P) ≠ 0.
```

Using Mathlib's definition of `Φ`, modulo `preΨ'_n` one gets

```text
Φₙ ≡ - preΨ'_{n+1} · preΨ'_{n-1} · parityFactor,
```

where the extra factor is:

```text
if Even n then 1 else Ψ₂Sq.
```

So the required coprimality package is:

```text
gcd(preΨ'_n, preΨ'_{n+1}) = 1,
gcd(preΨ'_n, preΨ'_{n-1}) = 1,
if Odd n then gcd(preΨ'_n, Ψ₂Sq) = 1.
```

The last condition says an odd-`n` torsion point is not a 2-torsion point.  It is easy conceptually, but it should be made explicit in Lean because it is exactly the factor that appears in `Φ` for odd `n`.

Then `Φₙ(P) ≠ 0`, hence `Ωₙ(P)^2 = Φₙ(P)^3 ≠ 0`, so `Ωₙ(P) ≠ 0`, contradiction.

---

## Can step 4 be proved using only the EDS recurrence?

Not cleanly.

The adjacent-coprimality part is EDS-flavored, and the definitions of `ψ`, `Ψ`, and `Φ` are EDS-flavored.  But the key implication

```text
(preΨ'_n)'(P.x) = 0  ⇒  Ωₙ(P) = 0
```

is infinitesimal.  It is the tangent action of multiplication-by-`n`, equivalently `[n]^*ω = nω`.

You can prove it by induction on the EDS recurrences if you strengthen the induction to include the derivative identity, but that is essentially re-proving the invariant-differential statement inside the EDS development.  It is not a simpler proof; it just hides the geometry.

The best Lean route is therefore:

1. add `twoΩ`/`Ω`,
2. add the invariant derivation on the coordinate ring,
3. prove the full congruence `2φDψ + n·twoΩ ≡ 0 mod ψ`,
4. reduce it to `preΨ'` using `mk_ψ`, `mk_φ`, and the parity factor.

---

## Direct gcd/resultant alternative

For a fixed small `n`, yes, a CAS-style certificate is possible:

```text
gcd(preΨ'_n, (preΨ'_n)') = 1
```

can be proved by producing explicit Bézout polynomials, or by computing a resultant and showing it is nonzero after the required hypotheses.

For arbitrary `n`, this is not the route I would take in Lean.  The general resultant/discriminant of division polynomials is a large theorem: it will involve powers of `n` and the discriminant of the curve.  Formalizing that universal resultant identity is likely harder than formalizing the invariant-differential congruence above.

So:

* **small fixed `n`**: resultant/Bézout certificate is feasible;
* **general `n`**: use the differential identity;
* **Mathlib-compatible exact statement**: include the parity factor `ηₙ = if Even n then ψ₂ else 1`.
