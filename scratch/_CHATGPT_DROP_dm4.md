# Q1977 (dm4): `KubertBridgeN16.lean`, the N = 16 formulas, and the obstruction curve

## Executive correction

There is a trap here: the statement

```text
X1(16) has genus 0
```

is not correct for the usual modular curve `X_1(16)` parameterizing an elliptic curve together with a point of exact order `16`.

The standard genus-zero list for `X_1(n)` is

```text
n = 1, 2, ..., 10, 12.
```

So `X_1(16)` is not analogous to `X_1(10)` or `X_1(12)`.  Consequently, there is no honest one-parameter rational Kubert family over `Q(t)` for a rational point of order `16` in the same sense as the N = 10 and N = 12 families.

What *does* exist is a genus-zero `X_0(16)` / quadratic-field normal form.  This is probably the formula that looks like the missing N = 16 Kubert family.  It gives rational coefficients and a point of order `16` over a quadratic field, not automatically over `Q`.

## The genus-zero-looking N = 16 coefficient pair

The useful coefficient pair is:

```text
A16(t) = (t^4 - 1)^2 - 4*t^2*(t^4 + 1)
       = t^8 - 4*t^6 - 2*t^4 - 4*t^2 + 1

B16(t) = 16*t^8.
```

Then

```text
A16(t)^2 - 4*B16(t)
  = (t - 1)^4 * (t + 1)^4 * (t^2 + 1)^2
      * (t^2 - 2*t - 1) * (t^2 + 2*t - 1).
```

Equivalently, after stripping the obvious square factor, the raw square condition is

```text
Y^2 = (t^2 - 2*t - 1) * (t^2 + 2*t - 1)
    = t^4 - 6*t^2 + 1.
```

This is **not** the same obstruction curve as

```text
w^2 = u^3 - u^2 - u        -- LMFDB 80.b3
```

under the same simple square-stripping transformation used for N = 10.  The latter curve is still the right obstruction curve already used in the N = 16 descent bridge, but the bridge from a hypothetical `ZMod 2 × ZMod 16` subgroup to a nondegenerate point on `80.b3` should be treated as the bridge axiom, not as a direct `A16^2 - 4B16` identity from the genus-zero-looking coefficient pair above.

## Recommended design

For `KubertBridgeN16.lean`, keep two layers separate:

1. A ring-verifiable section recording the N = 16 coefficient pair and its discriminant factorization.
2. The actual Mazur-discharge bridge axiom, landing on the obstruction curve `80.b3`:

```text
w^2 = u^3 - u^2 - u.
```

This is the robust analogue of the existing `DescentBridgeN16.lean` shape.

## Complete Lean 4 file

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

/-!
# Kubert bridge for the N = 16 obstruction

This file separates two facts which should not be conflated.

* There is a genus-zero-looking N = 16 coefficient pair

    A16(t) = (t^4 - 1)^2 - 4*t^2*(t^4 + 1),
    B16(t) = 16*t^8,

  whose discriminant has a completely ring-verifiable factorization.
  This is the `X_0(16)` / quadratic-field normal form: it gives rational
  coefficients and a point of order 16 over a quadratic field.

* The actual rational obstruction used for the Mazur discharge is the curve

    w^2 = u^3 - u^2 - u,

  LMFDB `80.b3`.  The public bridge axiom should land directly on a
  nondegenerate rational point of this curve.

Do **not** advertise this as a genus-zero `X_1(16)` family over `Q(t)`.
The usual `X_1(n)` genus-zero list is `n = 1, ..., 10, 12`, not `16`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof
namespace KubertBridgeN16

/-- The rational coefficient `A` in the genus-zero-looking N = 16 normal form. -/
def A16 (t : ℚ) : ℚ :=
  (t ^ 4 - 1) ^ 2 - 4 * t ^ 2 * (t ^ 4 + 1)

/-- The rational coefficient `B` in the genus-zero-looking N = 16 normal form. -/
def B16 (t : ℚ) : ℚ :=
  16 * t ^ 8

/-- Expanded form of `A16`, useful for matching external tables. -/
theorem A16_expanded (t : ℚ) :
    A16 t = t ^ 8 - 4 * t ^ 6 - 2 * t ^ 4 - 4 * t ^ 2 + 1 := by
  unfold A16
  ring

/-- The key ring-verifiable discriminant factorization. -/
theorem A16_sq_sub_four_B16_factor (t : ℚ) :
    A16 t ^ 2 - 4 * B16 t =
      (t - 1) ^ 4 * (t + 1) ^ 4 * (t ^ 2 + 1) ^ 2 *
        (t ^ 2 - 2 * t - 1) * (t ^ 2 + 2 * t - 1) := by
  unfold A16 B16
  ring

/-- The square factor in `A16^2 - 4B16`. -/
def A16SquareFactor (t : ℚ) : ℚ :=
  (t - 1) ^ 2 * (t + 1) ^ 2 * (t ^ 2 + 1)

/-- The remaining raw quartic factor after removing the square factor. -/
def A16RawQuartic (t : ℚ) : ℚ :=
  (t ^ 2 - 2 * t - 1) * (t ^ 2 + 2 * t - 1)

/-- Expanded form of the raw quartic factor. -/
theorem A16RawQuartic_expanded (t : ℚ) :
    A16RawQuartic t = t ^ 4 - 6 * t ^ 2 + 1 := by
  unfold A16RawQuartic
  ring

/--
If the discriminant is a square, then after dividing by the evident square
factor one obtains the raw quartic square condition.

This theorem is deliberately stated only for the raw quartic.  It is not the
`80.b3` obstruction curve.
-/
theorem square_discriminant_to_raw_quartic
    {t d : ℚ}
    (hD : d ^ 2 = A16 t ^ 2 - 4 * B16 t)
    (hden : A16SquareFactor t ≠ 0) :
    (d / A16SquareFactor t) ^ 2 = A16RawQuartic t := by
  rw [hD]
  unfold A16SquareFactor A16RawQuartic
  rw [A16_sq_sub_four_B16_factor]
  field_simp [hden]
  ring

/-! ## The actual N = 16 obstruction curve: LMFDB 80.b3 -/

/-- The N = 16 obstruction curve, LMFDB `80.b3`. -/
def E_N16_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - u

/-- Degenerate/cuspidal `u`-coordinates for the N = 16 obstruction. -/
def E_N16_DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

/--
Rational-points theorem for the obstruction curve.

For LMFDB `80.b3`, the Mordell-Weil group is `Z/2Z`; the affine rational
points are just `(0,0)`.  This degenerate predicate is intentionally a little
larger, matching the existing bridge API.
-/
axiom obstruction_curve_N16_points_degenerate :
    ∀ u w : ℚ, E_N16_AffineEquation u w → E_N16_DegenerateParameter u

/--
The actual N = 16 Kubert/descent bridge needed for the Mazur discharge.

A hypothetical `Z/2Z × Z/16Z` subgroup produces a nondegenerate rational
point on the obstruction curve `w^2 = u^3 - u^2 - u`.

This is the correct one-axiom interface to pair with the rational-points
calculation for `80.b3`.
-/
axiom Z2xZ16_gives_non_degenerate_N16_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u

/-- No elliptic curve over `ℚ` has a subgroup `Z/2Z × Z/16Z`. -/
theorem no_Z2_cross_Z16_from_kubert_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ16_gives_non_degenerate_N16_point E hE with
    ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N16_points_degenerate u w hcurve)

end KubertBridgeN16
end MazurProof
```

## If you want the shorter bridge-only version

If the goal is just to match the existing `DescentBridgeN16.lean`, the minimal file is:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped WeierstrassCurve.Affine

namespace MazurProof

def E_N16_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - u

def E_N16_DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

axiom obstruction_curve_N16_points_degenerate :
    ∀ u w : ℚ, E_N16_AffineEquation u w → E_N16_DegenerateParameter u

axiom Z2xZ16_gives_non_degenerate_N16_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u

theorem no_Z2_cross_Z16_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ16_gives_non_degenerate_N16_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N16_points_degenerate u w hcurve)

end MazurProof
```

## Bottom line

Use the ring identities above if you want to record the genus-zero-looking `X_0(16)` coefficient pair.

But for the Mazur proof, do **not** base the N = 16 discharge on a claim that `X_1(16)` is genus zero.  The safe public bridge axiom is:

```text
Z/2Z × Z/16Z torsion over Q gives a nondegenerate rational point on
w^2 = u^3 - u^2 - u.
```

Then `RationalPoints` for LMFDB `80.b3` closes the contradiction.
