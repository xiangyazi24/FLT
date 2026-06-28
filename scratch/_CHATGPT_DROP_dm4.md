# Q1973 (dm4): `KubertBridgeN14.lean` and the genus-1 base

## Executive answer

Yes: you can still write a `KubertBridgeN14.lean` whose public API reduces the N = 14 case to **one bridge axiom**, analogous in proof use to `kubert_C10_square` and `kubert_C12_square`.

But the **shape** of the axiom should change.  For N = 10 and N = 12 the bridge can look like a square condition in one free Kubert parameter because `X1(10)` and `X1(12)` are genus 0.  For N = 14, `X1(14)` is genus 1, so there is no global rational one-parameter Kubert coordinate.  The internal parameter space is instead a pair `(r,z)` on

```text
z^2 = 1 - 2*r + r^2 + 4*r^3.
```

So the N = 14 bridge should not be named or shaped as `kubert_C14_square`.  It should be a **noncuspidal obstruction-point axiom**:

```lean
axiom kubert_C14_obstruction_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u
```

Then the rational-points file for the obstruction curve proves that every rational point is degenerate, giving the contradiction.

## Obstruction curve API

Use the same target obstruction curve as in the existing N = 14 descent bridge:

```lean
def E_N14_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - 2 * u

/-- Affine cusp / degenerate `u`-coordinates on the N = 14 obstruction curve. -/
def E_N14_DegenerateParameter (u : ℚ) : Prop :=
  u = -2 ∨ u = 0 ∨ u = 1
```

This is the curve

```text
w^2 = u^3 + u^2 - 2u,
```

with LMFDB label `96.b3`.  Its rational points are

```text
O, (-2,0), (0,0), (1,0).
```

Thus the affine rational-points theorem should have this exact shape:

```lean
theorem obstruction_curve_N14_points_degenerate :
    ∀ u w : ℚ, E_N14_AffineEquation u w → E_N14_DegenerateParameter u := by
  -- from RationalPoints for LMFDB 96.b3 / E(Q) ~= (Z/2Z)^2
  ...
```

For the axiom-discharge skeleton, it is also fine to leave this as the existing axiom name until the rational-points proof is wired in:

```lean
axiom obstruction_curve_N14_points_degenerate :
    ∀ u w : ℚ, E_N14_AffineEquation u w → E_N14_DegenerateParameter u
```

## The single-axiom bridge for cyclic C14

For Mazur's cyclic torsion case, the clean single axiom is:

```lean
axiom C14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u
```

Then the final contradiction theorem is tiny:

```lean
theorem no_C14_from_N14_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases C14_gives_non_degenerate_N14_point E hE with
    ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N14_points_degenerate u w hcurve)
```

This is the direct analogue of the N = 10 and N = 12 bridge-discharge pattern, except that the bridge output is not a square predicate; it is a nondegenerate rational point on the genus-one obstruction curve.

## Product-group variant already matching the repo's `DescentBridgeN14.lean`

The repository already has the same bridge shape for the `ZMod 2 × ZMod 14` product-group target:

```lean
axiom Z2xZ14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u
```

and then:

```lean
theorem no_Z2_cross_Z14_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ14_gives_non_degenerate_N14_point E hE with
    ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N14_points_degenerate u w hcurve)
```

So if `KubertBridgeN14.lean` is for the cyclic Mazur case, use the `ZMod 14` axiom.  If it is for the product-group FLT branch, keep the existing `ZMod 2 × ZMod 14` source.

## More honest internal factorization of the N = 14 bridge

If you want the file to expose the genus-1 Kubert geometry rather than hiding it completely, split the bridge into two facts and prove the single public axiom by composition.

First define the genus-one Kubert base:

```lean
def X1_14_BaseEquation (r z : ℚ) : Prop :=
  z ^ 2 = 1 - 2 * r + r ^ 2 + 4 * r ^ 3

/-- Placeholder for excluding cusps / singular Kubert specializations. -/
def X1_14_NonCusp (r z : ℚ) : Prop :=
  True  -- replace by the actual denominator/discriminant side conditions
```

Then use a Kubert normal-form axiom landing on the base:

```lean
axiom kubert_C14_base_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ r z : ℚ, X1_14_BaseEquation r z ∧ X1_14_NonCusp r z
```

and a map from the noncuspidal base point to the obstruction curve:

```lean
axiom x1_14_base_to_obstruction_point
    {r z : ℚ}
    (hbase : X1_14_BaseEquation r z)
    (hnoncusp : X1_14_NonCusp r z) :
    ∃ u w : ℚ,
      E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u
```

The public one-axiom bridge can then be a theorem:

```lean
theorem C14_gives_non_degenerate_N14_point'
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u := by
  rcases kubert_C14_base_point E hE with ⟨r, z, hbase, hnoncusp⟩
  exact x1_14_base_to_obstruction_point hbase hnoncusp
```

This split is mathematically clearer, but for axiom discharge the combined `C14_gives_non_degenerate_N14_point` axiom is enough.

## Recommended `KubertBridgeN14.lean` skeleton

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! # Kubert bridge for the N = 14 obstruction -/

def E_N14_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - 2 * u

def E_N14_DegenerateParameter (u : ℚ) : Prop :=
  u = -2 ∨ u = 0 ∨ u = 1

/-- Rational points on LMFDB 96.b3 are all cuspidal/degenerate. -/
axiom obstruction_curve_N14_points_degenerate :
    ∀ u w : ℚ, E_N14_AffineEquation u w → E_N14_DegenerateParameter u

/--
Kubert N = 14 bridge.

Unlike N = 10 and N = 12, this is not a one-parameter square obstruction.
Internally it goes through the genus-one Kubert base
`z^2 = 1 - 2*r + r^2 + 4*r^3`, then maps a noncuspidal base point
to a nondegenerate point on `w^2 = u^3 + u^2 - 2*u`.
-/
axiom C14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u

theorem no_C14_from_N14_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases C14_gives_non_degenerate_N14_point E hE with
    ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N14_points_degenerate u w hcurve)

end MazurProof
```

## Bottom line

The genus-one base **does fundamentally change the bridge internals**: no single free Kubert parameter, and no natural `kubert_C14_square` theorem.

But it does **not** prevent a one-axiom discharge interface.  The right single axiom is:

```text
C14 torsion over Q gives a nondegenerate rational point on
E14 : w^2 = u^3 + u^2 - 2u.
```

Then the rational-points theorem for `96.b3` immediately kills it.
