# Q1207 (dm2): finiteness of real `m`-torsion from division polynomials

## Bottom line

I do **not** think the requested theorem can currently be proved as a no-`sorry`, Mathlib-only theorem from

```lean
import Mathlib
```

using only `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

The obstruction is not the finite-root argument.  That part is elementary.  The obstruction is the missing bridge theorem:

```text
m • P = 0  ==>  the x-coordinate of P is a root of the relevant division polynomial.
```

The current Mathlib division-polynomial file defines the polynomials, their recurrences, and map/base-change lemmas, but it does **not** appear to expose a theorem connecting `m • P = 0` in the elliptic-curve group to vanishing of `ψ_m`, `Ψ m`, `ΨSq m`, or `preΨ' m` at the point.

The docs for `DivisionPolynomial.Basic` list the available objects:

```lean
WeierstrassCurve.ψ₂
WeierstrassCurve.Ψ₂Sq
WeierstrassCurve.Ψ₃
WeierstrassCurve.preΨ₄
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ
WeierstrassCurve.map_ψ
WeierstrassCurve.baseChange_ψ
-- and analogous map/baseChange lemmas for the other polynomials
```

and the file explicitly says that `ωₙ` is still TODO.  It does not provide a point-multiplication formula or an iff theorem for torsion points and division-polynomial vanishing.

So the exact theorem

```lean
real_mTorsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) (hm : 0 < m) :
    Set.Finite {P : (E / ℝ).Point | m • P = 0}
```

is not presently a one-file consequence of the division-polynomial definitions.

Also, in Lean this should use additive scalar multiplication:

```lean
m • P = 0
```

not

```lean
m * P = 0
```

unless the FLT repo has custom notation translating `m * P` into scalar multiplication.

---

## The right polynomial to use

For a finiteness proof by `x`-coordinates, do **not** use only `preΨ' m`.

For even `m`, Mathlib's `preΨ'` deliberately strips off the `ψ₂` factor.  Thus `preΨ' 2 = 1`, so it cannot cut out the nonzero `2`-torsion points.  The univariate polynomial intended to remember the even `ψ₂` contribution is `ΨSq`:

```lean
W.ΨSq (m : ℤ) : ℝ[X]
```

For odd `m`, `ΨSq m` is essentially `preΨ m ^ 2`; for even `m`, it includes the `Ψ₂Sq` factor.  Thus, morally, the finite-root set should be:

```lean
{ x : ℝ | (W.ΨSq (m : ℤ)).eval x = 0 }
```

plus the point at infinity/zero point.

The proof also needs:

```lean
(W.ΨSq (m : ℤ)) ≠ 0
```

because `Polynomial.rootSet` is finite only for nonzero polynomials over a field.  I do not see a ready theorem in `DivisionPolynomial.Basic` packaging nonzeroness of `ΨSq m` for `0 < m` over `ℝ`.

So the missing bridge package is at least:

```lean
import Mathlib

namespace FLT

open Polynomial

/-- Schematic: actual point type should be the FLT/Mathlib real point type. -/
axiom RealPoint (E : WeierstrassCurve ℚ) : Type

/-- Schematic: actual real base-changed Weierstrass curve. -/
axiom realBaseChange (E : WeierstrassCurve ℚ) : WeierstrassCurve ℝ

/-- Schematic: x-coordinate representative, with the point at infinity handled separately. -/
axiom xCoord (E : WeierstrassCurve ℚ) : RealPoint E → ℝ

/--
Missing theorem 1: positive-level `ΨSq` is nonzero.
This is needed to use finite root sets.
-/
axiom ΨSq_ne_zero_of_pos
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m) :
    (realBaseChange E).ΨSq (m : ℤ) ≠ 0

/--
Missing theorem 2: nonzero `m`-torsion points have x-coordinate in the root set
of the relevant division polynomial.
-/
axiom xCoord_mem_ΨSq_rootSet_of_nsmul_eq_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m)
    {P : RealPoint E} :
    m • P = 0 → P ≠ 0 →
      (xCoord E P) ∈ Polynomial.rootSet ((realBaseChange E).ΨSq (m : ℤ)) ℝ

/--
Missing theorem 3: same x-coordinate gives at most the pair `P,-P`.
Mathlib has the relevant affine point API under
`WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep`, but this must be
connected to the exact FLT point type/notation.
-/
axiom eq_or_eq_neg_of_xCoord_eq
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {P Q : RealPoint E} :
    xCoord E P = xCoord E Q → P = Q ∨ P = -Q

end FLT
```

That is not the final proof; it is the smallest honest interface that the division-polynomial approach needs.

---

## What Mathlib already has for finite fibers

Mathlib's affine point file does have the right two-points-per-`x` idea.  The docs list:

```lean
WeierstrassCurve.Affine.Point.xRep
WeierstrassCurve.Affine.Point.xRep_zero
WeierstrassCurve.Affine.Point.xRep_some
WeierstrassCurve.Affine.Point.xRep_neg
WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep
WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff
```

So after the point type is exactly `W.toAffine.Point`, the finite-fiber part should be straightforward: each `xRep` fiber has at most two points, because two points with the same `xRep` are equal or negatives of each other.

The problem is not fiber finiteness.  The problem is showing that torsion points land in a finite `x`-coordinate set cut out by a nonzero division polynomial.

---

## The theorem that should be added first

The most useful next theorem is not `real_mTorsion_finite` itself.  It is the bridge lemma:

```lean
import Mathlib

namespace WeierstrassCurve

open Polynomial

/--
Target bridge theorem.  Names and point type should be adjusted to the exact
Mathlib point notation in the FLT repo.

For `m > 0`, if a real point `P` is killed by `m` and `P` is not the point at
infinity, then its x-coordinate is a root of `ΨSq m`.
-/
theorem Affine.Point.xRep_mem_rootSet_ΨSq_of_nsmul_eq_zero
    {W : WeierstrassCurve ℝ} [W.IsElliptic] {m : ℕ} (hm : 0 < m)
    {P : W.toAffine.Point}
    (hP : m • P = 0) (hP0 : P ≠ 0) :
    P.xRep ∈ Polynomial.rootSet (W.ΨSq (m : ℤ)) ℝ := by
  -- This is the missing division-polynomial/multiplication-formula theorem.
  -- It is not supplied by `DivisionPolynomial.Basic` at present.
  -- Expected proof ingredients:
  --   * the `ψ`, `Ψ`, `ΨSq`, `Φ`, `φ` definitions;
  --   * coordinate-ring congruence lemmas such as `Affine.CoordinateRing.mk_ψ`;
  --   * multiplication-by-m coordinate formula using `Φ/ΨSq` and `ω/ψ^3`;
  --   * the fact that `m • P = 0` forces the denominator/division polynomial to vanish.
  sorry

end WeierstrassCurve
```

This theorem is exactly where the real work belongs.  Once it exists, `real_mTorsion_finite` is a small set-theory proof.

---

## Expected final theorem after the bridge exists

After the bridge package exists, the proof shape is:

```lean
import Mathlib

namespace FLT

open Polynomial Set

/--
Schematic final theorem.  This is the intended dependency shape, not something
that currently follows from `DivisionPolynomial.Basic` alone.
-/
theorem real_mTorsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) (hm : 0 < m) :
    Set.Finite {P : (E / ℝ).Point | m • P = 0} := by
  -- Let `W` be the real base change of `E`.
  let W : WeierstrassCurve ℝ := E.baseChange ℝ

  -- Let `S` be the m-torsion subset of real points.
  let S : Set (E / ℝ).Point := {P | m • P = 0}

  -- Let `R` be the finite root set of the nonzero division polynomial.
  let R : Set ℝ := Polynomial.rootSet (W.ΨSq (m : ℤ)) ℝ

  have hpoly_ne : W.ΨSq (m : ℤ) ≠ 0 := by
    -- Missing nonzero theorem for positive-level division polynomial.
    exact ΨSq_ne_zero_of_pos E hm

  have hRfinite : R.Finite := by
    -- Exact theorem name may be one of:
    --   Polynomial.finite_rootSet
    --   Polynomial.rootSet_finite
    --   Polynomial.rootSet.finite
    -- depending on the local Mathlib version.
    simpa [R] using (Polynomial.finite_rootSet (p := W.ΨSq (m : ℤ)) hpoly_ne)

  have hx_sub : (fun P : (E / ℝ).Point => P.xRep) '' (S \ {0}) ⊆ R := by
    intro x hx
    rcases hx with ⟨P, hPS, hPx⟩
    rcases hPS with ⟨hPm, hPnot0⟩
    subst x
    exact WeierstrassCurve.Affine.Point.xRep_mem_rootSet_ΨSq_of_nsmul_eq_zero
      (W := W) hm hPm hPnot0

  -- `xRep` has fibers of size at most two, using:
  --   WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep
  -- Therefore `S \ {0}` is finite over the finite root set `R`.
  have hS_nonzero_finite : (S \ {0}).Finite := by
    -- finite image + finite fibers, with each fiber contained in `{P, -P}`
    -- after choosing one point in the fiber.
    sorry

  -- Add back the point at infinity/zero.
  have hzero : ({0} : Set (E / ℝ).Point).Finite := Set.finite_singleton 0
  exact hS_nonzero_finite.union hzero |>.subset (by
    intro P hP
    rcases Classical.em (P = 0) with hP0 | hP0
    · exact Or.inr hP0
    · exact Or.inl ⟨hP, hP0⟩)

end FLT
```

The two `sorry`s in this schematic are intentional markers of missing infrastructure.  The first is the genuine division-polynomial bridge.  The second is routine set theory/fiber finiteness and can be eliminated once the exact point type and `xRep` API are fixed.

---

## Why the requested theorem is not currently a direct Mathlib theorem

The proposed proof outline is mathematically right:

```text
m-torsion point
  -> x-coordinate root of division polynomial
  -> finitely many x-coordinates
  -> at most two points over each x
  -> finite torsion set.
```

But the current API stops before the first arrow.  `DivisionPolynomial.Basic` defines the division polynomials and coordinate-ring congruence statements, but it does not yet provide the multiplication-by-`m` formula or the theorem that killed points make the denominator vanish.

The finite-root and finite-fiber pieces are supported by Mathlib:

```lean
Polynomial.rootSet
Polynomial.roots
Polynomial.card_roots
Polynomial.card_roots'
Polynomial.finite_setOf_isRoot
Set.Finite.of_finite_image
Set.Finite.image
Set.Finite.union
Set.finite_singleton
WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep
WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff
```

The missing API is elliptic-specific:

```lean
m • P = 0 -> P.xRep ∈ rootSet (W.ΨSq (m : ℤ)) ℝ
```

and probably also:

```lean
W.ΨSq (m : ℤ) ≠ 0
```

for `0 < m` over `ℝ`.

## Recommendation

Do not try to prove `real_mTorsion_finite` first.

Add these lemmas in this order:

```lean
import Mathlib

namespace WeierstrassCurve

open Polynomial

/-- Positive-level univariate division polynomial is nonzero. -/
theorem ΨSq_ne_zero_of_pos
    {K : Type*} [Field K] {W : WeierstrassCurve K} [W.IsElliptic]
    {m : ℕ} (hm : 0 < m) :
    W.ΨSq (m : ℤ) ≠ 0 := by
  -- likely proof from leading coefficient / degree of division polynomials
  sorry

/-- Torsion points have x-coordinate among roots of `ΨSq`. -/
theorem Affine.Point.xRep_mem_rootSet_ΨSq_of_nsmul_eq_zero
    {K : Type*} [Field K] {W : WeierstrassCurve K} [W.IsElliptic]
    {m : ℕ} (hm : 0 < m) {P : W.toAffine.Point}
    (hP : m • P = 0) (hP0 : P ≠ 0) :
    P.xRep ∈ Polynomial.rootSet (W.ΨSq (m : ℤ)) K := by
  -- proof from division-polynomial multiplication formula
  sorry

end WeierstrassCurve
```

Once those are available, the requested finiteness theorem is a short wrapper.  Without them, a no-`sorry`, Mathlib-only proof of the exact theorem is not available from `DivisionPolynomial.Basic` alone.
