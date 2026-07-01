# Q2971 dm-codex2: 4-torsion at `tateP3` and the `ψ₄` core

Namespace: `MazurProof.KubertBridgeN12`.

Target: replace the residual

```lean
theorem tatePsi4CoreAt3P_eq_zero_of_origin_order12
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    tatePsi4CoreAt3P b c = 0
```

## Short answer

Mathlib has division-polynomial **definitions** for Weierstrass curves, including the univariate core `preΨ₄`, but I do not know of a current Mathlib theorem that directly turns

```lean
(4 : ℕ) • Q = 0
```

for an affine point `Q` into

```lean
Polynomial.eval Q.x W.preΨ₄ = 0
```

or into bivariate `ψ₄` vanishing. The exposed Mathlib API to use/check is the definition layer, not a ready torsion criterion. Therefore the shortest feasible Lean route is a **direct specialized affine group-law calculation** at

```lean
Q = tateP3 b c hb = (c, b - c).
```

The key identity to prove by `field_simp; ring` is

```lean
D^3 * ψ₂(2Q) = tatePsi4CoreAt3P b c,
D = b - c - c^2,
```

where

```lean
ψ₂(x,y) = 2*y + (1-c)*x - b
```

on the Tate model. From `hOrder`, `4 • Q = 0`; hence `2Q = -2Q`; hence `ψ₂(2Q)=0`; since `D≠0`, the core vanishes.

## 1. Mathlib API probes

Use these imports/probes first:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

#check WeierstrassCurve.preΨ₄
#check WeierstrassCurve.preΨ'_four
#check WeierstrassCurve.preΨ_four
#check WeierstrassCurve.ψ_four
#check WeierstrassCurve.Ψ_four
#check WeierstrassCurve.Φ_four
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
#check WeierstrassCurve.Affine.CoordinateRing.mk_φ
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
```

Expected useful facts from Mathlib:

```lean
-- `W.preΨ₄` is exactly the univariate polynomial
--   2X^6 + b₂X^5 + 5b₄X^4 + 10b₆X^3 + 10b₈X^2
--     + (b₂b₈-b₄b₆)X + (b₄b₈-b₆^2)

-- `W.ψ_four` rewrites `W.ψ 4` to `C W.preΨ₄ * W.ψ₂`.
-- `W.Ψ_four` rewrites `W.Ψ 4` similarly.
```

These are useful, but they are not enough by themselves. The following probes are the sort of theorem we would like, but they are expected to fail unless your local Mathlib has added more API:

```lean
-- expected FAIL in current Mathlib unless locally added:
-- #check WeierstrassCurve.Affine.Point.nsmul_eq_zero_iff_ψ
-- #check WeierstrassCurve.Affine.Point.nsmul_eq_zero_iff_preΨ
-- #check WeierstrassCurve.Affine.Point.divisionPolynomial_eq_zero_of_nsmul_eq_zero
-- #check WeierstrassCurve.Affine.Point.preΨ_eq_zero_of_nsmul_eq_zero
-- #check WeierstrassCurve.ψ_eq_zero_of_nsmul_eq_zero
```

So, unless one of those exists locally, do not spend time hunting for a magic theorem. Prove the specialized `D^3 * ψ₂(2Q) = core` identity.

## 2. Algebra: identify local core with `preΨ₄(c)`

This small theorem is optional but useful for sanity. It uses only Mathlib’s definition of `preΨ₄`.

```lean
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

namespace MazurProof.KubertBridgeN12

open Polynomial

/-- Sanity check: the hand-written core is `preΨ₄` evaluated at `x=c`. -/
theorem tatePsi4CoreAt3P_eq_eval_prePsi4
    (b c : ℚ) :
    tatePsi4CoreAt3P b c =
      Polynomial.eval c ((tateW b c).preΨ₄) := by
  -- If your local names use Greek `Ψ`, this is `WeierstrassCurve.preΨ₄`.
  -- The proof should be purely definitional plus ring normalization.
  simp [tatePsi4CoreAt3P, WeierstrassCurve.preΨ₄,
    tate_b2, tate_b4, tate_b6, tate_b8, tateW]
  ring

end MazurProof.KubertBridgeN12
```

If this theorem fails, first fix the definition-side mismatch. It means either the hand-written `tate_bᵢ` convention or the `tateW` coefficient convention is different from the one assumed in the prompt.

## 3. The direct route: explicit doubling of `Q = 3P`

For the Tate model

```text
y² + (1-c)xy - b y = x³ - b x²,
```

the coefficients are

```text
a1 = 1-c,
a2 = -b,
a3 = -b,
a4 = 0,
a6 = 0.
```

At

```text
Q = (c, b-c),
```

the tangent denominator and numerator are

```text
D = 2y + a1*x + a3 = b - c - c²,
N = 3x² + 2a2*x + a4 - a1*y = 2c² - b*c + c - b.
```

Define the explicit doubled coordinates using the usual affine tangent formula.

```lean
namespace MazurProof.KubertBridgeN12

noncomputable def tateP3DoubleDen (b c : ℚ) : ℚ :=
  b - c - c ^ 2

noncomputable def tateP3DoubleSlopeNum (b c : ℚ) : ℚ :=
  2 * c ^ 2 - b * c + c - b

noncomputable def tateP3DoubleSlope (b c : ℚ) : ℚ :=
  tateP3DoubleSlopeNum b c / tateP3DoubleDen b c

/-- x-coordinate of `2*(c,b-c)` on the Tate model. -/
noncomputable def tateP3DoubleX (b c : ℚ) : ℚ :=
  let λ := tateP3DoubleSlope b c
  λ ^ 2 + (1 - c) * λ + b - 2 * c

/-- y-coordinate of `2*(c,b-c)` on the Tate model. -/
noncomputable def tateP3DoubleY (b c : ℚ) : ℚ :=
  let λ := tateP3DoubleSlope b c
  let x2 := tateP3DoubleX b c
  let ν := (b - c) - λ * c
  - (λ + (1 - c)) * x2 - ν + b

end MazurProof.KubertBridgeN12
```

The sign in `tateP3DoubleY` is the generalized Weierstrass negation formula: if the tangent line has `y = λx + ν`, the third intersection point has y-coordinate `λ*x2 + ν`, and the group sum has y-coordinate

```text
-(λ*x2 + ν) - a1*x2 - a3 = -(λ+a1)*x2 - ν + b.
```

## 4. Prove the explicit doubling formula

This is the first actual group-law theorem to attack if not already available.

```lean
namespace MazurProof.KubertBridgeN12

/-- Nonsingularity proof for the explicit `2*tateP3` point.  Usually this follows
from `hDelta` once the point equation is checked; keep it local if point constructors need it. -/
theorem tateP3Double_nonsingular
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hD : tateP3DoubleDen b c ≠ 0) :
    WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (tateW b c))
      (tateP3DoubleX b c) (tateP3DoubleY b c) := by
  -- Try direct simplification first:
  --   simp [WeierstrassCurve.Affine.Nonsingular, tateW,
  --     tateP3DoubleX, tateP3DoubleY, tateP3DoubleSlope,
  --     tateP3DoubleSlopeNum, tateP3DoubleDen, hb, hD, hDelta]
  --   field_simp [hb, hD]
  --   ring
  -- If this is painful, avoid a named point constructor and prove the coordinate identity
  -- directly inside the doubling theorem below.
  by_cases h : True
  · -- replace this branch by the direct proof in the local file
    classical
    exact (by
      -- local implementation target
      aesop)

noncomputable def tateP3DoublePoint
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hD : tateP3DoubleDen b c ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some
    (tateP3DoubleX b c) (tateP3DoubleY b c)
    (tateP3Double_nonsingular b c hb hDelta hD)

/-- Explicit formula for doubling `Q=tateP3`. -/
theorem tate_two_nsmul_tateP3_eq_explicit
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hD : tateP3DoubleDen b c ≠ 0) :
    (2 : ℕ) • tateP3 b c hb =
      tateP3DoublePoint b c hb hDelta hD := by
  -- Use the affine addition/doubling formula.  The tangent denominator is exactly `D`.
  -- Typical shape:
  --   change tateP3 b c hb + tateP3 b c hb = _
  --   ext <;>
  --     simp [tateP3, tateP3DoublePoint, tateP3DoubleX, tateP3DoubleY,
  --       tateP3DoubleSlope, tateP3DoubleSlopeNum, tateP3DoubleDen,
  --       tateW, hb, hD] <;>
  --     field_simp [hb, hD] <;>
  --     ring
  -- If Mathlib splits addition cases, add facts:
  --   have hden : 2*(b-c) + (1-c)*c - b ≠ 0 := by simpa [tateP3DoubleDen] using hD
  -- and include `hden` in `simp`.
  change tateP3 b c hb + tateP3 b c hb =
    tateP3DoublePoint b c hb hDelta hD
  ext <;>
    simp [tateP3, tateP3DoublePoint, tateP3DoubleX, tateP3DoubleY,
      tateP3DoubleSlope, tateP3DoubleSlopeNum, tateP3DoubleDen,
      tateW, hb, hD] <;>
    field_simp [hb, hD] <;>
    ring

end MazurProof.KubertBridgeN12
```

If the displayed `tateP3Double_nonsingular` placeholder is too annoying, do not introduce `tateP3DoublePoint`; instead prove a theorem that unfolds `(2 : ℕ) • tateP3 ...` and extracts the coordinate values directly. The important algebra is the `field_simp [hD]; ring` calculation.

## 5. Key polynomial identity: `D^3 * ψ₂(2Q) = core`

This is the smallest algebra lemma that replaces the missing division-polynomial torsion API.

```lean
namespace MazurProof.KubertBridgeN12

/-- Specialized division-polynomial identity at `Q=(c,b-c)`.

This is the concrete replacement for a missing theorem of the form
`4 • Q = 0 -> preΨ₄(Q.x)=0`. -/
theorem tateP3Double_psi2_mul_den_cube_eq_core
    (b c : ℚ) (hD : tateP3DoubleDen b c ≠ 0) :
    (tateP3DoubleDen b c) ^ 3 *
      (2 * tateP3DoubleY b c + (1 - c) * tateP3DoubleX b c - b)
      = tatePsi4CoreAt3P b c := by
  -- This should be a pure rational-function calculation.
  -- The left side is `D^3 * ψ₂(2Q)`, while the right side is `preΨ₄(c)`.
  unfold tateP3DoubleY tateP3DoubleX tateP3DoubleSlope
    tateP3DoubleSlopeNum tateP3DoubleDen
  unfold tatePsi4CoreAt3P tate_b2 tate_b4 tate_b6 tate_b8
  field_simp [hD]
  ring

end MazurProof.KubertBridgeN12
```

If `ring` produces the negative of the core, change the theorem statement to

```lean
= - tatePsi4CoreAt3P b c
```

and adjust the final proof by `neg_eq_zero.mp`. The standard convention predicts the positive sign above.

## 6. Turning self-negation into `ψ₂=0`

For a point `(x,y)` on the Tate model, equality to its negative gives

```text
2y + (1-c)x - b = 0.
```

```lean
namespace MazurProof.KubertBridgeN12

private theorem eq_neg_self_of_two_nsmul_eq_zero
    {G : Type*} [AddGroup G] {R : G}
    (h : (2 : ℕ) • R = 0) :
    R = -R := by
  rw [two_nsmul] at h
  exact eq_neg_iff_add_eq_zero.mpr h

/-- If an explicit affine Tate point equals its negative, then its `ψ₂` value is zero. -/
theorem tate_some_eq_neg_self_psi2_eq_zero
    (b c x y : ℚ)
    (hxy : WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (tateW b c)) x y)
    (hself :
      WeierstrassCurve.Affine.Point.some x y hxy =
        - WeierstrassCurve.Affine.Point.some x y hxy) :
    2 * y + (1 - c) * x - b = 0 := by
  -- Negation on `y² + a1xy + a3y = ...` is `(x, -y-a1*x-a3)`.
  -- Here `a1=1-c`, `a3=-b`.
  -- Typical proof:
  --   simpa [tateW] using congrArg WeierstrassCurve.Affine.Point.y hself
  -- If there is no `.y` projection, use `ext`/`cases` on point equality and simplify.
  simpa [tateW] using congrArg WeierstrassCurve.Affine.Point.y hself

end MazurProof.KubertBridgeN12
```

If there is no `Point.y` projection in the local API, use this proof pattern instead:

```lean
  -- after `simp [WeierstrassCurve.Affine.Point.neg, tateW] at hself`,
  -- the remaining equality should be `y = -y - (1-c)*x + b`.
  -- `linear_combination` or `ring_nf` closes the target.
```

## 7. Main theorem skeleton

This is the desired residual replacement.

```lean
namespace MazurProof.KubertBridgeN12

theorem tatePsi4CoreAt3P_eq_zero_of_origin_order12
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    tatePsi4CoreAt3P b c = 0 := by
  have hD : tateP3DoubleDen b c ≠ 0 := by
    simpa [tateP3DoubleDen] using
      tate_sixP_den_ne_zero_of_origin_order12 b c hb hDelta hOrder

  let P := tateOriginAffine b c hb
  let Q := tateP3 b c hb

  have h3P : (3 : ℕ) • P = Q := by
    simpa [P, Q] using tate_three_nsmul_origin_eq b c hb hDelta

  have h12P : (12 : ℕ) • P = 0 := by
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [hOrder])

  have h4Q : (4 : ℕ) • Q = 0 := by
    rw [← h3P]
    simpa [nsmul_nsmul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h12P

  have h2twoQ : (2 : ℕ) • ((2 : ℕ) • Q) = 0 := by
    simpa [nsmul_nsmul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h4Q

  have htwoQ_self : (2 : ℕ) • Q = - ((2 : ℕ) • Q) :=
    eq_neg_self_of_two_nsmul_eq_zero h2twoQ

  have htwoQ_explicit :
      (2 : ℕ) • Q = tateP3DoublePoint b c hb hDelta hD := by
    simpa [Q] using tate_two_nsmul_tateP3_eq_explicit b c hb hDelta hD

  have hpsi2 :
      2 * tateP3DoubleY b c + (1 - c) * tateP3DoubleX b c - b = 0 := by
    rw [htwoQ_explicit] at htwoQ_self
    exact tate_some_eq_neg_self_psi2_eq_zero
      b c (tateP3DoubleX b c) (tateP3DoubleY b c)
      (tateP3Double_nonsingular b c hb hDelta hD)
      htwoQ_self

  have hcore := tateP3Double_psi2_mul_den_cube_eq_core b c hD
  calc
    tatePsi4CoreAt3P b c
        = (tateP3DoubleDen b c) ^ 3 *
            (2 * tateP3DoubleY b c + (1 - c) * tateP3DoubleX b c - b) := hcore.symm
    _ = 0 := by rw [hpsi2, mul_zero]

end MazurProof.KubertBridgeN12
```

If `addOrderOf_dvd_iff_nsmul_eq_zero.mp` has the opposite direction in your pinned Mathlib, swap `.mp`/`.mpr`; the intended local fact is exactly “`addOrderOf P ∣ 12` implies `12 • P = 0`.”

## 8. Even shorter fallback without point constructors

If `tateP3DoublePoint`/nonsingularity causes constructor friction, use a single specialized theorem that extracts `ψ₂(2Q)=0` directly:

```lean
theorem tateP3Double_psi2_eq_zero_of_four_nsmul
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hD : tateP3DoubleDen b c ≠ 0)
    (h4Q : (4 : ℕ) • tateP3 b c hb = 0) :
    2 * tateP3DoubleY b c + (1 - c) * tateP3DoubleX b c - b = 0 := by
  -- Prove by unfolding the affine addition formula for `2 • tateP3` and using
  -- `2 • (2 • Q)=0 -> 2Q=-2Q`.
  -- This avoids naming the explicit point/nonsingularity theorem separately.
  -- The proof body is still the same two calculations:
  --   1. `2Q` has coordinates `tateP3DoubleX/Y` by `field_simp [hD]; ring`.
  --   2. `2Q=-2Q` gives the Tate `ψ₂` equation.
  ...
```

Then main theorem becomes:

```lean
  have hpsi2 := tateP3Double_psi2_eq_zero_of_four_nsmul b c hb hDelta hD h4Q
  exact by
    have hcore := tateP3Double_psi2_mul_den_cube_eq_core b c hD
    rw [← hcore, hpsi2, mul_zero]
```

This fallback is often easier if Mathlib’s `Affine.Point.some` proof terms make rewriting noisy.

## 9. Bottom line

Use Mathlib’s division-polynomial module for the **definition** of `preΨ₄` and as a sanity check, but do not depend on a nonexistent torsion criterion theorem. The proof should be a specialized affine calculation:

```text
hOrder=12
  -> 12P=0
  -> 4(3P)=0
  -> 2(2(3P))=0
  -> 2(3P) = -2(3P)
  -> ψ₂(2(3P))=0
  -> D^3 * ψ₂(2(3P)) = preΨ₄(c) = tatePsi4CoreAt3P b c
  -> tatePsi4CoreAt3P b c = 0.
```

The two Lean lemmas to implement first are:

```lean
tate_two_nsmul_tateP3_eq_explicit
tateP3Double_psi2_mul_den_cube_eq_core
```

After those compile, the final `tatePsi4CoreAt3P_eq_zero_of_origin_order12` is a short order-theory wrapper.
