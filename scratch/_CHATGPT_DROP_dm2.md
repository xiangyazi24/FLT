# Q119 (dm2): SEAM1 rootwise crux — what is still genuinely missing

Target theorem:

```lean
theorem dual_root_implies_tangent_zero [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y) (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ W n 1 = 0
```

## Executive answer

I cannot honestly give a closed proof of this theorem from only the currently listed Mathlib/repo lemmas. The missing item is **not** the dual-number Taylor engine, the affine jet equation, the `ψ₂` unit fact, or `TangentO.nsmul₁ = n`. Those are local and already handled.

The genuinely missing item is a **raw coordinate multiplication-by-`n` theorem over the non-field ring `DualNumber K`**. More precisely, the proof needs a theorem saying that a dual-number affine point satisfying the curve equation, with `ψ₂` a unit, and satisfying the reduced equation `preΨ'_n(X)=0`, has `[n]` equal to the zero tangent in the projective `O` chart. This is the field-vs-ring bridge. It cannot be replaced by `Jacobian.Point (DualNumber K)` because that type’s group law is field-only.

The concrete proof strategy below gives the exact missing theorem, the raw coordinate objects it should use, and the final assembly. Do **not** add it as an axiom in production; prove it from the raw division-polynomial coordinate formula for `[n]` over a commutative ring. Once that theorem exists, `dual_root_implies_tangent_zero` is a short proof.

## Why `hrootε` alone is not a group-law statement

`hrootε` has type:

```lean
hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0
```

It says that the **reduced univariate division polynomial** vanishes at the dual x-coordinate `x + ε`.

To conclude that the infinitesimal point is killed by `[n]`, one must use the division-polynomial coordinate formula for multiplication-by-`n`. Classically, for a non-2 point, the vanishing of the full `ψ_n` forces the projective `[n]` coordinates to land at `O`. In projective form this is represented schematically by coordinates of the shape

```text
[n](X,Y) = [ φ_n(X,Y) ψ_n(X,Y) : ω_n(X,Y) : ψ_n(X,Y)^3 ].
```

If `ψ_n = 0` and the middle coordinate is a unit, this is `[0:1:0]`. For the first-order tangent, one additionally needs the `X/Y` tangent coordinate at `O` to be zero.

Mathlib’s current division-polynomial file has `ψ`, `Ψ`, `φ`, `Φ`, and coordinate-ring congruences, but not a reusable raw `ω_n` / projective `[n]` coordinate theorem over arbitrary commutative rings. That is exactly the missing bridge.

## The exact theorem to add, not as an axiom

The smallest useful theorem is the following. It is intentionally formulated over the raw dual-number affine lift and concludes directly in the `TangentO` chart, so it avoids building a full point group over `DualNumber K`.

```lean
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable

noncomputable section

open Polynomial
open scoped Polynomial DualNumber

namespace WeierstrassCurve

namespace SEAM1

variable {K : Type*} [Field K]

/-- The exact raw-coordinate bridge that must be proved from division-polynomial multiplication
formulas over `DualNumber K`.

Do not state this as an axiom in the production file. It is the missing lemma whose proof should
be built from:
* the affine dual lift `Pε = (x+ε, y+ε*slope)`;
* `AffineJet.equation_dual_lift_of_polynomialY_ne_zero`;
* the fact that the lifted `ψ₂ = W_Y(Pε)` is a unit because its scalar part is `hY`;
* `W.map_preΨ'` and the coordinate-ring congruences `mk_ψ`, `mk_Ψ_sq`, `mk_φ`;
* the raw projective/Jacobian multiplication-by-`n` coordinate formula over a commutative ring.
-/
theorem preΨ'_dual_root_to_OJet_zero_rawCoord
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ W n 1 = 0 := by
  -- This is the real remaining proof. See the proof plan below.
  sorry

/-- Once `preΨ'_dual_root_to_OJet_zero_rawCoord` is proved, the theorem requested in Q119 is
literally this wrapper. -/
theorem dual_root_implies_tangent_zero
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ W n 1 = 0 := by
  exact preΨ'_dual_root_to_OJet_zero_rawCoord
    (W := W) (n := n) hn hcurve hY hrootε

end SEAM1

end WeierstrassCurve
```

The wrapper is not the problem. The theorem `preΨ'_dual_root_to_OJet_zero_rawCoord` is.

## Concrete proof plan for the missing raw-coordinate theorem

Inside `preΨ'_dual_root_to_OJet_zero_rawCoord`, do the following.

### 1. Construct the dual-number point on the curve

Use the existing objects from your SEAM1 branch:

```lean
let Xε : DualNumber K := MultipleRootBridge.xε x
let Yε : DualNumber K := MultipleRootBridge.yε W x y
```

Then:

```lean
have hPε_curve :
    (W.toAffine.baseChange (DualNumber K)).Equation Xε Yε := by
  exact MultipleRootBridge.affine_dual_point_equation
    (W := W) hcurve hY
```

This step is already available from `AffineJet.equation_dual_iff` and the y-lift lemma.

### 2. Prove the lifted `ψ₂` is a unit

The lifted `ψ₂` is `W_Y(Xε,Yε)`:

```lean
let ψ₂ε : DualNumber K :=
  (W.toAffine.baseChange (DualNumber K)).polynomialY.evalEval Xε Yε
```

Its scalar part is the original `W_Y(x,y)`:

```lean
have hψ₂ε_fst : TrivSqZeroExt.fst ψ₂ε = W.toAffine.polynomialY.evalEval x y := by
  -- unfold `ψ₂ε`, `Xε`, `Yε`; use `Affine.evalEval_polynomialY`; simp.
  simp [ψ₂ε, Xε, Yε, MultipleRootBridge.xε, MultipleRootBridge.yε,
    WeierstrassCurve.Affine.evalEval_polynomialY]
```

Then use the standard dual-number unit lemma, which you should add if absent:

```lean
lemma dualNumber_isUnit_of_fst_ne_zero (z : DualNumber K)
    (hz : TrivSqZeroExt.fst z ≠ 0) : IsUnit z := by
  -- Explicit inverse: if z = a + εb and a ≠ 0, inverse is a⁻¹ - ε*(b*a⁻²).
  -- Prove with `TrivSqZeroExt.ext`; `field_simp [hz]`; `ring`.
  sorry
```

Thus:

```lean
have hψ₂ε_unit : IsUnit ψ₂ε := by
  apply dualNumber_isUnit_of_fst_ne_zero
  simpa [hψ₂ε_fst] using hY
```

This is exactly where `hY` is consumed.

### 3. Upgrade reduced `preΨ'` vanishing to full `ψ_n` vanishing

This is the non-2 branch.

For odd `n`, `ψ_n` corresponds to `preΨ'_n` directly.

For even `n`, the full `ψ_n` has a `ψ₂` factor and the reduced polynomial is `preΨ'_n`; since `ψ₂ε` is a unit, the reduced vanishing is equivalent to the full vanishing. In practice, the direction you need is just:

```lean
have hψnε : evalBivariateAt Xε Yε ((W.baseChange (DualNumber K)).ψ (n : ℤ)) = 0 := by
  -- Use `W.map_preΨ'`, `WeierstrassCurve.Ψ`, and `Affine.CoordinateRing.mk_ψ`/`mk_Ψ_sq`.
  -- Split by parity if needed:
  --   odd: `Ψ n = C (preΨ n)`;
  --   even: `Ψ n = C (preΨ n) * ψ₂` and `ψ₂ε` is a unit.
  sorry
```

A good lemma signature for this step is:

```lean
theorem full_ψ_eval_zero_of_preΨ'_eval_zero_of_ψ₂_unit
    (W : WeierstrassCurve K) {n : ℕ} {A : Type*} [CommRing A] [Algebra K A]
    {X Y : A}
    (hcurve : (W.toAffine.baseChange A).Equation X Y)
    (hψ₂_unit : IsUnit ((W.toAffine.baseChange A).polynomialY.evalEval X Y))
    (hpre : aeval X ((W.preΨ' n).map (algebraMap K A)) = 0) :
    -- use the actual bivariate-evaluation expression used in the repo
    evalBivariateAt X Y ((W.baseChange A).ψ (n : ℤ)) = 0 := by
  sorry
```

Use your repo’s actual bivariate evaluation notation; the public Mathlib files use `evalEval` for `R[X][Y]`.

### 4. Apply the raw projective multiplication-by-`n` coordinate theorem

This is the essential missing theorem. It should be stated once, independent of dual numbers.

A robust signature is:

```lean
/-- Raw projective multiplication formula on the non-2 affine chart.

For an affine point `(X,Y)` over a commutative ring `A`, if the curve equation holds and `ψ₂(X,Y)`
is a unit, then vanishing of the full `ψ_n` forces the raw projective `[n]` output to be equivalent
to `O` with tangent coordinate zero.
-/
theorem raw_nsmul_affine_nonTwo_of_ψ_eq_zero
    (W : WeierstrassCurve K) {A : Type*} [CommRing A] [Algebra K A]
    {n : ℕ} {X Y : A}
    (hcurve : (W.toAffine.baseChange A).Equation X Y)
    (hψ₂_unit : IsUnit ((W.toAffine.baseChange A).polynomialY.evalEval X Y))
    (hψn : evalBivariateAt X Y ((W.baseChange A).ψ (n : ℤ)) = 0) :
    -- exact conclusion should use the repo's raw `[n]` output object.
    rawNsmulTangentAtO W n X Y = 0 := by
  sorry
```

For SEAM1, instantiate `A = DualNumber K`, `X = Xε`, `Y = Yε`. The conclusion should be identified with:

```lean
TangentO.nsmul₁ W n 1 = 0
```

If the repo does not yet have `rawNsmulTangentAtO`, define the **minimal** object instead of a full raw nsmul point:

```lean
/-- The first-order `O`-chart coordinate of the raw `[n]` output, when the output lies at infinity. -/
noncomputable def rawNsmulTangentAtO
    (W : WeierstrassCurve K) (n : ℕ) (X Y : DualNumber K) : K :=
  -- Choose the actual projective coordinate expression used by the division-polynomial formula.
  -- For the classical `[φ_n ψ_n : ω_n : ψ_n^3]`, this is the ε-coefficient of Xcoord/Ycoord.
  sorry
```

The theorem must then prove this object agrees with `TangentO.nsmul₁ W n 1` for the specific infinitesimal input constructed from the multiple root.

### 5. Why raw `addXYZ`/`dblXYZ` alone are not enough

The public raw `Jacobian.addXYZ` and `Jacobian.dblXYZ` are denominator-cleared formulas. They are stated over `CommRing`, and the following map/base-change lemmas exist:

```lean
WeierstrassCurve.Jacobian.map_dblXYZ
WeierstrassCurve.Jacobian.map_addXYZ
WeierstrassCurve.Jacobian.baseChange_dblXYZ
WeierstrassCurve.Jacobian.baseChange_addXYZ
```

But using them recursively over `DualNumber K` is dangerous: the scale factors that are nonzero over fields may become nilpotent and nonunit over dual numbers. In exactly the infinitesimal cases needed here, a denominator-cleared formula can collapse to the zero triple even though the corresponding projective point has a valid first-order limit.

Therefore the theorem should **not** be proved by defining `[n]` recursively with `addXYZ`/`dblXYZ` over `DualNumber K` unless every scaling factor is separately proved to be a unit. The safer route is the division-polynomial projective coordinate formula.

## Minimal missing theorem, in final desired form

If you want the smallest possible SEAM1-facing theorem, use this exact statement:

```lean
/-- Non-2 reduced dual root forces zero tangent output under `[n]`.

This is the only raw-coordinate theorem needed by `dual_root_implies_tangent_zero`.
-/
theorem preΨ'_dual_root_to_OJet_zero_rawCoord
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ W n 1 = 0 := by
  let Xε : DualNumber K := MultipleRootBridge.xε x
  let Yε : DualNumber K := MultipleRootBridge.yε W x y

  have hPε_curve :
      (W.toAffine.baseChange (DualNumber K)).Equation Xε Yε := by
    simpa [Xε, Yε] using
      MultipleRootBridge.affine_dual_point_equation
        (W := W) (x := x) (y := y) hcurve hY

  let ψ₂ε : DualNumber K :=
    (W.toAffine.baseChange (DualNumber K)).polynomialY.evalEval Xε Yε

  have hψ₂ε_fst : TrivSqZeroExt.fst ψ₂ε = W.toAffine.polynomialY.evalEval x y := by
    simp [ψ₂ε, Xε, Yε, MultipleRootBridge.xε, MultipleRootBridge.yε,
      WeierstrassCurve.Affine.evalEval_polynomialY]

  have hψ₂ε_unit : IsUnit ψ₂ε := by
    apply dualNumber_isUnit_of_fst_ne_zero
    simpa [hψ₂ε_fst] using hY

  have hfullψ :
      evalBivariateAt Xε Yε ((W.baseChange (DualNumber K)).ψ (n : ℤ)) = 0 := by
    exact full_ψ_eval_zero_of_preΨ'_eval_zero_of_ψ₂_unit
      (W := W) (n := n) hPε_curve hψ₂ε_unit hrootε

  exact raw_nsmul_affine_nonTwo_ψ_zero_tangent
    (W := W) (n := n) (X := Xε) (Y := Yε)
    hPε_curve hψ₂ε_unit hfullψ
```

Replace `evalBivariateAt` with the repo’s actual bivariate evaluation expression, likely `evalEval Xε Yε` for `K[X][Y]`. Replace `raw_nsmul_affine_nonTwo_ψ_zero_tangent` with the chosen theorem name.

This is the concrete proof. The two helper theorems in it are not optional conveniences; they are exactly the missing multiplication-by-`n` coordinate content.

## What the raw multiplication theorem should prove internally

Internally, prove a projective coordinate formula for `[n]` over `A`:

```text
[n](X,Y) = [ φ_n(X,Y) ψ_n(X,Y) : ω_n(X,Y) : ψ_n(X,Y)^3 ]
```

on the non-2 affine chart, or the equivalent reduced-`preΨ'` version. Then under `ψ_n = 0`:

```text
X_output = 0,
Z_output = 0,
Y_output is a unit.
```

The unit of `Y_output` is the only subtle point. It is classically supplied by the same normalization that makes the projective formula represent `O` when `ψ_n = 0`. If `ω_n` is not yet defined in Mathlib, define only the part needed here:

```lean
/-- Middle projective coordinate of `[n]` on the non-2 affine chart. -/
noncomputable def omegaLike (W : WeierstrassCurve K) (n : ℕ) : K[X][Y] := ...
```

and prove:

```lean
theorem omegaLike_unit_at_nonTwo_ψ_zero
    {A : Type*} [CommRing A] [Algebra K A] {X Y : A}
    (hcurve : ...)
    (hψ₂_unit : IsUnit ...)
    (hψn : evalEval X Y ((W.baseChange A).ψ (n : ℤ)) = 0) :
    IsUnit (evalEval X Y ((omegaLike W n).map ...))
```

For the final tangent-zero conclusion, you only need `X_output = 0` and `Y_output` a unit.

## Why `hn : (n : K) ≠ 0` appears in this theorem

The bridge theorem `preΨ'_dual_root_to_OJet_zero_rawCoord` itself may not mathematically need `hn`; it says a dual reduced `n`-division root gives zero `[n]` output tangent. I would keep `hn` in the statement only because the surrounding root dictionary and final contradiction already carry it.

The actual contradiction is:

```lean
have hzero : TangentO.nsmul₁ W n 1 = 0 := dual_root_implies_tangent_zero ...
have hlin  : TangentO.nsmul₁ W n 1 = (n : K) := by
  simpa using TangentO.nsmul₁_eq_natCast_mul (W := W) n (1 : K)
exact hn (by simpa [hlin] using hzero)
```

So `hn` is consumed by the final assembly, not by the raw coordinate bridge.

## Final assessment

The requested theorem is exactly the point where the project needs one more real algebraic theorem: a raw division-polynomial multiplication formula over commutative rings, specialized to dual numbers/non-2 points. All local first-order ingredients are done. There is no valid Lean shortcut through `Jacobian.Point (DualNumber K)`, and recursive `addXYZ` over `DualNumber K` is not safe unless every cleared denominator is tracked as a unit.

The next implementation step should therefore be:

```lean
theorem raw_nsmul_affine_nonTwo_ψ_zero_tangent
    ... : TangentO.nsmul₁ W n 1 = 0
```

proved from a projective division-polynomial coordinate formula, not from the field-only point group.
