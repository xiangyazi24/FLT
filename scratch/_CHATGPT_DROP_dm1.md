# Q322 (dm1): exact Lean `linear_combination` proof for the general-`m` `addX` identity

## Main point

Use the residual form of each input identity.  With

```text
Hφ = φ_m - (X*ψ_m² - ψ_{m+1}*ψ_{m-1}) = 0,
```

the exact coefficients are:

```text
c₁ = -ψ₂
c₂ = -1
c₃ = ψ_m
c₄ = C(4X² + b₂X + b₄)*ψ_m² + 2*C(X)*φ_m - 2*C(X)*ψ_{m-1}*ψ_{m+1}.
```

For the `Hmiss` version using `C W.Ψ₂Sq`, there is no `HF` term.  The `-4*ψ_m^4` coefficient only appears if `Hmiss` is stated with `ψ₂²` instead of `C W.Ψ₂Sq`.

The Lean code below is written as a self-contained theorem over `K[X][Y]`.  I use an unfolded `addX_unfolded` definition to avoid fighting `W.map (algebraMap K K[X][Y])` coercions.  It is exactly Mathlib’s `Jacobian.addX` specialized to

```text
P = [C X, Y, 1],
Q = [φ_m, ω_m, ψ_m].
```

If your local file already has `W.toPoly.toJacobian.addX genericAffineRep (W.divPolyRep m)`, prove one small unfold lemma equating it with `addX_unfolded` and then rewrite before applying the theorem below.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Generic affine point `[X,Y,1]` as a bivariate Jacobian-coordinate representative. -/
private def genericAffineRep : Fin 3 → K[X][Y] :=
  ![C X, Y, 1]

/-- Projective representative `[φ_m, ω_m, ψ_m]`, where `omegaP` is the bivariate `ω`. -/
private def divPolyRep (omegaP : ℤ → K[X][Y]) (m : ℤ) : Fin 3 → K[X][Y] :=
  ![W.φ m, omegaP m, W.ψ m]

/-- `Jacobian.addX` unfolded for `P=[X,Y,1]` and `Q=[φ_m,ω_m,ψ_m]`. -/
private def addX_unfolded (omegaP : ℤ → K[X][Y]) (m : ℤ) : K[X][Y] :=
  C X * W.φ m ^ 2
    - 2 * Y * omegaP m * W.ψ m
    + (C X) ^ 2 * W.φ m * W.ψ m ^ 2
    - C (C W.a₁) * C X * omegaP m * W.ψ m
    - C (C W.a₁) * Y * W.φ m * W.ψ m ^ 2
    + 2 * C (C W.a₂) * C X * W.φ m * W.ψ m ^ 2
    - C (C W.a₃) * omegaP m * W.ψ m
    - C (C W.a₃) * Y * W.ψ m ^ 4
    + C (C W.a₄) * W.φ m * W.ψ m ^ 2
    + C (C W.a₄) * C X * W.ψ m ^ 4
    + 2 * C (C W.a₆) * W.ψ m ^ 4

/-- The `Hmiss`/Ward residual in the `C W.Ψ₂Sq` normalization. -/
private def HmissΨ (m : ℤ) : K[X][Y] :=
  W.ψ (m - 1) ^ 2 * W.ψ (m + 2)
    + W.ψ (m - 2) * W.ψ (m + 1) ^ 2
    + W.ψ m ^ 3 * C W.Ψ₂Sq
    - W.ψ (m - 1) * W.ψ m * W.ψ (m + 1)
        * C (6 * X ^ 2 + C W.b₂ * X + C W.b₄)

/-- The coefficient of the `φ_m` definition residual. -/
private def addX_c₄ (m : ℤ) : K[X][Y] :=
  C (4 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.ψ m ^ 2
    + 2 * C X * W.φ m
    - 2 * C X * W.ψ (m - 1) * W.ψ (m + 1)

/-- Raw symbolic `linear_combination` identity for the general `addX` step.

This theorem assumes the four residual identities as hypotheses.  It is the exact Lean form of
Q317’s CAS identity. -/
theorem addX_projective_general_from_residuals
    (omegaP : ℤ → K[X][Y]) (m : ℤ)
    (hω :
      (2 : K[X][Y]) * W.ψ m * omegaP m
        - (W.ψ (2 * m)
            - W.ψ m ^ 2 * (C (C W.a₁) * W.φ m + C (C W.a₃) * W.ψ m ^ 2)) = 0)
    (heven :
      W.ψ (2 * m) * W.ψ₂
        - (W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2)
            - W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2) = 0)
    (hmiss : W.HmissΨ m = 0)
    (hφ : W.φ m - (C X * W.ψ m ^ 2 - W.ψ (m + 1) * W.ψ (m - 1)) = 0) :
    (2 : K[X][Y])
      * (W.addX_unfolded omegaP m - W.ψ (m - 1) ^ 2 * W.φ (m + 1)) = 0 := by
  linear_combination (norm := ring_nf [addX_unfolded, HmissΨ, addX_c₄])
    (-W.ψ₂) * hω
      - heven
      + W.ψ m * hmiss
      + W.addX_c₄ m * hφ

/-- Convenient wrapper when `ω` is known by the usual equality rather than residual form. -/
theorem addX_projective_general
    (omegaP : ℤ → K[X][Y]) (m : ℤ)
    (hωeq :
      (2 : K[X][Y]) * W.ψ m * omegaP m =
        W.ψ (2 * m)
          - W.ψ m ^ 2 * (C (C W.a₁) * W.φ m + C (C W.a₃) * W.ψ m ^ 2))
    (hmiss : W.HmissΨ m = 0) :
    (2 : K[X][Y])
      * (W.addX_unfolded omegaP m - W.ψ (m - 1) ^ 2 * W.φ (m + 1)) = 0 := by
  refine W.addX_projective_general_from_residuals omegaP m ?hω ?heven hmiss ?hφ
  · exact sub_eq_zero.mpr hωeq
  · exact sub_eq_zero.mpr (W.ψ_even m)
  · rw [WeierstrassCurve.φ]
    ring

end

end WeierstrassCurve
```

## If your `Hmiss` theorem is the `ψ₂²` version

If the available theorem is

```lean
Hmissψ₂ m =
  ψ_{m-1}² ψ_{m+2} + ψ_{m-2} ψ_{m+1}²
    + ψ_m³ ψ₂²
    - ψ_{m-1} ψ_m ψ_{m+1} C(6X²+b₂X+b₄) = 0,
```

then replace `HmissΨ` by `Hmissψ₂` and add the curve-equation term coefficient

```lean
-4 * W.ψ m ^ 4
```

against the identity

```lean
W.ψ₂ ^ 2 - C W.Ψ₂Sq - 4 * W.toAffine.polynomial = 0
```

which is exactly Mathlib’s `C_Ψ₂Sq` rearranged.

The `C W.Ψ₂Sq` version above is cleaner because the `HF` coefficient is zero.

## Coercion note

If you want the theorem literally with Mathlib’s `Jacobian.addX`, define your polynomial-coefficient curve by mapping coefficients into `K[X][Y]`:

```lean
private abbrev Wbivar : WeierstrassCurve.Jacobian K[X][Y] :=
  (W.map (algebraMap K K[X][Y])).toJacobian
```

Then prove the unfold lemma:

```lean
private theorem addX_unfolded_eq_jacobian_addX
    (omegaP : ℤ → K[X][Y]) (m : ℤ) :
    W.addX_unfolded omegaP m =
      Wbivar W |>.addX (genericAffineRep (K := K)) (W.divPolyRep omegaP m) := by
  rw [addX_unfolded, genericAffineRep, divPolyRep, WeierstrassCurve.Jacobian.addX]
  simp [Wbivar, WeierstrassCurve.map]
  ring
```

Depending on the exact local name for `toPoly`, your version may be even shorter:

```lean
rw [addX_unfolded, genericAffineRep, divPolyRep, Jacobian.addX]
ring_nf
```

Once this unfold lemma is in place, rewrite the goal to `addX_unfolded` and apply `addX_projective_general`.
