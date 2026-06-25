# Q318 (dm2): Deriving `Hmiss` from `mk_invariant_descended`

CAS `Hmiss`:

```text
ψ_{m-1}² ψ_{m+2}
+ ψ_{m-2} ψ_{m+1}²
+ ψ_m³ Ψ₂Sq
- ψ_{m-1} ψ_m ψ_{m+1} · (6X² + b₂X + b₄)
= 0              in the affine coordinate ring.
```

`mk_invariant_descended` says:

```text
mk(Ψ₃ · (ψ_{m+2}ψ_{m-1}² + ψ_{m+1}²ψ_{m-2} + ψ₂²ψ_m³))
  = mk((preΨ₄ + ψ₂⁴) · (ψ_{m+1}ψ_mψ_{m-1})).
```

## CAS verification of the key coefficient identity

The needed identity is true **modulo the `b`-relation**.  More precisely,

```text
Ψ₃ · (6X²+b₂X+b₄) - (preΨ₄ + Ψ₂Sq²)
  = X² · (b₂b₆ - b₄² - 4b₈).
```

Since Mathlib has

```lean
W.b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
```

this gives, in `R[X]`,

```text
preΨ₄ + Ψ₂Sq² = Ψ₃ · (6X²+b₂X+b₄).
```

### CAS script

```python
import sympy as sp

X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

Psi2Sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
prePsi4 = (
    2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
    + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2)
)
Hcoeff = 6*X**2 + b2*X + b4
bRel = b2*b6 - b4**2 - 4*b8

expr = sp.expand(Psi3*Hcoeff - (prePsi4 + Psi2Sq**2))
print('difference =', sp.factor(expr))
print('difference_minus_X2_bRel_zero =', sp.expand(expr - X**2*bRel) == 0)
print('reduced_mod_bRel_zero =', sp.rem(sp.Poly(expr, b8), sp.Poly(bRel, b8)).as_expr() == 0)
```

### CAS output

```text
difference = X**2*(b2*b6 - b4**2 - 4*b8)
difference_minus_X2_bRel_zero = True
reduced_mod_bRel_zero = True
```

## Lean helper: the coefficient identity

Use this helper in `PsiInvariant.lean`.  The exact tactic may need the local namespace prefixes already opened in the file, but the mathematical certificate is simply `X^2 * W.b_relation.symm` after applying `C`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The coefficient in the CAS missing invariant. -/
def HmissCoeff (W : WeierstrassCurve R) : R[X] :=
  (6 : R[X]) * X ^ 2 + C W.b₂ * X + C W.b₄

/-- `preΨ₄ + Ψ₂Sq² = Ψ₃(6X²+b₂X+b₄)`, using the universal `b_relation`. -/
lemma preΨ₄_add_Ψ₂Sq_sq_eq_Ψ₃_mul_HmissCoeff (W : WeierstrassCurve R) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.Ψ₃ * HmissCoeff W := by
  linear_combination (norm := ring_nf [HmissCoeff, WeierstrassCurve.preΨ₄,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])
    X ^ 2 * ((congrArg (fun t : R => (C t : R[X])) W.b_relation).symm)

end WeierstrassCurve
```

If the sign is flipped by local normalization, replace `X ^ 2 * ...` by `-X ^ 2 * ...`; CAS says the exact difference

```text
Ψ₃*HmissCoeff - (preΨ₄+Ψ₂Sq²)
```

is `+ X²*bRel`.

## Coordinate-ring version of `preΨ₄ + ψ₂⁴`

In the coordinate ring, use `mk_ψ₂_sq`:

```lean
Affine.CoordinateRing.mk_ψ₂_sq :
  mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)
```

Then:

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local notation "mkW" p => CoordinateRing.mk W.toAffine p

/-- Coordinate-ring form of `preΨ₄ + ψ₂⁴ = Ψ₃(6X²+b₂X+b₄)`. -/
lemma mk_preΨ₄_add_ψ₂_pow_four_eq_Ψ₃_mul_HmissCoeff :
    mkW (C W.preΨ₄ + W.ψ₂ ^ 4) =
      mkW (C (W.Ψ₃ * HmissCoeff W)) := by
  have hψ2sq : mkW (W.ψ₂ ^ 2) = mkW (C W.Ψ₂Sq) := by
    simpa using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))
  calc
    mkW (C W.preΨ₄ + W.ψ₂ ^ 4)
        = mkW (C W.preΨ₄) + mkW (W.ψ₂ ^ 2) ^ 2 := by
            simp [pow_two, pow_succ, map_add, map_mul, mul_assoc]
    _ = mkW (C W.preΨ₄) + mkW (C W.Ψ₂Sq) ^ 2 := by
            rw [hψ2sq]
    _ = mkW (C (W.preΨ₄ + W.Ψ₂Sq ^ 2)) := by
            simp [map_add, map_mul, map_pow]
    _ = mkW (C (W.Ψ₃ * HmissCoeff W)) := by
            rw [W.preΨ₄_add_Ψ₂Sq_sq_eq_Ψ₃_mul_HmissCoeff]

end CoordinateRing
end Affine
end WeierstrassCurve
```

## Define `Hmiss` in Lean

Use your actual `ψ` terms from `PsiInvariant.lean`; this version takes them as parameters.

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- CAS `Hmiss` as a bivariate polynomial. -/
def HmissPoly
    (ψm2 ψm1 ψm ψp1 ψp2 : R[X][Y]) : R[X][Y] :=
  ψm1 ^ 2 * ψp2
    + ψm2 * ψp1 ^ 2
    + C W.Ψ₂Sq * ψm ^ 3
    - C (HmissCoeff W) * (ψm1 * ψm * ψp1)

end CoordinateRing
end Affine
end WeierstrassCurve
```

## First consequence of `mk_invariant_descended`: `Ψ₃ * Hmiss = 0`

This part does **not** need cancellation.

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local notation "mkW" p => CoordinateRing.mk W.toAffine p

/-- `mk_invariant_descended` gives `mk(Ψ₃ * Hmiss) = 0`. -/
lemma Ψ₃_mul_Hmiss_of_mk_invariant_descended
    (ψm2 ψm1 ψm ψp1 ψp2 : R[X][Y])
    -- Replace this hypothesis by the actual theorem call to `mk_invariant_descended`.
    (hInv :
      mkW (C W.Ψ₃ * (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3)) =
        mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1))) :
    mkW (C W.Ψ₃ * HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0 := by
  have hψ2sq : mkW (W.ψ₂ ^ 2) = mkW (C W.Ψ₂Sq) := by
    simpa using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))
  have hpre4 :
      mkW (C W.preΨ₄ + W.ψ₂ ^ 4) = mkW (C (W.Ψ₃ * HmissCoeff W)) :=
    mk_preΨ₄_add_ψ₂_pow_four_eq_Ψ₃_mul_HmissCoeff (W := W)

  have hInv' :
      mkW (C W.Ψ₃ *
          (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + C W.Ψ₂Sq * ψm ^ 3)) =
        mkW (C W.Ψ₃ * C (HmissCoeff W) * (ψp1 * ψm * ψm1)) := by
    calc
      mkW (C W.Ψ₃ *
          (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + C W.Ψ₂Sq * ψm ^ 3))
          = mkW (C W.Ψ₃ *
              (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3)) := by
                -- Replace `C Ψ₂Sq` by `ψ₂²` inside the coordinate ring.
                -- If `rw [← hψ2sq]` does not rewrite under `mk`, use this `simp` normalization.
                apply_fun (fun z => z) at hψ2sq
                rw [← hψ2sq]
                simp [map_add, map_mul, map_pow, mul_assoc]
      _ = mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1)) := hInv
      _ = mkW (C W.Ψ₃ * C (HmissCoeff W) * (ψp1 * ψm * ψm1)) := by
                rw [hpre4]
                simp [map_mul, mul_assoc]

  -- Now subtract RHS from LHS in the coordinate ring.
  linear_combination (norm := ring_nf [HmissPoly, map_add, map_sub, map_mul, map_pow,
    mul_assoc, mul_comm, mul_left_comm]) hInv'

end CoordinateRing
end Affine
end WeierstrassCurve
```

Depending on the actual local form of `mk_invariant_descended`, the middle `rw [← hψ2sq]` may need to be replaced by a `calc` in the coordinate ring. The algebraic content is exactly: replace `mk(ψ₂²)` by `mk(C Ψ₂Sq)`, replace `mk(preΨ₄+ψ₂⁴)` by `mk(C(Ψ₃*HmissCoeff))`, then move the RHS across.

## Cancelling `Ψ₃` to get `Hmiss`

This is valid over a field with `(3 : K) ≠ 0`.

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

local notation "mkW" p => CoordinateRing.mk W.toAffine p

/-- Nonzero class of `Ψ₃` in the affine coordinate ring, assuming `char K ≠ 3`. -/
lemma mk_C_Ψ₃_ne_zero (h3 : (3 : K) ≠ 0) :
    mkW (C W.Ψ₃) ≠ 0 := by
  have hC : (C W.Ψ₃ : K[X][Y]) ≠ 0 := by
    exact C_ne_zero.mpr (W.Ψ₃_ne_zero h3)
  exact by
    simpa [CoordinateRing.mk] using
      (AdjoinRoot.mk_ne_zero_of_natDegree_lt W.toAffine.monic_polynomial hC (by
        -- `C W.Ψ₃` has Y-degree 0, while `W.polynomial` has Y-degree 2.
        rw [WeierstrassCurve.Affine.natDegree_polynomial]
        simpa using (show (C W.Ψ₃ : K[X][Y]).natDegree < 2 by
          simp [hC])))

/-- Derive CAS `Hmiss` from `mk_invariant_descended` by cancelling `Ψ₃`. -/
lemma Hmiss_of_mk_invariant_descended
    (h3 : (3 : K) ≠ 0)
    (ψm2 ψm1 ψm ψp1 ψp2 : K[X][Y])
    -- Replace this hypothesis by the actual theorem call to `mk_invariant_descended`.
    (hInv :
      mkW (C W.Ψ₃ * (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3)) =
        mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1))) :
    mkW (HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0 := by
  have hmul_mk :
      mkW (C W.Ψ₃ * HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0 :=
    Ψ₃_mul_Hmiss_of_mk_invariant_descended
      (W := W) ψm2 ψm1 ψm ψp1 ψp2 hInv

  have hmul :
      mkW (C W.Ψ₃) * mkW (HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0 := by
    simpa [map_mul] using hmul_mk

  exact (mul_eq_zero.mp hmul).resolve_left (mk_C_Ψ₃_ne_zero (W := W) h3)

end CoordinateRing
end Affine
end WeierstrassCurve
```

## Important caveat

Without cancellation of `mk(C Ψ₃)`, `mk_invariant_descended` gives only

```lean
mkW (C W.Ψ₃ * HmissPoly ...) = 0
```

not `mkW (HmissPoly ...) = 0`.

So the proof of `Hmiss` from `mk_invariant_descended` needs the extra assumption used above:

```lean
h3 : (3 : K) ≠ 0
```

or some other proof that `mkW (C W.Ψ₃)` is nonzero and cancellable in the coordinate ring. In the `Ψ₃ = 0` stratum, this cancellation is exactly what fails, so use the nonsingularity/resultant certificates there instead.
