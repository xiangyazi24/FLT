# Q321 (dm2): Lean proof of `preΨ₄ + Ψ₂Sq² = Ψ₃ · (6X²+b₂X+b₄)`

Goal:

```lean
W.preΨ₄ + W.Ψ₂Sq ^ 2 =
  W.Ψ₃ * ((6 : K[X]) * X ^ 2 + C W.b₂ * X + C W.b₄)
```

Mathlib’s actual `b`-relation is oriented as

```lean
W.b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
```

CAS gives

```text
Ψ₃*(6X²+b₂X+b₄) - (preΨ₄+Ψ₂Sq²)
  = X²*(b₂*b₆ - b₄² - 4*b₈).
```

Equivalently,

```text
(preΨ₄+Ψ₂Sq²) - Ψ₃*(6X²+b₂X+b₄)
  = X²*(4*b₈ - (b₂*b₆ - b₄²)).
```

So in Lean the linear-combination coefficient should be `X ^ 2` times the `C`-lift of `W.b_relation`, **not** `.symm`.

## Buildable Lean file

```lean
import Mathlib

noncomputable section

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The coefficient `6X² + b₂X + b₄` occurring in the descended invariant. -/
def HmissCoeff (W : WeierstrassCurve R) : R[X] :=
  (6 : R[X]) * X ^ 2 + C W.b₂ * X + C W.b₄

/-- Universal coefficient identity:
`preΨ₄ + Ψ₂Sq² = Ψ₃ * (6X² + b₂X + b₄)`.

The raw polynomial difference is `X² * (4*b₈ - (b₂*b₆ - b₄²))`, so this is exactly
`X²` times the `C`-lift of `W.b_relation`.
-/
lemma preΨ₄_add_Ψ₂Sq_sq_eq_Ψ₃_mul_HmissCoeff (W : WeierstrassCurve R) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.Ψ₃ * HmissCoeff W := by
  have hbrel := W.b_relation
  have hbrelC : (C (4 * W.b₈) : R[X]) = C (W.b₂ * W.b₆ - W.b₄ ^ 2) := by
    exact congrArg (fun t : R => (C t : R[X])) hbrel
  linear_combination (norm := ring_nf [HmissCoeff,
      WeierstrassCurve.preΨ₄,
      WeierstrassCurve.Ψ₂Sq,
      WeierstrassCurve.Ψ₃,
      WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,
      WeierstrassCurve.b₈])
    X ^ 2 * hbrelC

end WeierstrassCurve
```

## If you want the theorem without defining `HmissCoeff`

```lean
import Mathlib

noncomputable section

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

lemma preΨ₄_add_Ψ₂Sq_sq_eq_Ψ₃_mul_coeff (W : WeierstrassCurve R) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 =
      W.Ψ₃ * ((6 : R[X]) * X ^ 2 + C W.b₂ * X + C W.b₄) := by
  have hbrel := W.b_relation
  have hbrelC : (C (4 * W.b₈) : R[X]) = C (W.b₂ * W.b₆ - W.b₄ ^ 2) := by
    exact congrArg (fun t : R => (C t : R[X])) hbrel
  linear_combination (norm := ring_nf [
      WeierstrassCurve.preΨ₄,
      WeierstrassCurve.Ψ₂Sq,
      WeierstrassCurve.Ψ₃,
      WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,
      WeierstrassCurve.b₈])
    X ^ 2 * hbrelC

end WeierstrassCurve
```

## CAS verification script

```python
import sympy as sp

X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

Psi2Sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
prePsi4 = (
    2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
    + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2)
)
H = 6*X**2 + b2*X + b4
bRel = b2*b6 - b4**2 - 4*b8

expr_rhs_minus_lhs = sp.expand(Psi3*H - (prePsi4 + Psi2Sq**2))
expr_lhs_minus_rhs = sp.expand((prePsi4 + Psi2Sq**2) - Psi3*H)

print('rhs_minus_lhs =', sp.factor(expr_rhs_minus_lhs))
print('lhs_minus_rhs =', sp.factor(expr_lhs_minus_rhs))
print('rhs_minus_lhs_minus_X2_bRel_zero =', sp.expand(expr_rhs_minus_lhs - X**2*bRel) == 0)
print('lhs_minus_rhs_plus_X2_bRel_zero =', sp.expand(expr_lhs_minus_rhs + X**2*bRel) == 0)
```

Output:

```text
rhs_minus_lhs = X**2*(b2*b6 - b4**2 - 4*b8)
lhs_minus_rhs = -X**2*(b2*b6 - b4**2 - 4*b8)
rhs_minus_lhs_minus_X2_bRel_zero = True
lhs_minus_rhs_plus_X2_bRel_zero = True
```

## Notes

* No `ext` is needed; `linear_combination` reduces the polynomial equality directly.
* The theorem is over a general `CommRing R`; no field or elliptic nonsingularity hypothesis is needed.
* If this lives in a file that already imports the elliptic-curve division-polynomial files and tactics, you can replace `import Mathlib` by the narrower imports already present in that file.
