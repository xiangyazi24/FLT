# Q93 (dm1): `n = 3` division-polynomial separability certificate

## Result

For

```text
Ψ₃  = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
Ψ₃' = 12*X**3 + 3*b2*X**2 + 6*b4*X + 3*b6
Δ   = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
bRel = b2*b6 - b4**2 - 4*b8
```

the following integer-coefficient cofactors satisfy

```text
A3*Ψ₃ + B3*Ψ₃' = -81*Δ**2 + Q3*bRel
```

over `ℤ[b2,b4,b6,b8][X]`.

```text
A3 = 648*X**2*b2**3*b6 - 648*X**2*b2**2*b4**2 + 1296*X**2*b2**2*b8 - 27216*X**2*b2*b4*b6 + 23328*X**2*b4**3 - 31104*X**2*b4*b8 + 104976*X**2*b6**2 + 162*X*b2**4*b6 - 162*X*b2**3*b4**2 - 6480*X*b2**2*b4*b6 + 5832*X*b2*b4**3 + 2592*X*b2*b4*b8 + 29160*X*b2*b6**2 - 11664*X*b4**2*b6 - 46656*X*b6*b8 - 81*b2**4*b8 + 405*b2**3*b4*b6 - 324*b2**2*b4**3 + 3888*b2**2*b4*b8 + 81*b2**2*b6**2 - 16524*b2*b4**2*b6 - 14256*b2*b6*b8 + 11664*b4**4 - 31104*b4**2*b8 + 69984*b4*b6**2 + 20736*b8**2

B3 = -162*X**3*b2**3*b6 + 162*X**3*b2**2*b4**2 - 324*X**3*b2**2*b8 + 6804*X**3*b2*b4*b6 - 5832*X**3*b4**3 + 7776*X**3*b4*b8 - 26244*X**3*b6**2 - 54*X**2*b2**4*b6 + 54*X**2*b2**3*b4**2 - 27*X**2*b2**3*b8 + 2187*X**2*b2**2*b4*b6 - 1944*X**2*b2*b4**3 - 9477*X**2*b2*b6**2 + 2916*X**2*b4**2*b6 + 11664*X**2*b6*b8 + 27*X*b2**4*b8 - 189*X*b2**3*b4*b6 + 162*X*b2**2*b4**3 - 1350*X*b2**2*b4*b8 - 81*X*b2**2*b6**2 + 7776*X*b2*b4**2*b6 + 4536*X*b2*b6*b8 - 5832*X*b4**4 + 11664*X*b4**2*b8 - 30618*X*b4*b6**2 - 5184*X*b8**2 + 27*b2**3*b4*b8 - 108*b2**3*b6**2 + 81*b2**2*b4**2*b6 - 189*b2**2*b6*b8 - 972*b2*b4**2*b8 + 4374*b2*b4*b6**2 - 432*b2*b8**2 - 2916*b4**3*b6 + 11664*b4*b6*b8 - 19683*b6**3

Q3 = -972*b2**2*b4*b8 - 324*b2**2*b6**2 + 6480*b2*b4**2*b6 + 2592*b2*b6*b8 - 5184*b4**4 + 9072*b4**2*b8 - 26244*b4*b6**2 - 5184*b8**2
```

The actual resultant before imposing `bRel = 0` is

```text
Res_X(Ψ₃, Ψ₃') = -81*Δ**2 + Q3*bRel.
```

Equivalently,

```text
Res_X(Ψ₃, Ψ₃') + 81*Δ**2
  = -324*bRel*(3*b2**2*b4*b8 + b2**2*b6**2 - 20*b2*b4**2*b6
      - 8*b2*b6*b8 + 16*b4**4 - 28*b4**2*b8
      + 81*b4*b6**2 + 16*b8**2).
```

## Verification / reproduction script

This is self-contained.  It computes the Sylvester/Bézout coefficient solve for `A3,B3`, checks that the solution is integral, checks the resultant relation modulo `bRel`, and verifies the final displayed identity.

```python
import sympy as sp

X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

Psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
dPsi3 = sp.diff(Psi3, X)
Delta = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
bRel = b2*b6 - b4**2 - 4*b8

A3 = (
    648*X**2*b2**3*b6 - 648*X**2*b2**2*b4**2
    + 1296*X**2*b2**2*b8 - 27216*X**2*b2*b4*b6
    + 23328*X**2*b4**3 - 31104*X**2*b4*b8
    + 104976*X**2*b6**2 + 162*X*b2**4*b6
    - 162*X*b2**3*b4**2 - 6480*X*b2**2*b4*b6
    + 5832*X*b2*b4**3 + 2592*X*b2*b4*b8
    + 29160*X*b2*b6**2 - 11664*X*b4**2*b6
    - 46656*X*b6*b8 - 81*b2**4*b8
    + 405*b2**3*b4*b6 - 324*b2**2*b4**3
    + 3888*b2**2*b4*b8 + 81*b2**2*b6**2
    - 16524*b2*b4**2*b6 - 14256*b2*b6*b8
    + 11664*b4**4 - 31104*b4**2*b8
    + 69984*b4*b6**2 + 20736*b8**2
)

B3 = (
    -162*X**3*b2**3*b6 + 162*X**3*b2**2*b4**2
    - 324*X**3*b2**2*b8 + 6804*X**3*b2*b4*b6
    - 5832*X**3*b4**3 + 7776*X**3*b4*b8
    - 26244*X**3*b6**2 - 54*X**2*b2**4*b6
    + 54*X**2*b2**3*b4**2 - 27*X**2*b2**3*b8
    + 2187*X**2*b2**2*b4*b6 - 1944*X**2*b2*b4**3
    - 9477*X**2*b2*b6**2 + 2916*X**2*b4**2*b6
    + 11664*X**2*b6*b8 + 27*X*b2**4*b8
    - 189*X*b2**3*b4*b6 + 162*X*b2**2*b4**3
    - 1350*X*b2**2*b4*b8 - 81*X*b2**2*b6**2
    + 7776*X*b2*b4**2*b6 + 4536*X*b2*b6*b8
    - 5832*X*b4**4 + 11664*X*b4**2*b8
    - 30618*X*b4*b6**2 - 5184*X*b8**2
    + 27*b2**3*b4*b8 - 108*b2**3*b6**2
    + 81*b2**2*b4**2*b6 - 189*b2**2*b6*b8
    - 972*b2*b4**2*b8 + 4374*b2*b4*b6**2
    - 432*b2*b8**2 - 2916*b4**3*b6
    + 11664*b4*b6*b8 - 19683*b6**3
)

Q3 = (
    -972*b2**2*b4*b8 - 324*b2**2*b6**2
    + 6480*b2*b4**2*b6 + 2592*b2*b6*b8
    - 5184*b4**4 + 9072*b4**2*b8
    - 26244*b4*b6**2 - 5184*b8**2
)

# Recompute A3,B3 by the Sylvester/Bézout coefficient solve.
# A has degree < deg(dPsi3)=3, B has degree < deg(Psi3)=4.
Res = sp.resultant(Psi3, dPsi3, X)
a0, a1, a2, c0, c1, c2, c3 = sp.symbols('a0 a1 a2 c0 c1 c2 c3')
A = a0 + a1*X + a2*X**2
B = c0 + c1*X + c2*X**2 + c3*X**3
coeff_poly = sp.Poly(A*Psi3 + B*dPsi3 - Res, X)
eqs = [sp.Eq(coeff_poly.coeff_monomial(X**i), 0) for i in range(7)]
sol = sp.solve(eqs, [a0, a1, a2, c0, c1, c2, c3], dict=True, simplify=False)[0]
A_computed = sp.expand(A.subs(sol))
B_computed = sp.expand(B.subs(sol))

assert A_computed == A3
assert B_computed == B3

# Integer-coefficient checks.
for name, poly in [('A3', A3), ('B3', B3), ('Q3', Q3)]:
    P = sp.Poly(poly, X, b2, b4, b6, b8, domain=sp.ZZ)
    assert all(c in sp.ZZ for c in P.coeffs()), name

assert sp.expand(A3*Psi3 + B3*dPsi3 - Res) == 0
assert sp.expand(Res - (-81*Delta**2) - Q3*bRel) == 0
assert sp.expand(A3*Psi3 + B3*dPsi3 - (-81*Delta**2) - Q3*bRel) == 0

print('deg_X(A3)=', sp.Poly(A3, X).degree())
print('deg_X(B3)=', sp.Poly(B3, X).degree())
print('deg_X(Q3)=', sp.Poly(Q3, X).degree())
print('OK')
```

Expected final output:

```text
deg_X(A3)= 2
deg_X(B3)= 3
deg_X(Q3)= 0
OK
```

## Lean certificate

The following is the direct certificate shape for `FLT/EllipticCurve/Torsion.lean` or a nearby division-polynomial file.  The only possible local-name adjustment is the discriminant definition name if your imports expose it as a qualified theorem/definition other than `WeierstrassCurve.Δ`; the polynomial certificate itself is completely expanded.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k)

private lemma bRelC (W : WeierstrassCurve k) :
    C W.b₂ * C W.b₆ - C W.b₄ ^ 2 - C (4 : k) * C W.b₈ = (0 : k[X]) := by
  have hb0 : W.b₂ * W.b₆ - W.b₄ ^ 2 - (4 : k) * W.b₈ = 0 := by
    have hb := b_relation (W := W)
    -- `hb : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2`.
    rw [← hb]
    ring
  have hbC := congrArg (fun z : k => (C z : k[X])) hb0
  simpa [map_sub, map_mul, map_pow] using hbC

private noncomputable def A₃ (W : WeierstrassCurve k) : k[X] :=
  648 * X ^ 2 * C W.b₂ ^ 3 * C W.b₆
    - 648 * X ^ 2 * C W.b₂ ^ 2 * C W.b₄ ^ 2
    + 1296 * X ^ 2 * C W.b₂ ^ 2 * C W.b₈
    - 27216 * X ^ 2 * C W.b₂ * C W.b₄ * C W.b₆
    + 23328 * X ^ 2 * C W.b₄ ^ 3
    - 31104 * X ^ 2 * C W.b₄ * C W.b₈
    + 104976 * X ^ 2 * C W.b₆ ^ 2
    + 162 * X * C W.b₂ ^ 4 * C W.b₆
    - 162 * X * C W.b₂ ^ 3 * C W.b₄ ^ 2
    - 6480 * X * C W.b₂ ^ 2 * C W.b₄ * C W.b₆
    + 5832 * X * C W.b₂ * C W.b₄ ^ 3
    + 2592 * X * C W.b₂ * C W.b₄ * C W.b₈
    + 29160 * X * C W.b₂ * C W.b₆ ^ 2
    - 11664 * X * C W.b₄ ^ 2 * C W.b₆
    - 46656 * X * C W.b₆ * C W.b₈
    - 81 * C W.b₂ ^ 4 * C W.b₈
    + 405 * C W.b₂ ^ 3 * C W.b₄ * C W.b₆
    - 324 * C W.b₂ ^ 2 * C W.b₄ ^ 3
    + 3888 * C W.b₂ ^ 2 * C W.b₄ * C W.b₈
    + 81 * C W.b₂ ^ 2 * C W.b₆ ^ 2
    - 16524 * C W.b₂ * C W.b₄ ^ 2 * C W.b₆
    - 14256 * C W.b₂ * C W.b₆ * C W.b₈
    + 11664 * C W.b₄ ^ 4
    - 31104 * C W.b₄ ^ 2 * C W.b₈
    + 69984 * C W.b₄ * C W.b₆ ^ 2
    + 20736 * C W.b₈ ^ 2

private noncomputable def B₃ (W : WeierstrassCurve k) : k[X] :=
  - 162 * X ^ 3 * C W.b₂ ^ 3 * C W.b₆
    + 162 * X ^ 3 * C W.b₂ ^ 2 * C W.b₄ ^ 2
    - 324 * X ^ 3 * C W.b₂ ^ 2 * C W.b₈
    + 6804 * X ^ 3 * C W.b₂ * C W.b₄ * C W.b₆
    - 5832 * X ^ 3 * C W.b₄ ^ 3
    + 7776 * X ^ 3 * C W.b₄ * C W.b₈
    - 26244 * X ^ 3 * C W.b₆ ^ 2
    - 54 * X ^ 2 * C W.b₂ ^ 4 * C W.b₆
    + 54 * X ^ 2 * C W.b₂ ^ 3 * C W.b₄ ^ 2
    - 27 * X ^ 2 * C W.b₂ ^ 3 * C W.b₈
    + 2187 * X ^ 2 * C W.b₂ ^ 2 * C W.b₄ * C W.b₆
    - 1944 * X ^ 2 * C W.b₂ * C W.b₄ ^ 3
    - 9477 * X ^ 2 * C W.b₂ * C W.b₆ ^ 2
    + 2916 * X ^ 2 * C W.b₄ ^ 2 * C W.b₆
    + 11664 * X ^ 2 * C W.b₆ * C W.b₈
    + 27 * X * C W.b₂ ^ 4 * C W.b₈
    - 189 * X * C W.b₂ ^ 3 * C W.b₄ * C W.b₆
    + 162 * X * C W.b₂ ^ 2 * C W.b₄ ^ 3
    - 1350 * X * C W.b₂ ^ 2 * C W.b₄ * C W.b₈
    - 81 * X * C W.b₂ ^ 2 * C W.b₆ ^ 2
    + 7776 * X * C W.b₂ * C W.b₄ ^ 2 * C W.b₆
    + 4536 * X * C W.b₂ * C W.b₆ * C W.b₈
    - 5832 * X * C W.b₄ ^ 4
    + 11664 * X * C W.b₄ ^ 2 * C W.b₈
    - 30618 * X * C W.b₄ * C W.b₆ ^ 2
    - 5184 * X * C W.b₈ ^ 2
    + 27 * C W.b₂ ^ 3 * C W.b₄ * C W.b₈
    - 108 * C W.b₂ ^ 3 * C W.b₆ ^ 2
    + 81 * C W.b₂ ^ 2 * C W.b₄ ^ 2 * C W.b₆
    - 189 * C W.b₂ ^ 2 * C W.b₆ * C W.b₈
    - 972 * C W.b₂ * C W.b₄ ^ 2 * C W.b₈
    + 4374 * C W.b₂ * C W.b₄ * C W.b₆ ^ 2
    - 432 * C W.b₂ * C W.b₈ ^ 2
    - 2916 * C W.b₄ ^ 3 * C W.b₆
    + 11664 * C W.b₄ * C W.b₆ * C W.b₈
    - 19683 * C W.b₆ ^ 3

private noncomputable def Q₃ (W : WeierstrassCurve k) : k[X] :=
  - 972 * C W.b₂ ^ 2 * C W.b₄ * C W.b₈
    - 324 * C W.b₂ ^ 2 * C W.b₆ ^ 2
    + 6480 * C W.b₂ * C W.b₄ ^ 2 * C W.b₆
    + 2592 * C W.b₂ * C W.b₆ * C W.b₈
    - 5184 * C W.b₄ ^ 4
    + 9072 * C W.b₄ ^ 2 * C W.b₈
    - 26244 * C W.b₄ * C W.b₆ ^ 2
    - 5184 * C W.b₈ ^ 2

/-- Integer Bézout certificate for `Ψ₃` and its derivative, after using `b_relation`. -/
private lemma bezout_Ψ₃_dΨ₃ (W : WeierstrassCurve k) :
    A₃ W * W.Ψ₃ + B₃ W * derivative W.Ψ₃ = C ((-81 : k) * W.Δ ^ 2) := by
  have hb := bRelC (W := W)
  linear_combination (norm := ring_nf [A₃, B₃, Q₃, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.Δ]) (Q₃ W) * hb

variable [W.IsElliptic]

lemma Ψ₃_isCoprime_derivative (h3 : (3 : k) ≠ 0) :
    IsCoprime W.Ψ₃ (derivative W.Ψ₃) := by
  classical
  have hbez := bezout_Ψ₃_dΨ₃ (W := W)
  have h81 : (-81 : k) ≠ 0 := by
    have hpow : (3 : k) ^ 4 ≠ 0 := pow_ne_zero 4 h3
    have h81pos : (81 : k) ≠ 0 := by
      norm_num at hpow ⊢
    exact neg_ne_zero.mpr h81pos
  have hunit_scalar : IsUnit ((-81 : k) * W.Δ ^ 2) := by
    exact (isUnit_iff_ne_zero.mpr h81).mul ((W.isUnit_Δ).pow 2)
  have hunitC : IsUnit (C ((-81 : k) * W.Δ ^ 2) : k[X]) := by
    exact isUnit_C.mpr hunit_scalar
  rcases hunitC with ⟨u, hu⟩
  rw [← hu] at hbez
  refine ⟨↑u⁻¹ * A₃ W, ↑u⁻¹ * B₃ W, ?_⟩
  calc
    (↑u⁻¹ * A₃ W) * W.Ψ₃ + (↑u⁻¹ * B₃ W) * derivative W.Ψ₃
        = ↑u⁻¹ * (A₃ W * W.Ψ₃ + B₃ W * derivative W.Ψ₃) := by ring
    _ = ↑u⁻¹ * ↑u := by rw [hbez]
    _ = 1 := by simp

lemma preΨ'_three_separable (h3 : (3 : k) ≠ 0) :
    (W.preΨ' 3).Separable := by
  rw [preΨ'_three, Polynomial.separable_def]
  exact Ψ₃_isCoprime_derivative (W := W) h3

end

end WeierstrassCurve
```

## Integration notes

* The certificate identity is independent of `[W.IsElliptic]`; ellipticity is used only to make `W.Δ` a unit via `W.isUnit_Δ`.
* The hypothesis `(3 : k) ≠ 0` is exactly what makes `-81 = -3^4` a unit in `k`.
* This proves the `n = 3` instance of the broader separability brick:
  ```lean
  (W.preΨ' 3).Separable
  ```
  without needing the general multiplication-by-`n` étaleness theorem.
