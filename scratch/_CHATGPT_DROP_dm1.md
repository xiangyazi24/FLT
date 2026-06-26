# Q826 (dm1): separability of `preΨ₄`

## Key point

Do **not** compute a degree-6 resultant certificate over independent variables

```text
ℤ[b₂,b₄,b₆,b₈][X].
```

The `bᵢ` are not independent for a Weierstrass curve: Mathlib has

```lean
lemma WeierstrassCurve.b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
```

Equivalently, after inverting `4`, one can eliminate

```text
b₈ = (b₂*b₆ - b₄²)/4.
```

After this elimination, `gcdex(preΨ₄, preΨ₄')` gives a small Bézout certificate whose right side is

```text
(-4 * Δ)^2,
```

not the full resultant.  This is much smaller than the resultant identity

```text
Res(preΨ₄, preΨ₄') = 2^9 * Δ^5
```

(up to the sign convention for `Polynomial.resultant`).

The certificate below proves separability because `[W.IsElliptic]` makes `Δ` a unit, and `h4 : (4 : K) ≠ 0` makes `4` a unit in the field `K`.

## Lean code

I have not run this in a local Mathlib checkout in this environment.  The algebraic certificate was checked with the Sympy script below.  The only Lean-fragile line is the `simp ...; ring1` proof of the certificate; if your branch's simp set differs, replace that line by a more explicit derivative-simp list.  The cofactors and proof structure are the intended drop-in code.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K]

private def psi4SepA (W : WeierstrassCurve K) : K[X] :=
  -2 *
    (C (69 * W.b₂ ^ 3 * W.b₆ - 69 * W.b₂ ^ 2 * W.b₄ ^ 2
        - 2274 * W.b₂ * W.b₄ * W.b₆ + 2048 * W.b₄ ^ 3
        + 5832 * W.b₆ ^ 2)
      + C (-60 * W.b₂ * W.b₄ ^ 2 - 3960 * W.b₄ * W.b₆) * X
      + C (150 * W.b₂ ^ 2 * W.b₄ + 540 * W.b₂ * W.b₆
          - 4320 * W.b₄ ^ 2) * X ^ 2
      + C (50 * W.b₂ ^ 3 - 1320 * W.b₂ * W.b₄
          + 2160 * W.b₆) * X ^ 3
      + C (120 * W.b₂ ^ 2 - 2880 * W.b₄) * X ^ 4)

private def psi4SepB (W : WeierstrassCurve K) : K[X] :=
  2 *
    (C (2 * W.b₂ ^ 4 * W.b₆ - 2 * W.b₂ ^ 3 * W.b₄ ^ 2
        - 67 * W.b₂ ^ 2 * W.b₄ * W.b₆ + 59 * W.b₂ * W.b₄ ^ 3
        + 156 * W.b₂ * W.b₆ ^ 2 + 50 * W.b₄ ^ 2 * W.b₆)
      + C (29 * W.b₂ ^ 3 * W.b₆ - 29 * W.b₂ ^ 2 * W.b₄ ^ 2
          - 884 * W.b₂ * W.b₄ * W.b₆ + 808 * W.b₄ ^ 3
          + 1872 * W.b₆ ^ 2) * X
      + C (80 * W.b₂ ^ 2 * W.b₆ - 20 * W.b₂ * W.b₄ ^ 2
          - 1560 * W.b₄ * W.b₆) * X ^ 2
      + C (40 * W.b₂ ^ 2 * W.b₄ + 120 * W.b₂ * W.b₆
          - 1120 * W.b₄ ^ 2) * X ^ 3
      + C (10 * W.b₂ ^ 3 - 260 * W.b₂ * W.b₄
          + 360 * W.b₆) * X ^ 4
      + C (20 * W.b₂ ^ 2 - 480 * W.b₄) * X ^ 5)

private lemma psi4Sep_bezout (W : WeierstrassCurve K) :
    psi4SepA W * W.preΨ₄ + psi4SepB W * derivative W.preΨ₄ =
      C (((-4 : K) * W.Δ) ^ 2) := by
  simp [psi4SepA, psi4SepB, preΨ₄, Δ, b₂, b₄, b₆, b₈]
  ring1

/-- The reduced 4-division polynomial is separable away from characteristic `2`. -/
theorem Psi4_separable (W : WeierstrassCurve K) [W.IsElliptic]
    (h4 : (4 : K) ≠ 0) : (W.preΨ₄).Separable := by
  rw [Polynomial.separable_def']
  let u : K := ((-4 : K) * W.Δ) ^ 2
  have hu : u ≠ 0 := by
    dsimp [u]
    exact pow_ne_zero 2 <|
      mul_ne_zero (by simpa using (neg_ne_zero.mpr h4 : (-(4 : K)) ≠ 0)) W.isUnit_Δ.ne_zero
  refine ⟨C u⁻¹ * psi4SepA W, C u⁻¹ * psi4SepB W, ?_⟩
  calc
    (C u⁻¹ * psi4SepA W) * W.preΨ₄
        + (C u⁻¹ * psi4SepB W) * derivative W.preΨ₄
        = C u⁻¹ * (psi4SepA W * W.preΨ₄
            + psi4SepB W * derivative W.preΨ₄) := by
          ring
    _ = C u⁻¹ * C u := by
          rw [psi4Sep_bezout]
          rfl
    _ = 1 := by
          rw [← C_mul, inv_mul_cancel hu, C_1]

end

end WeierstrassCurve
```

### If `simp` does not reduce the derivative enough

Replace the body of `psi4Sep_bezout` by the more explicit version:

```lean
private lemma psi4Sep_bezout (W : WeierstrassCurve K) :
    psi4SepA W * W.preΨ₄ + psi4SepB W * derivative W.preΨ₄ =
      C (((-4 : K) * W.Δ) ^ 2) := by
  simp only [psi4SepA, psi4SepB, preΨ₄, Δ, b₂, b₄, b₆, b₈,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_ofNat]
  ring1
```

Depending on the exact Mathlib revision, the broad `simp [...]` version is usually more robust because `derivative` has a good simp API.

## Sympy script that generated the certificate

This script does **not** run gcdex over independent `b₂,b₄,b₆,b₈`.  It first eliminates `b₈` using the universal Weierstrass identity `4b₈ = b₂b₆ - b₄²`.  That is exactly the identity Mathlib calls `W.b_relation`.

```python
import sympy as sp

x, b2, b4, b6 = sp.symbols("x b2 b4 b6")

# Use the Weierstrass relation 4*b8 = b2*b6 - b4^2.
b8 = (b2*b6 - b4**2) / 4

psi4 = (
    2*x**6
    + b2*x**5
    + 5*b4*x**4
    + 10*b6*x**3
    + 10*b8*x**2
    + (b2*b8 - b4*b6)*x
    + (b4*b8 - b6**2)
)
dpsi4 = sp.diff(psi4, x)

Delta = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
D = sp.factor(-4 * Delta)

F = sp.Poly(psi4, x, domain=sp.QQ.frac_field(b2, b4, b6))
G = sp.Poly(dpsi4, x, domain=sp.QQ.frac_field(b2, b4, b6))

s, t, g = sp.gcdex(F, G)  # s*F + t*G = g
assert g.as_expr() == 1

s_expr = sp.factor(s.as_expr())
t_expr = sp.factor(t.as_expr())

# Clear the common denominator.  This denominator is D^2 = (-4*Delta)^2.
den_s = sp.together(s_expr).as_numer_denom()[1]
den_t = sp.together(t_expr).as_numer_denom()[1]
den = sp.factor(sp.lcm(den_s, den_t))

A = sp.factor(s_expr * den)
B = sp.factor(t_expr * den)

assert sp.factor(den - D**2) == 0
assert sp.factor(A*psi4 + B*dpsi4 - D**2) == 0

print("A =")
print(A)
print("\nB =")
print(B)
print("\nright side =")
print(sp.factor(D**2))
print("\nresultant check =")
print(sp.factor(sp.resultant(sp.Poly(psi4, x), sp.Poly(dpsi4, x), x) / Delta**5))
```

Expected output for the cofactors is:

```text
A =
-2*(69*b2**3*b6 + 50*b2**3*x**3 - 69*b2**2*b4**2
 + 150*b2**2*b4*x**2 + 210*b2**2*b6*x + 120*b2**2*x**4
 - 60*b2*b4**2*x - 2274*b2*b4*b6 - 1320*b2*b4*x**3
 + 540*b2*b6*x**2 + 2048*b4**3 - 4320*b4**2*x**2
 - 3960*b4*b6*x - 2880*b4*x**4 + 5832*b6**2 + 2160*b6*x**3)

B =
2*(2*b2**4*b6 - 2*b2**3*b4**2 + 29*b2**3*b6*x
 + 10*b2**3*x**4 - 29*b2**2*b4**2*x - 67*b2**2*b4*b6
 + 40*b2**2*b4*x**3 + 80*b2**2*b6*x**2 + 20*b2**2*x**5
 + 59*b2*b4**3 - 20*b2*b4**2*x**2 - 884*b2*b4*b6*x
 - 260*b2*b4*x**4 + 156*b2*b6**2 + 120*b2*b6*x**3
 + 808*b4**3*x + 50*b4**2*b6 - 1120*b4**2*x**3
 - 1560*b4*b6*x**2 - 480*b4*x**5 + 1872*b6**2*x
 + 360*b6*x**4)

right side =
(b2**3*b6 - b2**2*b4**2 - 36*b2*b4*b6 + 32*b4**3 + 108*b6**2)**2
```

Since

```text
b2**3*b6 - b2**2*b4**2 - 36*b2*b4*b6 + 32*b4**3 + 108*b6**2 = -4*Delta,
```

the right side is `(-4*Δ)^2`, exactly as used in the Lean certificate.

## Encoding note

The script's `A` and `B` are polynomials in `x`.  In Lean, each coefficient is wrapped with `Polynomial.C`, and `x^i` becomes `X ^ i`.  For example, the Sympy term

```text
150*b2**2*b4*x**2
```

becomes

```lean
C (150 * W.b₂ ^ 2 * W.b₄) * X ^ 2
```

The right-hand side is a unit because:

```lean
W.isUnit_Δ : IsUnit W.Δ
h4 : (4 : K) ≠ 0
```

and in a field every nonzero element is a unit.  The final proof multiplies the Bézout certificate by `C u⁻¹`, where

```lean
u = ((-4 : K) * W.Δ) ^ 2.
```
