# Q288 (dm1): symbolic CAS gate for the general-`m` `addX` identity

## Executive result

The proposed direct proof **does not close** with only the listed hypotheses

```text
Hω, Heven, Hφ, Hφ1, HF.
```

After substituting all of them, the symbolic remainder is not zero.  It is exactly

```text
ψ_m * Hmiss
```

where the missing relation is

```text
Hmiss = ψ_{m-1}^2*ψ_{m+2}
        + ψ_{m-2}*ψ_{m+1}^2
        + ψ_m^3*Ψ₂Sq
        - ψ_{m-1}*ψ_m*ψ_{m+1}*(6*X^2 + b₂*X + b₄).
```

Here

```text
b₂ = a₁^2 + 4*a₂
b₄ = a₁*a₃ + 2*a₄
b₆ = a₃^2 + 4*a₆
Ψ₂Sq = 4*X^3 + b₂*X^2 + 2*b₄*X + b₆.
```

So the decisive CAS gate says:

```text
listed hypotheses alone: FAIL
listed hypotheses + Hmiss: OK
```

This is important for Lean: the general `addX` proof cannot be just a `linear_combination` of `Hω`, `Heven`, `Hφ`, `Hφ1`, and `HF`.  You need one additional invariant.  The natural interpretation is that `Hmiss` is another division-polynomial / projective-representative identity, closely related to the assertion that the representative

```text
R_m = [φ_m : ω_m : ψ_m]
```

has the correct `X`/curve behavior.  In a Lean decomposition, add it as a separate atom or derive it from the projective representative equation / division-polynomial recurrences.

---

## Runnable SymPy script

```python
import sympy as sp

# Curve variables and general Weierstrass coefficients.
X, Y = sp.symbols('X Y')
a1, a2, a3, a4, a6 = sp.symbols('a1 a2 a3 a4 a6')

# Formal division-polynomial symbols around m.
pm2, pm1, pm, pp1, pp2, p2m = sp.symbols(
    'psi_m_minus_2 psi_m_minus_1 psi_m psi_m_plus_1 psi_m_plus_2 psi_2m'
)

# Standard b-invariants and two-division square.
b2 = a1**2 + 4*a2
b4 = a1*a3 + 2*a4
b6 = a3**2 + 4*a6
Psi2Sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
half_dPsi2Sq = 6*X**2 + b2*X + b4
psi2 = 2*Y + a1*X + a3

# Affine Weierstrass equation F_W = 0.
F = Y**2 + a1*X*Y + a3*Y - X**3 - a2*X**2 - a4*X - a6

# Hφ and Hφ1 are imposed by defining these expressions.
phi_m = X*pm**2 - pp1*pm1
phi_m_plus_1 = X*pp1**2 - pp2*pm

# Hω: 2*ψ_m*ω_m = ψ_2m - ψ_m^2*(a1*φ_m + a3*ψ_m^2).
Homega_rhs = p2m - pm**2*(a1*phi_m + a3*pm**2)

# Mathlib general Jacobian.addX for P=[X,Y,1], Q=[φ_m,ω_m,ψ_m].
# Instead of introducing omega and dividing, build 2*addX directly:
# the omega terms combine as -2*psi2*(psi_m*omega_m), and Hω replaces
# 2*psi_m*omega_m by Homega_rhs.
nonomega_addX = (
    X*phi_m**2
    + X**2*phi_m*pm**2
    - a1*Y*phi_m*pm**2
    + 2*a2*X*phi_m*pm**2
    - a3*Y*pm**4
    + a4*phi_m*pm**2
    + a4*X*pm**4
    + 2*a6*pm**4
)

expr_after_Homega = sp.expand(
    2*(nonomega_addX - pm1**2*phi_m_plus_1)
    - psi2*Homega_rhs
)

# Heven: psi_2m * psi2 = psi_{m-1}^2*psi_m*psi_{m+2}
#                            - psi_{m-2}*psi_m*psi_{m+1}^2.
Heven_rhs = pm1**2*pm*pp2 - pm2*pm*pp1**2

# The expression contains -psi2*psi_2m.  Replace it by -Heven_rhs.
expr_after_Heven = sp.expand(expr_after_Homega + psi2*p2m - Heven_rhs)

# Reduce by the Weierstrass equation as a monic polynomial in Y.
q, rem = sp.div(
    sp.Poly(expr_after_Heven, Y),
    sp.Poly(F, Y),
)
rem_expr = sp.expand(rem.as_expr())

Hmiss = sp.expand(
    pm1**2*pp2
    + pm2*pp1**2
    + pm**3*Psi2Sq
    - pm1*pm*pp1*half_dPsi2Sq
)

print('quotient by F after listed hypotheses =', q.as_expr())
print('remainder after listed hypotheses =')
print(sp.factor(rem_expr))
print()
print('is remainder zero?', rem_expr == 0)
print('remainder equals psi_m * Hmiss?', sp.expand(rem_expr - pm*Hmiss) == 0)
print()
print('Hmiss =')
print(Hmiss)

# Repaired check: add the missing relation Hmiss = 0.
repaired = sp.expand(rem_expr - pm*Hmiss)
assert repaired == 0
print()
print('after adding Hmiss: OK')
```

## Output

```text
quotient by F after listed hypotheses = 0
remainder after listed hypotheses =
psi_m*(4*X**3*psi_m**3 + X**2*a1**2*psi_m**3 + 4*X**2*a2*psi_m**3 - 6*X**2*psi_m*psi_m_minus_1*psi_m_plus_1 - X*a1**2*psi_m*psi_m_minus_1*psi_m_plus_1 + 2*X*a1*a3*psi_m**3 - 4*X*a2*psi_m*psi_m_minus_1*psi_m_plus_1 + 4*X*a4*psi_m**3 - a1*a3*psi_m*psi_m_minus_1*psi_m_plus_1 + a3**2*psi_m**3 - 2*a4*psi_m*psi_m_minus_1*psi_m_plus_1 + 4*a6*psi_m**3 + psi_m_minus_1**2*psi_m_plus_2 + psi_m_minus_2*psi_m_plus_1**2)

is remainder zero? False
remainder equals psi_m * Hmiss? True

Hmiss =
4*X**3*psi_m**3 + X**2*a1**2*psi_m**3 + 4*X**2*a2*psi_m**3 - 6*X**2*psi_m*psi_m_minus_1*psi_m_plus_1 - X*a1**2*psi_m*psi_m_minus_1*psi_m_plus_1 + 2*X*a1*a3*psi_m**3 - 4*X*a2*psi_m*psi_m_minus_1*psi_m_plus_1 + 4*X*a4*psi_m**3 - a1*a3*psi_m*psi_m_minus_1*psi_m_plus_1 + a3**2*psi_m**3 - 2*a4*psi_m*psi_m_minus_1*psi_m_plus_1 + 4*a6*psi_m**3 + psi_m_minus_1**2*psi_m_plus_2 + psi_m_minus_2*psi_m_plus_1**2

A compact form of Hmiss is:

Hmiss = ψ_{m-1}^2*ψ_{m+2}
        + ψ_{m-2}*ψ_{m+1}^2
        + ψ_m^3*(4*X^3 + b₂*X^2 + 2*b₄*X + b₆)
        - ψ_{m-1}*ψ_m*ψ_{m+1}*(6*X^2 + b₂*X + b₄)

after adding Hmiss: OK
```

---

## Lean implication

The general theorem needs one more hypothesis/lemma:

```lean
/-- Missing adjacent invariant needed for the general symbolic `addX` proof. -/
theorem psi_adjacent_X_invariant
    (W : WeierstrassCurve K) (m : ℤ) :
    Affine.CoordinateRing.mk W.toAffine
      (W.ψ (m - 1)^2 * W.ψ (m + 2)
        + W.ψ (m - 2) * W.ψ (m + 1)^2
        + W.ψ m^3 * C W.Ψ₂Sq
        - W.ψ (m - 1) * W.ψ m * W.ψ (m + 1)
            * C (6*X^2 + C W.b₂ * X + C W.b₄)) = 0 := by
  sorry
```

The exact Lean expression for the final factor should use `C` and `Polynomial.X` in `K[X][Y]`; I wrote it schematically above.  This lemma appears to be the missing atom.  With it, the direct `addX` proof becomes the expected `linear_combination` of:

```text
Hω,
Heven,
Hφ,
Hφ1,
HF,
psi_adjacent_X_invariant.
```

So the proposed four-hypothesis proof is too optimistic, but the repaired proof is still algebraic and non-circular.
