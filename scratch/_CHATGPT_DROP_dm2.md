# Q257 (dm2): General Weierstrass `addX` cofactor for `m = 2`

CAS target:

```text
addX([X,Y,1], [φ₂,ω₂,ψ₂]) - ψ₁² φ₃ = Q · F_W
```

for the general Weierstrass equation

```text
F_W = Y² + a₁XY + a₃Y - X³ - a₂X² - a₄X - a₆.
```

## Result

The quotient is small and factors cleanly:

```text
Q = 2 * ψ₂² * Ψ₂Sq
```

where

```text
ψ₂   = 2Y + a₁X + a₃
Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆
      = 4X³ + (a₁²+4a₂)X² + 2(2a₄+a₁a₃)X + (a₃²+4a₆).
```

Expanded:

```text
Q = 8*X**5*a1**2 + 32*X**4*Y*a1 + 2*X**4*a1**4 + 8*X**4*a1**2*a2 + 16*X**4*a1*a3 + 32*X**3*Y**2 + 8*X**3*Y*a1**3 + 32*X**3*Y*a1*a2 + 32*X**3*Y*a3 + 8*X**3*a1**3*a3 + 8*X**3*a1**2*a4 + 16*X**3*a1*a2*a3 + 8*X**3*a3**2 + 8*X**2*Y**2*a1**2 + 32*X**2*Y**2*a2 + 24*X**2*Y*a1**2*a3 + 32*X**2*Y*a1*a4 + 32*X**2*Y*a2*a3 + 12*X**2*a1**2*a3**2 + 8*X**2*a1**2*a6 + 16*X**2*a1*a3*a4 + 8*X**2*a2*a3**2 + 16*X*Y**2*a1*a3 + 32*X*Y**2*a4 + 24*X*Y*a1*a3**2 + 32*X*Y*a1*a6 + 32*X*Y*a3*a4 + 8*X*a1*a3**3 + 16*X*a1*a3*a6 + 8*X*a3**2*a4 + 8*Y**2*a3**2 + 32*Y**2*a6 + 8*Y*a3**3 + 32*Y*a3*a6 + 2*a3**4 + 8*a3**2*a6
```

The division remainder modulo `F_W`, treated as monic in `Y`, is zero.

For the short specialization `a₁=a₂=a₃=0, a₄=A, a₆=B`, this becomes

```text
Q = 2*(2Y)^2*(4X^3 + 4AX + 4B) = 32Y²(X³+AX+B),
```

matching the earlier short-Weierstrass computation.

## Mathlib `Jacobian.addX` formula used

I used the `WeierstrassCurve.Jacobian.addX` definition from Mathlib’s `Jacobian/Formula.lean`:

```text
addX(P,Q) =
  P₀*Q₀²*P₂²
  - 2*P₁*Q₁*P₂*Q₂
  + P₀²*Q₀*Q₂²
  - a₁*P₀*Q₁*P₂²*Q₂
  - a₁*P₁*Q₀*P₂*Q₂²
  + 2*a₂*P₀*Q₀*P₂²*Q₂²
  - a₃*Q₁*P₂⁴*Q₂
  - a₃*P₁*P₂*Q₂⁴
  + a₄*Q₀*P₂⁴*Q₂²
  + a₄*P₀*P₂²*Q₂⁴
  + 2*a₆*P₂⁴*Q₂⁴.
```

## Complete runnable SymPy script

```python
import sympy as sp

X, Y, a1, a2, a3, a4, a6 = sp.symbols("X Y a1 a2 a3 a4 a6")

FW = Y**2 + a1*X*Y + a3*Y - X**3 - a2*X**2 - a4*X - a6

b2 = a1**2 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3**2 + 4*a6
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2

psi1 = sp.Integer(1)
psi2 = 2*Y + a1*X + a3
psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
prepsi4 = (
    2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
    + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2)
)
psi4 = sp.expand(psi2 * prepsi4)

phi2 = sp.expand(X*psi2**2 - psi3)
phi3 = sp.expand(X*psi3**2 - psi4*psi2)

# 2*psi2*omega2 = psi4 - psi2^2*(a1*phi2 + a3*psi2^2)
omega2_num = sp.expand(psi4 - psi2**2*(a1*phi2 + a3*psi2**2))
omega2, omega2_rem = sp.div(
    omega2_num, 2*psi2, Y, X, a1, a2, a3, a4, a6, domain=sp.QQ
)
omega2 = sp.expand(omega2)
omega2_rem = sp.expand(omega2_rem)
assert omega2_rem == 0


def jacobian_addX(P, Q):
    """Mathlib WeierstrassCurve.Jacobian.addX specialized from Formula.lean."""
    P0, P1, P2 = P
    Q0, Q1, Q2 = Q
    return sp.expand(
        P0*Q0**2*P2**2
        - 2*P1*Q1*P2*Q2
        + P0**2*Q0*Q2**2
        - a1*P0*Q1*P2**2*Q2
        - a1*P1*Q0*P2*Q2**2
        + 2*a2*P0*Q0*P2**2*Q2**2
        - a3*Q1*P2**4*Q2
        - a3*P1*P2*Q2**4
        + a4*Q0*P2**4*Q2**2
        + a4*P0*P2**2*Q2**4
        + 2*a6*P2**4*Q2**4
    )


P = [X, Y, sp.Integer(1)]
R2 = [phi2, omega2, psi2]

addX = jacobian_addX(P, R2)
bigPoly = sp.expand(addX - psi1**2 * phi3)

# Divide by F_W as a monic polynomial in Y.
Qpoly, Rem = sp.div(sp.Poly(bigPoly, Y), sp.Poly(FW, Y))
Q = sp.expand(Qpoly.as_expr())
Rem = sp.expand(Rem.as_expr())

print("omega2_exact_division_remainder_zero =", omega2_rem == 0)
print("division_remainder_zero =", Rem == 0)
print("Q_expanded =")
print(sp.sstr(Q))
print()
print("Q_factored =")
print(sp.sstr(sp.factor(Q)))
print()
print(
    "Q_equals_2_psi2sq_Psi2Sq =",
    sp.expand(Q - 2*psi2**2*(4*X**3 + b2*X**2 + 2*b4*X + b6)) == 0,
)
print("identity_verified =", sp.expand(bigPoly - Q*FW) == 0)
```

## Script output

```text
omega2_exact_division_remainder_zero = True
division_remainder_zero = True
Q_expanded =
8*X**5*a1**2 + 32*X**4*Y*a1 + 2*X**4*a1**4 + 8*X**4*a1**2*a2 + 16*X**4*a1*a3 + 32*X**3*Y**2 + 8*X**3*Y*a1**3 + 32*X**3*Y*a1*a2 + 32*X**3*Y*a3 + 8*X**3*a1**3*a3 + 8*X**3*a1**2*a4 + 16*X**3*a1*a2*a3 + 8*X**3*a3**2 + 8*X**2*Y**2*a1**2 + 32*X**2*Y**2*a2 + 24*X**2*Y*a1**2*a3 + 32*X**2*Y*a1*a4 + 32*X**2*Y*a2*a3 + 12*X**2*a1**2*a3**2 + 8*X**2*a1**2*a6 + 16*X**2*a1*a3*a4 + 8*X**2*a2*a3**2 + 16*X*Y**2*a1*a3 + 32*X*Y**2*a4 + 24*X*Y*a1*a3**2 + 32*X*Y*a1*a6 + 32*X*Y*a3*a4 + 8*X*a1*a3**3 + 16*X*a1*a3*a6 + 8*X*a3**2*a4 + 8*Y**2*a3**2 + 32*Y**2*a6 + 8*Y*a3**3 + 32*Y*a3*a6 + 2*a3**4 + 8*a3**2*a6

Q_factored =
2*(X*a1 + 2*Y + a3)**2*(4*X**3 + X**2*a1**2 + 4*X**2*a2 + 2*X*a1*a3 + 4*X*a4 + a3**2 + 4*a6)

Q_equals_2_psi2sq_Psi2Sq = True
identity_verified = True
```
