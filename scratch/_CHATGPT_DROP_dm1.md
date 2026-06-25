# Q236 (dm1): CAS cofactor for the short-Weierstrass `addX` identity

## Result

For the short Weierstrass curve

```text
F_W = Y**2 - X**3 - A*X - B
```

with the standard short-Weierstrass division polynomials and

```text
ω_m = (ψ_{m+2}*ψ_{m-1}**2 - ψ_{m-2}*ψ_{m+1}**2) / (4*Y),
```

the first nontrivial `addX` identity, `m = 2`, is:

```text
addX([X,Y,1], [φ₂,ω₂,ψ₂]) - ψ₁**2 * φ₃
  = Q₂ * F_W
```

where division by `F_W` is performed as a monic polynomial in `Y`, and

```text
Q₂ = 32*X**3*Y**2 + 32*A*X*Y**2 + 32*B*Y**2
   = 32*Y**2*(X**3 + A*X + B).
```

The same script also checks that the remainder is zero for `m = 3`.  I did not print the full `Q₃` because it has 58 terms; the script computes it and can print it by setting `PRINT_Q3 = True`.

## Runnable SymPy script

```python
import sympy as sp

X, Y, A, B = sp.symbols('X Y A B')
F = Y**2 - X**3 - A*X - B

# Standard short-Weierstrass division polynomials, enough for m = 2, 3.
# These are used as polynomials in ZZ[A,B,X,Y]; identities are checked modulo F.
psi = {}
psi[0] = sp.Integer(0)
psi[1] = sp.Integer(1)
psi[2] = 2*Y
psi[3] = 3*X**4 + 6*A*X**2 + 12*B*X - A**2
psi[4] = 4*Y*(X**6 + 5*A*X**4 + 20*B*X**3 - 5*A**2*X**2 - 4*A*B*X - 8*B**2 - A**3)
psi[5] = sp.expand(psi[4]*psi[2]**3 - psi[1]*psi[3]**3)

def getpsi(n: int):
    if n in psi:
        return psi[n]
    if n < 0:
        return -getpsi(-n)
    raise ValueError(f'psi({n}) not precomputed; this script only needs psi through 5')

def phi(n: int):
    return sp.expand(X*getpsi(n)**2 - getpsi(n + 1)*getpsi(n - 1))

def omega(n: int):
    """Standard short-Weierstrass omega_n with denominator 4Y."""
    numerator = sp.expand(getpsi(n + 2)*getpsi(n - 1)**2 - getpsi(n - 2)*getpsi(n + 1)**2)
    q, r = sp.div(
        sp.Poly(numerator, Y, domain=sp.QQ[A, B, X]),
        sp.Poly(4*Y, Y, domain=sp.QQ[A, B, X]),
    )
    assert r.as_expr() == 0, f'omega({n}) numerator not divisible by 4Y'
    out = sp.expand(q.as_expr())
    # Check it is actually integral.
    sp.Poly(out, X, Y, A, B, domain=sp.ZZ)
    return out

def addX(P, Q):
    """Mathlib Jacobian.addX specialized to a1=a2=a3=0, a4=A, a6=B."""
    XP, YP, ZP = P
    XQ, YQ, ZQ = Q
    return sp.expand(
        XP*XQ**2*ZP**2
        - 2*YP*YQ*ZP*ZQ
        + XP**2*XQ*ZQ**2
        + A*XQ*ZP**4*ZQ**2
        + A*XP*ZP**2*ZQ**4
        + 2*B*ZP**4*ZQ**4
    )

def Rm(m: int):
    return (phi(m), omega(m), getpsi(m))

def quotient_by_F_in_Y(expr):
    """Return q such that expr = q*F, proving the remainder is zero, with F monic in Y."""
    q, r = sp.div(
        sp.Poly(sp.expand(expr), Y, domain=sp.QQ[A, B, X]),
        sp.Poly(F, Y, domain=sp.QQ[A, B, X]),
    )
    assert r.as_expr() == 0, f'nonzero remainder: {r.as_expr()}'
    q_expr = sp.expand(q.as_expr())
    # Check q has integer coefficients.
    sp.Poly(q_expr, X, Y, A, B, domain=sp.ZZ)
    return q_expr

PRINT_Q3 = False
P = (X, Y, sp.Integer(1))

quotients = {}
for m in (2, 3):
    expr = sp.expand(addX(P, Rm(m)) - getpsi(m - 1)**2 * phi(m + 1))
    Qm = quotient_by_F_in_Y(expr)
    quotients[m] = Qm
    print(f'm={m}: remainder zero')
    print(f'm={m}: Q terms = {len(sp.Poly(Qm, X, Y, A, B).terms())}')
    print(f'm={m}: deg_Y(Q) = {sp.Poly(Qm, Y).degree()}')

print('Q2 =', quotients[2])
print('Q2 factored =', sp.factor(quotients[2]))

if PRINT_Q3:
    print('Q3 =', quotients[3])

assert quotients[2] == 32*X**3*Y**2 + 32*A*X*Y**2 + 32*B*Y**2
print('OK')
```

## Verification output

Running the script prints:

```text
m=2: remainder zero
m=2: Q terms = 3
m=2: deg_Y(Q) = 2
m=3: remainder zero
m=3: Q terms = 58
m=3: deg_Y(Q) = 4
Q2 = 32*A*X*Y**2 + 32*B*Y**2 + 32*X**3*Y**2
Q2 factored = 32*Y**2*(A*X + B + X**3)
OK
```
