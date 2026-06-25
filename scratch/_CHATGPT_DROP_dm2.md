# Q199 (dm2): CAS verification for short-Weierstrass projective division-polynomial addX/addY

## Executive result

I checked the requested Mathlib `Jacobian.addX/addY` identities for the short Weierstrass curve

```text
Y^2 = X^3 + A X + B.
```

There is an important correction:

```text
ω_m = (ψ_{m+2} ψ_{m-1}^2 - ψ_{m-2} ψ_{m+1}^2) / (4 ψ_m)
```

is **not** a polynomial formula for the standard projective representative `[φ_m, ω_m, ψ_m]`.  In fact, with this denominator, `ω_3`, `ω_4`, and `ω_5` are not in `K[X,Y]`.  The `m=2` quotient is polynomial, but it is off by a factor of `1/2`, and the `addX` identity already fails.

The standard short-Weierstrass formula is

```text
ω_m = (ψ_{m+2} ψ_{m-1}^2 - ψ_{m-2} ψ_{m+1}^2) / (4Y)
    = (ψ_{m+2} ψ_{m-1}^2 - ψ_{m-2} ψ_{m+1}^2) / (2ψ_2).
```

With that corrected denominator, the identities

```text
addX([X,Y,1], [φ_m,ω_m,ψ_m]) ≡ ψ_{m-1}^2 φ_{m+1}     mod F_W
addY([X,Y,1], [φ_m,ω_m,ψ_m]) ≡ ψ_{m-1}^3 ω_{m+1}     mod F_W
```

are all verified for `m = 2,3,4`.

## Runnable Python/SymPy script

```python
import sympy as sp

X, Y, A, B = sp.symbols("X Y A B")
FW = Y**2 - X**3 - A*X - B


def rem_curve(poly):
    """Remainder modulo Y^2 - X^3 - A*X - B, treating it as monic in Y."""
    return sp.expand(sp.rem(sp.Poly(sp.expand(poly), Y), sp.Poly(FW, Y)).as_expr())


def is_zero_mod_curve(poly):
    return rem_curve(poly) == 0


def exact_div(num, den):
    """Exact polynomial division in QQ[Y,X,A,B]."""
    q, r = sp.div(sp.expand(num), sp.expand(den), Y, X, A, B, domain=sp.QQ)
    return sp.expand(q), sp.expand(r)


# Short-Weierstrass division polynomials.
psi = {
    0: sp.Integer(0),
    1: sp.Integer(1),
    2: 2*Y,
    3: 3*X**4 + 6*A*X**2 + 12*B*X - A**2,
    4: 4*Y*(X**6 + 5*A*X**4 + 20*B*X**3 - 5*A**2*X**2
             - 4*A*B*X - 8*B**2 - A**3),
}

# Need up to psi_7, because the Y-check for m=4 uses omega_5.
for n in range(5, 8):
    if n % 2:
        m = (n - 1) // 2
        psi[n] = sp.expand(psi[m+2]*psi[m]**3 - psi[m-1]*psi[m+1]**3)
    else:
        m = n // 2
        q, r = exact_div(
            psi[m] * (psi[m+2]*psi[m-1]**2 - psi[m-2]*psi[m+1]**2),
            2*Y,
        )
        assert r == 0
        psi[n] = q

# phi_m = X*psi_m^2 - psi_{m+1}*psi_{m-1}
phi = {m: sp.expand(X*psi[m]**2 - psi[m+1]*psi[m-1]) for m in range(1, 6)}


def omega_numerator(m):
    return sp.expand(psi[m+2]*psi[m-1]**2 - psi[m-2]*psi[m+1]**2)


# User-requested denominator: 4*psi_m.
# This is checked for exact polynomial quotient; it is not exact for m=3,4,5.
omega_user = {}
omega_user_ok = {}
for m in range(2, 6):
    q, r = exact_div(omega_numerator(m), 4*psi[m])
    omega_user[m] = q
    omega_user_ok[m] = (r == 0)

# Standard short-Weierstrass denominator: 4Y = 2*psi_2.
omega_std = {}
for m in range(2, 6):
    q, r = exact_div(omega_numerator(m), 4*Y)
    assert r == 0
    omega_std[m] = q


# Mathlib Jacobian.addX/addY specialized to a1=a2=a3=0, a4=A, a6=B.
# Variables are Jacobian coordinates P=[P0,P1,P2], Q=[Q0,Q1,Q2]
# with affine coordinates x=P0/P2^2, y=P1/P2^3.
def jac_addX(P, Q):
    P0, P1, P2 = P
    Q0, Q1, Q2 = Q
    return sp.expand(
        P0*Q0**2*P2**2
        - 2*P1*Q1*P2*Q2
        + P0**2*Q0*Q2**2
        + A*Q0*P2**4*Q2**2
        + A*P0*P2**2*Q2**4
        + 2*B*P2**4*Q2**4
    )


def jac_negAddY(P, Q):
    P0, P1, P2 = P
    Q0, Q1, Q2 = Q
    return sp.expand(
        -P1*Q0**3*P2**3
        + 2*P1*Q1**2*P2**3
        - 3*P0**2*Q0*Q1*P2**2*Q2
        + 3*P0*P1*Q0**2*P2*Q2**2
        + P0**3*Q1*Q2**3
        - 2*P1**2*Q1*Q2**3
        - A*Q0*Q1*P2**6*Q2
        - A*P0*Q1*P2**4*Q2**3
        + A*P1*Q0*P2**3*Q2**4
        + A*P0*P1*P2*Q2**6
        - 2*B*Q1*P2**6*Q2**3
        + 2*B*P1*P2**3*Q2**6
    )


def jac_addY(P, Q):
    # For short Weierstrass, Jacobian.negY([X,Y,Z]) = -Y,
    # so addY = -negAddY.
    return sp.expand(-jac_negAddY(P, Q))


P = [X, Y, sp.Integer(1)]

print("USER omega_m = numerator/(4*psi_m): polynomial exactness")
for m in range(2, 6):
    print(f"omega_{m}: {'POLYNOMIAL' if omega_user_ok[m] else 'NOT_POLYNOMIAL'}")

print("\nVerification using USER omega where polynomial:")
for m in [2, 3, 4]:
    if not omega_user_ok[m]:
        print(f"m={m} X: NO (omega_{m} is not a polynomial)")
    else:
        Q = [phi[m], omega_user[m], psi[m]]
        ok = is_zero_mod_curve(jac_addX(P, Q) - psi[m-1]**2 * phi[m+1])
        print(f"m={m} X: {'YES' if ok else 'NO'}")

    if not (omega_user_ok[m] and omega_user_ok[m+1]):
        bad = [f"omega_{j}" for j in (m, m+1) if not omega_user_ok[j]]
        print(f"m={m} Y: NO ({', '.join(bad)} not polynomial)")
    else:
        Q = [phi[m], omega_user[m], psi[m]]
        ok = is_zero_mod_curve(jac_addY(P, Q) - psi[m-1]**3 * omega_user[m+1])
        print(f"m={m} Y: {'YES' if ok else 'NO'}")

print("\nVerification using STANDARD omega_m = numerator/(4*Y) = numerator/(2*psi_2):")
for m in [2, 3, 4]:
    Q = [phi[m], omega_std[m], psi[m]]
    okx = is_zero_mod_curve(jac_addX(P, Q) - psi[m-1]**2 * phi[m+1])
    oky = is_zero_mod_curve(jac_addY(P, Q) - psi[m-1]**3 * omega_std[m+1])
    print(f"m={m} X: {'YES' if okx else 'NO'}")
    print(f"m={m} Y: {'YES' if oky else 'NO'}")
```

## Output

```text
USER omega_m = numerator/(4*psi_m): polynomial exactness
omega_2: POLYNOMIAL
omega_3: NOT_POLYNOMIAL
omega_4: NOT_POLYNOMIAL
omega_5: NOT_POLYNOMIAL

Verification using USER omega where polynomial:
m=2 X: NO
m=2 Y: NO (omega_3 not polynomial)
m=3 X: NO (omega_3 is not a polynomial)
m=3 Y: NO (omega_3, omega_4 not polynomial)
m=4 X: NO (omega_4 is not a polynomial)
m=4 Y: NO (omega_4, omega_5 not polynomial)

Verification using STANDARD omega_m = numerator/(4*Y) = numerator/(2*psi_2):
m=2 X: YES
m=2 Y: YES
m=3 X: YES
m=3 Y: YES
m=4 X: YES
m=4 Y: YES
```

## Diagnosis

The requested projective representative

```text
R_m = [φ_m, ω_m, ψ_m]
```

is correct for the standard division-polynomial `ω_m`, but the denominator in the prompt is not the standard one.  For the short Weierstrass curve, the standard formula is

```text
4Y * ω_m = ψ_{m+2} ψ_{m-1}^2 - ψ_{m-2} ψ_{m+1}^2.
```

Since `ψ_2 = 2Y`, this is equivalently

```text
2ψ_2 * ω_m = ψ_{m+2} ψ_{m-1}^2 - ψ_{m-2} ψ_{m+1}^2.
```

It is **not**

```text
4ψ_m * ω_m = ψ_{m+2} ψ_{m-1}^2 - ψ_{m-2} ψ_{m+1}^2.
```

So the requested identities fail as stated, but the corrected standard `ω_m` verifies all six `m=2,3,4` `addX/addY` identities modulo `F_W`.
