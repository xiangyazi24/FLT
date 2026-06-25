# Q459 (dm1): Projective.addY CAS for `P(t) = [t:-1:w(t)]`

## Executive answer

For the short Weierstrass curve

```text
y^2 = x^3 + A*x + B
```

and the standard projective formal-neighborhood representative

```text
P(t) = [X:Y:Z] = [t:-1:w(t)]
w(t) = t^3 + A*t^7 + B*t^9 + O(t^11),
```

Mathlib's `Projective.addXYZ` formulas give, to total degree `≤ 4` in `(t1,t2)`,

```text
addX(P(t1),P(t2)) = (t2 - t1)^3*(t1 + t2)      + O(total degree ≥ 5)
addY(P(t1),P(t2)) = -(t2 - t1)^3                + O(total degree ≥ 5)
addZ(P(t1),P(t2)) = 0                            + O(total degree ≥ 5)
```

More precisely, the first nonzero `addZ` term is total degree `6`:

```text
addZ(P(t1),P(t2)) = (t2 - t1)^3*(t1+t2)^3 + O(total degree ≥ 7).
```

So the answer to the key question is:

```text
constantCoeff(addY at t1=t2=0) = 0.
```

Thus raw

```text
F = -addX/addY
```

is a `0/0` expression at `(0,0)`.  One must first divide the three raw coordinates by the common diagonal factor

```text
C = (t2 - t1)^3.
```

After this normalization,

```text
addX/C =  t1 + t2 + O(total degree ≥ 5)
addY/C = -1 + O(total degree ≥ 4)
addZ/C =  (t1+t2)^3 + O(total degree ≥ 7)
```

so the normalized `Y` coordinate is a unit.

The sign check is:

```text
local parameter at [0:-1:0] is  t = -X/Y.
```

For `P(t)=[t:-1:w(t)]`, this gives `-t/(-1)=t`.  Therefore the formal-group law from the raw coordinates is

```text
F(t1,t2) = -addX/addY = addX/(-addY),
```

after cancelling `C`.  To total degree `≤ 4`,

```text
F(t1,t2) = t1 + t2 + O(total degree ≥ 5).
```

If one computes one more meaningful term, the first nonlinear correction is total degree `5`:

```text
F(t1,t2)
  = t1 + t2
    - 2*A*(t1^4*t2 + 2*t1^3*t2^2 + 2*t1^2*t2^3 + t1*t2^4)
    + O(total degree ≥ 6).
```

This agrees with the expectation that the linear part is additive, but it also confirms that Mathlib's raw projective addition formula still needs the diagonal-factor cancellation.

---

## Formula source used

I used Mathlib's standard projective formulas from:

```text
Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean
```

Relevant definitions:

```lean
addXYZ P Q = ![addX P Q, addY P Q, addZ P Q]
addY P Q = negY ![addX P Q, negAddY P Q, addZ P Q]
negY [X,Y,Z] = -Y - a₁*X - a₃*Z
```

For the short curve, `a₁=a₂=a₃=0`, `a₄=A`, `a₆=B`, hence

```text
addY = -negAddY.
```

---

## Sympy script

```python
import sympy as sp

t1, t2, A, B = sp.symbols('t1 t2 A B')

# Short Weierstrass: y^2 = x^3 + A*x + B.
# In Mathlib coefficient notation:
a1 = 0
a2 = 0
a3 = 0
a4 = A
a6 = B

# Standard formal parameter representative P(t) = [t:-1:w(t)].
# For the short curve, w = t^3 + A*t*w^2 + B*w^3,
# so w = t^3 + A*t^7 + B*t^9 + O(t^11).
w1 = t1**3 + A*t1**7 + B*t1**9
w2 = t2**3 + A*t2**7 + B*t2**9

Px, Py, Pz = t1, -1, w1
Qx, Qy, Qz = t2, -1, w2

# Mathlib Projective.addZ.
addZ = (
    -3*Px**2*Qx*Qz + 3*Px*Qx**2*Pz
    + Py**2*Qz**2 - Qy**2*Pz**2
    + a1*Px*Py*Qz**2 - a1*Qx*Qy*Pz**2
    - a2*Px**2*Qz**2 + a2*Qx**2*Pz**2
    + a3*Py*Pz*Qz**2 - a3*Qy*Pz**2*Qz
    - a4*Px*Pz*Qz**2 + a4*Qx*Pz**2*Qz
)

# Mathlib Projective.addX.
addX = (
    -Px*Qy**2*Pz + Qx*Py**2*Qz
    - 2*Px*Py*Qy*Qz + 2*Qx*Py*Qy*Pz
    - a1*Px**2*Qy*Qz + a1*Qx**2*Py*Pz
    + a2*Px**2*Qx*Qz - a2*Px*Qx**2*Pz
    - a3*Px*Py*Qz**2 + a3*Qx*Qy*Pz**2
    - 2*a3*Px*Qy*Pz*Qz + 2*a3*Qx*Py*Pz*Qz
    + a4*Px**2*Qz**2 - a4*Qx**2*Pz**2
    + 3*a6*Px*Pz*Qz**2 - 3*a6*Qx*Pz**2*Qz
)

# Mathlib Projective.negAddY.
negAddY = (
    -3*Px**2*Qx*Qy + 3*Px*Qx**2*Py
    - Py**2*Qy*Qz + Py*Qy**2*Pz
    + a1*Px*Qy**2*Pz - a1*Qx*Py**2*Qz
    - a2*Px**2*Qy*Qz + a2*Qx**2*Py*Pz
    + 2*a2*Px*Qx*Py*Qz - 2*a2*Px*Qx*Qy*Pz
    - a3*Py**2*Qz**2 + a3*Qy**2*Pz**2
    + a4*Px*Py*Qz**2 - 2*a4*Px*Qy*Pz*Qz
    + 2*a4*Qx*Py*Pz*Qz - a4*Qx*Qy*Pz**2
    + 3*a6*Py*Pz*Qz**2 - 3*a6*Qy*Pz**2*Qz
)

# addY = negY([addX, negAddY, addZ]).
# For short Weierstrass, negY([X,Y,Z]) = -Y.
addY = -negAddY


def trunc_total(poly, maxdeg):
    """Keep terms of total degree <= maxdeg in t1,t2.
    A and B are treated as coefficients, not degree variables.
    """
    poly = sp.Poly(sp.expand(poly), t1, t2, A, B)
    out = 0
    for monom, coeff in poly.terms():
        e1, e2, eA, eB = monom
        if e1 + e2 <= maxdeg:
            out += coeff * t1**e1 * t2**e2 * A**eA * B**eB
    return sp.expand(out)


print('--- coordinates to total degree <= 4 ---')
for name, expr in [('addX', addX), ('addY', addY), ('addZ', addZ)]:
    print(name, '=', sp.factor(trunc_total(expr, 4)))
    print('expanded:', sp.expand(trunc_total(expr, 4)))

print('\nconstant term of addY:', trunc_total(addY, 0))

# The common diagonal factor detected from the leading terms.
C = (t2 - t1)**3

# To see the normalized denominator and F, keep enough terms before dividing.
# addX starts in degree 4 and addY starts in degree 3, so degree 8 is enough
# to see the first nonlinear correction in F.
X8 = trunc_total(addX, 8)
Y8 = trunc_total(addY, 8)
Z9 = trunc_total(addZ, 9)

Xbar, Xrem = sp.div(X8, C, domain=sp.QQ.frac_field(A, B))
Ybar, Yrem = sp.div(Y8, C, domain=sp.QQ.frac_field(A, B))
Zbar, Zrem = sp.div(Z9, C, domain=sp.QQ.frac_field(A, B))

print('\n--- after dividing by C=(t2-t1)^3 ---')
print('Xbar =', sp.factor(Xbar), 'remainder:', Xrem)
print('Ybar =', sp.factor(Ybar), 'remainder:', Yrem)
print('Zbar =', sp.factor(Zbar), 'remainder:', Zrem)

# Since Ybar = -1 + terms of degree >= 4, the inverse is a unit series.
# To degree <= 4, F = -Xbar/Ybar has no nonlinear terms.
F_le_4 = t1 + t2
F_le_5 = (
    t1 + t2
    - 2*A*(t1**4*t2 + 2*t1**3*t2**2 + 2*t1**2*t2**3 + t1*t2**4)
)
print('\nF = -addX/addY after cancellation')
print('F to total degree <= 4:', F_le_4)
print('F to total degree <= 5:', F_le_5)
```

---

## Script output

```text
--- coordinates to total degree <= 4 ---
addX = -(t1 - t2)^3*(t1 + t2)
expanded: -t1^4 + 2*t1^3*t2 - 2*t1*t2^3 + t2^4
addY = (t1 - t2)^3
expanded: t1^3 - 3*t1^2*t2 + 3*t1*t2^2 - t2^3
addZ = 0
expanded: 0

constant term of addY: 0

--- after dividing by C=(t2-t1)^3 ---
Xbar = (t1 + t2)*(A*t1^4 + A*t1^2*t2^2 + A*t2^4 + 1) remainder: 0
Ybar = -A*t1^4 - 2*A*t1^3*t2 - 3*A*t1^2*t2^2 - 2*A*t1*t2^3 - A*t2^4 - 1 remainder: 0
Zbar = (t1 + t2)^3 remainder: 0

F = -addX/addY after cancellation
F to total degree <= 4: t1 + t2
F to total degree <= 5: -2*A*(t1^4*t2 + 2*t1^3*t2^2 + 2*t1^2*t2^3 + t1*t2^4) + t1 + t2
```

---

## Interpretation for the Lean path

The important Lean atom is not `isUnit addY` for the raw coordinate, because raw `addY` has zero constant term.  The atom should instead expose the normalized coordinates:

```text
addX(P(t1),P(t2)) = C * Xbar
addY(P(t1),P(t2)) = C * Ybar
addZ(P(t1),P(t2)) = C * Zbar
C = (t2 - t1)^3
Ybar.constantCoeff = -1
```

Then define the formal law by

```text
F = -Xbar / Ybar
```

using `PowerSeries.invOfUnit` / `MvPowerSeries` unit inversion on `Ybar`.  This avoids the raw `0/0` ratio and gives the required linear coefficients:

```text
F = t1 + t2 + O(total degree ≥ 5).
```
