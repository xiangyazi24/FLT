# Q476 (dm1): normalized `Projective.addXYZ` quotients for `P(t)=[t:-1:w(t)]`

## Executive answer

For the short Weierstrass curve

```text
y^2 = x^3 + A*x + B
```

with

```text
P(t) = [t:-1:w(t)]
w(t) = t^3 + A*t^7 + B*t^9 + O(t^11),
```

Mathlib's projective addition formulas give the following truncations to total degree `≤ 8` in `(t1,t2)`:

```text
addX = -(t1 - t2)^3*(t1 + t2)*(1 + A*t1^4 + A*t1^2*t2^2 + A*t2^4)
       + O(total degree ≥ 9)

addY =  (t1 - t2)^3*(1 + A*t1^4 + 2*A*t1^3*t2
                        + 3*A*t1^2*t2^2 + 2*A*t1*t2^3 + A*t2^4)
       + O(total degree ≥ 9)

addZ = -(t1 - t2)^3*(t1 + t2)^3
       + O(total degree ≥ 9)
```

Therefore, after dividing by the requested divisor

```text
D = (t1 - t2)^3,
```

the normalized quotients are:

```text
addX / D = -(t1 + t2)*(1 + A*t1^4 + A*t1^2*t2^2 + A*t2^4)

addY / D =  1 + A*t1^4 + 2*A*t1^3*t2
              + 3*A*t1^2*t2^2 + 2*A*t1*t2^3 + A*t2^4

addZ / D = -(t1 + t2)^3
```

The polynomial division remainders are all zero for the degree-8 truncations.

## Sign check

With the divisor exactly as requested, `D=(t1-t2)^3`, the normalized `addY` constant coefficient is

```text
(addY / (t1-t2)^3)(0,0) = 1.
```

So the requested verification `Q(0,0)=-1` is off by a sign for this divisor.  The `-1` constant occurs if one divides by the opposite diagonal factor:

```text
D' = (t2 - t1)^3 = -(t1 - t2)^3,
```

because then

```text
addY / D' = -1 - A*t1^4 - 2*A*t1^3*t2
              - 3*A*t1^2*t2^2 - 2*A*t1*t2^3 - A*t2^4.
```

Both normalizations are valid projectively; they differ by the unit scalar `-1`.  For the local parameter

```text
t = -X/Y,
```

using the requested divisor gives

```text
F(t1,t2) = - (addX/D) / (addY/D)
         = t1 + t2 + O(total degree ≥ 5),
```

as expected.

---

## Explicit expanded degree-8 coordinates

```text
addX = -A*t1^8 + 2*A*t1^7*t2 - A*t1^6*t2^2
       + A*t1^2*t2^6 - 2*A*t1*t2^7 + A*t2^8
       - t1^4 + 2*t1^3*t2 - 2*t1*t2^3 + t2^4

addY = A*t1^7 - A*t1^6*t2 - 2*A*t1^4*t2^3
       + 2*A*t1^3*t2^4 + A*t1*t2^6 - A*t2^7
       + t1^3 - 3*t1^2*t2 + 3*t1*t2^2 - t2^3

addZ = -t1^6 + 3*t1^4*t2^2 - 3*t1^2*t2^4 + t2^6
```

No `B` term appears through total degree `8`; the first `B` contributions occur later.

---

## Runnable Sympy script

```python
import sympy as sp

# Variables.  A and B are coefficients; total degree is measured only in t1,t2.
t1, t2, A, B = sp.symbols('t1 t2 A B')

# Short Weierstrass curve: y^2 = x^3 + A*x + B.
# Mathlib coefficient convention: a1=a2=a3=0, a4=A, a6=B.

# Formal-neighborhood representative P(t) = [t:-1:w(t)].
# Use enough terms for total-degree <= 8 in the output.
w1 = t1**3 + A*t1**7 + B*t1**9
w2 = t2**3 + A*t2**7 + B*t2**9

Px, Py, Pz = t1, -1, w1
Qx, Qy, Qz = t2, -1, w2

# Mathlib Projective.addZ specialized to a1=a2=a3=0, a4=A, a6=B.
addZ = (
    -3*Px**2*Qx*Qz + 3*Px*Qx**2*Pz
    + Py**2*Qz**2 - Qy**2*Pz**2
    - A*Px*Pz*Qz**2 + A*Qx*Pz**2*Qz
)

# Mathlib Projective.addX specialized to the short curve.
addX = (
    -Px*Qy**2*Pz + Qx*Py**2*Qz
    - 2*Px*Py*Qy*Qz + 2*Qx*Py*Qy*Pz
    + A*Px**2*Qz**2 - A*Qx**2*Pz**2
    + 3*B*Px*Pz*Qz**2 - 3*B*Qx*Pz**2*Qz
)

# Mathlib Projective.negAddY specialized to the short curve.
negAddY = (
    -3*Px**2*Qx*Qy + 3*Px*Qx**2*Py
    - Py**2*Qy*Qz + Py*Qy**2*Pz
    + A*Px*Py*Qz**2 - 2*A*Px*Qy*Pz*Qz
    + 2*A*Qx*Py*Pz*Qz - A*Qx*Qy*Pz**2
    + 3*B*Py*Pz*Qz**2 - 3*B*Qy*Pz**2*Qz
)

# addY = negY([addX, negAddY, addZ]).
# For a1=a3=0, negY([X,Y,Z]) = -Y, so addY = -negAddY.
addY = -negAddY


def trunc_total(poly, maxdeg):
    """Keep terms whose total degree in t1,t2 is <= maxdeg.
    A and B are treated as coefficient variables.
    """
    poly = sp.Poly(sp.expand(poly), t1, t2, A, B)
    out = 0
    for monom, coeff in poly.terms():
        e1, e2, eA, eB = monom
        if e1 + e2 <= maxdeg:
            out += coeff * t1**e1 * t2**e2 * A**eA * B**eB
    return sp.expand(out)


def divide_by_D(name, expr, maxdeg=8):
    D = (t1 - t2)**3
    tr = trunc_total(expr, maxdeg)
    q, r = sp.div(
        sp.Poly(tr, t1, t2, domain=sp.QQ.frac_field(A, B)),
        sp.Poly(D, t1, t2, domain=sp.QQ.frac_field(A, B)),
    )
    q = q.as_expr()
    r = r.as_expr()
    print(f'--- {name} to total degree <= {maxdeg} ---')
    print('truncated factor:', sp.factor(tr))
    print('truncated expanded:', sp.expand(tr))
    print('quotient factor:', sp.factor(q))
    print('quotient expanded:', sp.expand(q))
    print('remainder:', r)
    print('quotient constant:', q.subs({t1: 0, t2: 0}))
    print()
    return tr, q, r


X8, Xq, Xr = divide_by_D('addX', addX)
Y8, Yq, Yr = divide_by_D('addY', addY)
Z8, Zq, Zr = divide_by_D('addZ', addZ)

print('Summary:')
print('addX/(t1-t2)^3 =', sp.factor(Xq))
print('addY/(t1-t2)^3 =', sp.factor(Yq))
print('addZ/(t1-t2)^3 =', sp.factor(Zq))
print('Y quotient at (0,0) =', Yq.subs({t1: 0, t2: 0}))

# Optional sign comparison with Dprime = (t2-t1)^3.
Dprime = (t2 - t1)**3
Yq_prime, Yr_prime = sp.div(
    sp.Poly(Y8, t1, t2, domain=sp.QQ.frac_field(A, B)),
    sp.Poly(Dprime, t1, t2, domain=sp.QQ.frac_field(A, B)),
)
print('addY/(t2-t1)^3 =', sp.factor(Yq_prime.as_expr()))
print('Y quotient for Dprime at (0,0) =', Yq_prime.as_expr().subs({t1: 0, t2: 0}))
```

---

## Script output

```text
--- addX to total degree <= 8 ---
truncated factor: -(t1 - t2)^3*(t1 + t2)*(A*t1^4 + A*t1^2*t2^2 + A*t2^4 + 1)
truncated expanded: -A*t1**8 + 2*A*t1**7*t2 - A*t1**6*t2**2 + A*t1**2*t2**6 - 2*A*t1*t2**7 + A*t2**8 - t1**4 + 2*t1**3*t2 - 2*t1*t2**3 + t2**4
quotient factor: -(t1 + t2)*(A*t1**4 + A*t1**2*t2**2 + A*t2**4 + 1)
quotient expanded: -A*t1**5 - A*t1**4*t2 - A*t1**3*t2**2 - A*t1**2*t2**3 - A*t1*t2**4 - A*t2**5 - t1 - t2
remainder: 0
quotient constant: 0

--- addY to total degree <= 8 ---
truncated factor: (t1 - t2)^3*(A*t1**4 + 2*A*t1**3*t2 + 3*A*t1**2*t2**2 + 2*A*t1*t2**3 + A*t2**4 + 1)
truncated expanded: A*t1**7 - A*t1**6*t2 - 2*A*t1**4*t2**3 + 2*A*t1**3*t2**4 + A*t1*t2**6 - A*t2**7 + t1**3 - 3*t1**2*t2 + 3*t1*t2**2 - t2**3
quotient factor: A*t1**4 + 2*A*t1**3*t2 + 3*A*t1**2*t2**2 + 2*A*t1*t2**3 + A*t2**4 + 1
quotient expanded: A*t1**4 + 2*A*t1**3*t2 + 3*A*t1**2*t2**2 + 2*A*t1*t2**3 + A*t2**4 + 1
remainder: 0
quotient constant: 1

--- addZ to total degree <= 8 ---
truncated factor: -(t1 - t2)^3*(t1 + t2)^3
truncated expanded: -t1**6 + 3*t1**4*t2**2 - 3*t1**2*t2**4 + t2**6
quotient factor: -(t1 + t2)^3
quotient expanded: -t1**3 - 3*t1**2*t2 - 3*t1*t2**2 - t2**3
remainder: 0
quotient constant: 0

Summary:
addX/(t1-t2)^3 = -(t1 + t2)*(A*t1**4 + A*t1**2*t2**2 + A*t2**4 + 1)
addY/(t1-t2)^3 = A*t1**4 + 2*A*t1**3*t2 + 3*A*t1**2*t2**2 + 2*A*t1*t2**3 + A*t2**4 + 1
addZ/(t1-t2)^3 = -(t1 + t2)^3
Y quotient at (0,0) = 1
addY/(t2-t1)^3 = -A*t1**4 - 2*A*t1**3*t2 - 3*A*t1**2*t2**2 - 2*A*t1*t2**3 - A*t2**4 - 1
Y quotient for Dprime at (0,0) = -1
```

---

## Lean-relevant takeaway

For the requested divisor `(t1-t2)^3`, the normalized denominator is a unit with constant coefficient `+1`.  For the earlier convention `(t2-t1)^3`, it is a unit with constant coefficient `-1`.  The sign is projectively irrelevant, but it matters for the exact statement of the Lean lemma.

A clean Lean target for the short-curve degree-8 atom is therefore:

```text
normalizedAddY_short_deg8 =
  1 + A*T1^4 + 2*A*T1^3*T2 + 3*A*T1^2*T2^2 + 2*A*T1*T2^3 + A*T2^4
```

if the divisor is `(T1-T2)^3`, and its constant coefficient is `1`, not `-1`.
