# Q28 (dm2): Keystone diff-add numerator cofactors — ODD branch, INTEGER lift

This is the ODD branch with generators ordered as

```text
Adj0, Inv0, Adj1, Inv1, bRel
```

## Method / order used

The Q18 QQ lift used a lex order whose leading term for `c3` was `3*x**4`, which forced `/3` when the Groebner-basis element corresponding to the `Adj1`/`Inv1` S-polynomial was normalized.  For this integer version I used an extended Buchberger-style lift over `ZZ` with exact coefficient division only, and **did not normalize nonunit leading coefficients**.

The lex order used by the integer lift is

```text
Pm2, P3, Pm1, P2, P0, P1, b2, b6, b4, b8, x
```

This order makes the leading `c3` terms use the `b2*x**3` coefficient where possible, and makes `bRel` lead with `b2*b6`; both are unit-leading over `ZZ`.  Some generated S-polynomial remainders still have leading coefficient `3`, but the reduction keeps them as integer polynomials and only reduces a term when the leading coefficient divides exactly.  The script tracks every generated basis element as a `ZZ[V]`-linear combination of the original five generators.  It then reduces `G` to zero and converts the lift back to cofactors for exactly

```python
Adj0, Inv0, Adj1, Inv1, bRel
```

The computed integer basis has length `10` and processes `45` S-pairs.  The final script verifies

```python
sp.expand(G - (q0*Adj0 + q1*Inv0 + q2*Adj1 + q3*Inv1 + q4*bRel)) == 0
```

and asserts that every coefficient denominator is `1`.

## Self-contained script

```python
import math
from collections import deque
import sympy as sp

Pm2, Pm1, P0, P1, P2, P3, x, b2, b4, b6, b8 = sp.symbols(
    'Pm2 Pm1 P0 P1 P2 P3 x b2 b4 b6 b8'
)

# Integer-lift order.  In this lex order the b2-leading terms of c3 and bRel
# have unit leading coefficient.  Nonunit remainders are retained; the code never
# normalizes by dividing by 2 or 3.
V = [Pm2, P3, Pm1, P2, P0, P1, b2, b6, b4, b8, x]
USER_VARS = [Pm2, Pm1, P0, P1, P2, P3, x, b2, b4, b6, b8]

def poly(expr):
    return sp.Poly(sp.expand(expr), *V, domain=sp.ZZ)

def zero():
    return sp.Poly(0, *V, domain=sp.ZZ)

def monomial_poly(coeff, mon):
    coeff = int(coeff)
    if coeff == 0:
        return zero()
    return sp.Poly.from_dict({tuple(mon): coeff}, V, domain=sp.ZZ)

def lm_lc(f):
    return f.terms()[0]

def divides(a, b):
    return all(ai <= bi for ai, bi in zip(a, b))

def submon(b, a):
    return tuple(bi - ai for ai, bi in zip(a, b))

def lcmmon(a, b):
    return tuple(max(ai, bi) for ai, bi in zip(a, b))

def reduce_exact(f, basis):
    qs = [zero() for _ in basis]
    r = zero()
    p = f
    while not p.is_zero:
        m, c = lm_lc(p)
        reduced = False
        for i, g in enumerate(basis):
            mg, cg = lm_lc(g)
            if divides(mg, m) and c % cg == 0:
                t = monomial_poly(c // cg, submon(m, mg))
                qs[i] += t
                p -= t * g
                reduced = True
                break
        if not reduced:
            t = monomial_poly(c, m)
            r += t
            p -= t
    return qs, r

def spolynomial(f, g):
    mf, cf = lm_lc(f)
    mg, cg = lm_lc(g)
    m = lcmmon(mf, mg)
    coeff_lcm = abs(cf * cg) // math.gcd(abs(int(cf)), abs(int(cg)))
    tf = monomial_poly(coeff_lcm // cf, submon(m, mf))
    tg = monomial_poly(coeff_lcm // cg, submon(m, mg))
    return tf * f - tg * g, tf, tg

# ODD-branch definitions from the prompt.
s = 4*x**3 + b2*x**2 + 2*b4*x + b6
c3 = 3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8
d4 = (
    2*x**6 + b2*x**5 + 5*b4*x**4 + 10*b6*x**3 + 10*b8*x**2
    + (b2*b8 - b4*b6)*x + (b4*b8 - b6**2)
)

Z0 = P0**2
F0 = x*P0**2 - P1*Pm1*s
Z1 = P1**2*s
F1 = x*P1**2*s - P2*P0

pre2m = P0*(Pm1**2*P2 - Pm2*P1**2)
pre2m2 = P1*(P0**2*P3 - Pm1*P2**2)
deltaP = F0*Z1 - F1*Z0
sumNumP = (
    2*F0*F1*(F0*Z1 + F1*Z0)
    + b2*F0*F1*Z0*Z1
    + b4*Z0*Z1*(F0*Z1 + F1*Z0)
    + b6*Z0**2*Z1**2
)
Phi2m1 = x*deltaP**2 - s*pre2m2*pre2m
diffAddNumP = sumNumP - deltaP**2*x
G = sp.expand(c3*(Phi2m1 - diffAddNumP))

bRel = b2*b6 - b4**2 - 4*b8
Adj0 = sp.expand(Pm2*P2 - s**2*Pm1*P1 + c3*P0**2)
Inv0 = sp.expand(c3*(P2*Pm1**2 + P1**2*Pm2 + P0**3) - (d4 + s**2)*P1*P0*Pm1)
Adj1 = sp.expand(Pm1*P3 - P2*P0 + c3*P1**2)
Inv1 = sp.expand(c3*(P3*P0**2 + P2**2*Pm1 + s**2*P1**3) - (d4 + s**2)*P2*P1*P0)

gens = [poly(Adj0), poly(Inv0), poly(Adj1), poly(Inv1), poly(bRel)]

# Extended integer Buchberger-style lift.  The representation vector reps[i]
# records basis[i] as a Z[V]-linear combination of the original five generators.
basis = list(gens)
reps = []
for i in range(len(gens)):
    ri = [zero() for _ in gens]
    ri[i] = sp.Poly(1, *V, domain=sp.ZZ)
    reps.append(ri)

pairs = deque((i, j) for i in range(len(basis)) for j in range(i))
processed_pairs = 0
while pairs:
    i, j = pairs.popleft()
    processed_pairs += 1
    S, ti, tj = spolynomial(basis[i], basis[j])
    S_rep = [ti*reps[i][k] - tj*reps[j][k] for k in range(len(gens))]
    qs, rem = reduce_exact(S, basis)
    rem_rep = [
        S_rep[k] - sum((qs[a]*reps[a][k] for a in range(len(basis))), zero())
        for k in range(len(gens))
    ]
    if not rem.is_zero:
        # Normalize signs only; do not divide by nonunits.
        if lm_lc(rem)[1] < 0:
            rem = -rem
            rem_rep = [-rr for rr in rem_rep]
        n = len(basis)
        basis.append(rem)
        reps.append(rem_rep)
        for a in range(n):
            pairs.append((n, a))

q_basis, rem = reduce_exact(poly(G), basis)
assert rem.is_zero

q_poly = [
    sum((q_basis[a] * reps[a][k] for a in range(len(basis))), zero())
    for k in range(len(gens))
]
q0, q1, q2, q3, q4 = [sp.expand(q.as_expr()) for q in q_poly]

# Internal representation checks.
for i, b in enumerate(basis):
    assert b == sum((reps[i][k]*gens[k] for k in range(len(gens))), zero())

assert sp.expand(G - (q0*Adj0 + q1*Inv0 + q2*Adj1 + q3*Inv1 + q4*bRel)) == 0
for q in [q0, q1, q2, q3, q4]:
    qq = sp.Poly(q, *USER_VARS, domain=sp.QQ)
    assert all(coeff.q == 1 for _, coeff in qq.terms())

print(f'basis length = {len(basis)}; processed pairs = {processed_pairs}')
for i, q in enumerate([q0, q1, q2, q3, q4]):
    print(f'q{i} = {sp.sstr(q)}')
    print()
print('OK')
```

## Printed integer cofactors and verification output

```text
basis length = 10; processed pairs = 45
q0 = -P0**2*P1**4*b2**3*x**6 - 6*P0**2*P1**4*b2**2*b4*x**5 - 3*P0**2*P1**4*b2**2*b6*x**4 - P0**2*P1**4*b2**2*b8*x**3 - 13*P0**2*P1**4*b2**2*x**7 - 12*P0**2*P1**4*b2*b4**2*x**4 - 10*P0**2*P1**4*b2*b4*b6*x**3 - 3*P0**2*P1**4*b2*b4*b8*x**2 - 55*P0**2*P1**4*b2*b4*x**6 - 36*P0**2*P1**4*b2*b6*x**5 - 14*P0**2*P1**4*b2*b8*x**4 - 54*P0**2*P1**4*b2*x**8 - 9*P0**2*P1**4*b4**3*x**3 - 12*P0**2*P1**4*b4**2*b6*x**2 - 3*P0**2*P1**4*b4**2*b8*x - 57*P0**2*P1**4*b4**2*x**5 - 3*P0**2*P1**4*b4*b6**2*x - P0**2*P1**4*b4*b6*b8 - 69*P0**2*P1**4*b4*b6*x**4 - 28*P0**2*P1**4*b4*b8*x**3 - 120*P0**2*P1**4*b4*x**7 - 18*P0**2*P1**4*b6**2*x**3 - 18*P0**2*P1**4*b6*b8*x**2 - 90*P0**2*P1**4*b6*x**6 - 4*P0**2*P1**4*b8**2*x - 36*P0**2*P1**4*b8*x**5 - 72*P0**2*P1**4*x**9 - 2*P0*P1**3*P2*Pm1*b2**2*x**5 - 10*P0*P1**3*P2*Pm1*b2*b4*x**4 - 8*P0*P1**3*P2*Pm1*b2*b6*x**3 - 2*P0*P1**3*P2*Pm1*b2*b8*x**2 - 14*P0*P1**3*P2*Pm1*b2*x**6 - 12*P0*P1**3*P2*Pm1*b4**2*x**3 - 18*P0*P1**3*P2*Pm1*b4*b6*x**2 - 4*P0*P1**3*P2*Pm1*b4*b8*x - 36*P0*P1**3*P2*Pm1*b4*x**5 - 6*P0*P1**3*P2*Pm1*b6**2*x - 2*P0*P1**3*P2*Pm1*b6*b8 - 30*P0*P1**3*P2*Pm1*b6*x**4 - 8*P0*P1**3*P2*Pm1*b8*x**3 - 24*P0*P1**3*P2*Pm1*x**7

q1 = P0**3*P1*P3*b2*x**2 + 2*P0**3*P1*P3*b4*x + P0**3*P1*P3*b6 + 4*P0**3*P1*P3*x**3 + P0**2*P1**2*P2*b2**2*x**3 + 3*P0**2*P1**2*P2*b2*b4*x**2 + 10*P0**2*P1**2*P2*b2*x**4 + 3*P0**2*P1**2*P2*b4**2*x + P0**2*P1**2*P2*b4*b6 + 16*P0**2*P1**2*P2*b4*x**3 + 6*P0**2*P1**2*P2*b6*x**2 + 4*P0**2*P1**2*P2*b8*x + 24*P0**2*P1**2*P2*x**5 + P0*P1*P2**2*Pm1*b2*x**2 + 2*P0*P1*P2**2*Pm1*b4*x + P0*P1*P2**2*Pm1*b6 + 4*P0*P1*P2**2*Pm1*x**3

q2 = P0**4*P1**2*b2**3*x**6 + 6*P0**4*P1**2*b2**2*b4*x**5 + 3*P0**4*P1**2*b2**2*b6*x**4 + P0**4*P1**2*b2**2*b8*x**3 + 13*P0**4*P1**2*b2**2*x**7 + 12*P0**4*P1**2*b2*b4**2*x**4 + 11*P0**4*P1**2*b2*b4*b6*x**3 + 3*P0**4*P1**2*b2*b4*b8*x**2 + 55*P0**4*P1**2*b2*b4*x**6 + 2*P0**4*P1**2*b2*b6**2*x**2 + P0**4*P1**2*b2*b6*b8*x + 35*P0**4*P1**2*b2*b6*x**5 + 14*P0**4*P1**2*b2*b8*x**4 + 54*P0**4*P1**2*b2*x**8 + 8*P0**4*P1**2*b4**3*x**3 + 10*P0**4*P1**2*b4**2*b6*x**2 + 2*P0**4*P1**2*b4**2*b8*x + 58*P0**4*P1**2*b4**2*x**5 + 3*P0**4*P1**2*b4*b6**2*x + P0**4*P1**2*b4*b6*b8 + 69*P0**4*P1**2*b4*b6*x**4 + 24*P0**4*P1**2*b4*b8*x**3 + 120*P0**4*P1**2*b4*x**7 + 18*P0**4*P1**2*b6**2*x**3 + 10*P0**4*P1**2*b6*b8*x**2 + 90*P0**4*P1**2*b6*x**6 + 40*P0**4*P1**2*b8*x**5 + 72*P0**4*P1**2*x**9 - 2*P0**3*P1*P2*Pm1*b2**2*x**5 - 10*P0**3*P1*P2*Pm1*b2*b4*x**4 - 8*P0**3*P1*P2*Pm1*b2*b6*x**3 - 2*P0**3*P1*P2*Pm1*b2*b8*x**2 - 14*P0**3*P1*P2*Pm1*b2*x**6 - 12*P0**3*P1*P2*Pm1*b4**2*x**3 - 18*P0**3*P1*P2*Pm1*b4*b6*x**2 - 4*P0**3*P1*P2*Pm1*b4*b8*x - 36*P0**3*P1*P2*Pm1*b4*x**5 - 6*P0**3*P1*P2*Pm1*b6**2*x - 2*P0**3*P1*P2*Pm1*b6*b8 - 30*P0**3*P1*P2*Pm1*b6*x**4 - 8*P0**3*P1*P2*Pm1*b8*x**3 - 24*P0**3*P1*P2*Pm1*x**7

q3 = -P0**4*P1*b2*x**2 - 2*P0**4*P1*b4*x - P0**4*P1*b6 - 4*P0**4*P1*x**3

q4 = P0**5*P1**2*P2*b2*x**4 + 3*P0**5*P1**2*P2*b4*x**3 + 3*P0**5*P1**2*P2*b6*x**2 + P0**5*P1**2*P2*b8*x + 3*P0**5*P1**2*P2*x**5 - P0**4*P1**4*b2*b4*x**6 - 2*P0**4*P1**4*b2*b6*x**5 - P0**4*P1**4*b2*b8*x**4 + P0**4*P1**4*b2*x**8 - 3*P0**4*P1**4*b4**2*x**5 - 9*P0**4*P1**4*b4*b6*x**4 - 4*P0**4*P1**4*b4*b8*x**3 - 6*P0**4*P1**4*b6**2*x**3 - 5*P0**4*P1**4*b6*b8*x**2 - 3*P0**4*P1**4*b6*x**6 - P0**4*P1**4*b8**2*x - 2*P0**4*P1**4*b8*x**5 + 3*P0**4*P1**4*x**9 - 3*P0**3*P1**3*P2*Pm1*b2**2*x**5 - 12*P0**3*P1**3*P2*Pm1*b2*b4*x**4 - 7*P0**3*P1**3*P2*Pm1*b2*b6*x**3 - 2*P0**3*P1**3*P2*Pm1*b2*b8*x**2 - 26*P0**3*P1**3*P2*Pm1*b2*x**6 - 12*P0**3*P1**3*P2*Pm1*b4**2*x**3 - 13*P0**3*P1**3*P2*Pm1*b4*b6*x**2 - 3*P0**3*P1**3*P2*Pm1*b4*b8*x - 55*P0**3*P1**3*P2*Pm1*b4*x**5 - 3*P0**3*P1**3*P2*Pm1*b6**2*x - P0**3*P1**3*P2*Pm1*b6*b8 - 39*P0**3*P1**3*P2*Pm1*b6*x**4 - 14*P0**3*P1**3*P2*Pm1*b8*x**3 - 54*P0**3*P1**3*P2*Pm1*x**7 + P0**2*P1**5*Pm1*b2**3*x**8 + 7*P0**2*P1**5*Pm1*b2**2*b4*x**7 + 5*P0**2*P1**5*Pm1*b2**2*b6*x**6 + P0**2*P1**5*Pm1*b2**2*b8*x**5 + 11*P0**2*P1**5*Pm1*b2**2*x**9 + 16*P0**2*P1**5*Pm1*b2*b4**2*x**6 + 22*P0**2*P1**5*Pm1*b2*b4*b6*x**5 + 4*P0**2*P1**5*Pm1*b2*b4*b8*x**4 + 52*P0**2*P1**5*Pm1*b2*b4*x**8 + 7*P0**2*P1**5*Pm1*b2*b6**2*x**4 + 2*P0**2*P1**5*Pm1*b2*b6*b8*x**3 + 38*P0**2*P1**5*Pm1*b2*b6*x**7 + 8*P0**2*P1**5*Pm1*b2*b8*x**6 + 40*P0**2*P1**5*Pm1*b2*x**10 + 12*P0**2*P1**5*Pm1*b4**3*x**5 + 24*P0**2*P1**5*Pm1*b4**2*b6*x**4 + 4*P0**2*P1**5*Pm1*b4**2*b8*x**3 + 60*P0**2*P1**5*Pm1*b4**2*x**7 + 15*P0**2*P1**5*Pm1*b4*b6**2*x**3 + 4*P0**2*P1**5*Pm1*b4*b6*b8*x**2 + 84*P0**2*P1**5*Pm1*b4*b6*x**6 + 16*P0**2*P1**5*Pm1*b4*b8*x**5 + 96*P0**2*P1**5*Pm1*b4*x**9 + 3*P0**2*P1**5*Pm1*b6**3*x**2 + P0**2*P1**5*Pm1*b6**2*b8*x + 27*P0**2*P1**5*Pm1*b6**2*x**5 + 8*P0**2*P1**5*Pm1*b6*b8*x**4 + 72*P0**2*P1**5*Pm1*b6*x**8 + 16*P0**2*P1**5*Pm1*b8*x**7 + 48*P0**2*P1**5*Pm1*x**11 + P0**2*P1**2*P2**2*Pm1**2*b4*x**3 + 2*P0**2*P1**2*P2**2*Pm1**2*b6*x**2 + P0**2*P1**2*P2**2*Pm1**2*b8*x - P0**2*P1**2*P2**2*Pm1**2*x**5

OK
```
