# Q13 (dm2): Keystone diff-add numerator cofactors — ODD branch

This is for the ODD branch with generators ordered as

```text
Adj0, Inv0, Adj1, Inv1, bRel
```

## Method / order used

I used SymPy 1.14 over `QQ`, with a lexicographic Groebner lift in the variable order

```text
Pm2, P3, Pm1, P2, P0, P1, x, b2, b4, b6, b8
```

The input polynomials are the fully expanded ODD-branch polynomials from the prompt.  The Groebner basis has six elements: SymPy's basis is `[g0, g1, g2, g3, h, bRel]`.  Since `bRel` is itself in the basis, SymPy reduces several of `g0`, `g1`, and `g3` modulo `bRel`; the script below tracks those correction terms and converts the Groebner-basis lift back to the original five generators.  The final identity verified is exactly

```python
sp.expand(G - (q0*Adj0 + q1*Inv0 + q2*Adj1 + q3*Inv1 + q4*bRel)) == 0
```

## Self-contained script

```python
import sympy as sp

Pm2, Pm1, P0, P1, P2, P3, x, b2, b4, b6, b8 = sp.symbols(
    'Pm2 Pm1 P0 P1 P2 P3 x b2 b4 b6 b8'
)
# The lift order is lex in this variable sequence.
lift_vars = [Pm2, P3, Pm1, P2, P0, P1, x, b2, b4, b6, b8]

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

# Groebner lift: SymPy returns the six-element lex basis
#   g0, g1, g2, g3, h, bRel.
# The original generator order is Adj0, Inv0, Adj1, Inv1, bRel.
Gb = sp.groebner([Adj0, Inv0, Adj1, Inv1, bRel], *lift_vars, order='lex', domain=sp.QQ)
assert len(Gb.polys) == 6
qg, rem = Gb.reduce(G)
assert sp.expand(rem) == 0

def div_by_bRel(poly):
    q, r = sp.div(sp.expand(poly), bRel, *lift_vars)
    assert sp.expand(r) == 0
    return sp.expand(q)

# Convert the SymPy Groebner-basis lift back to a lift by the original five generators.
a0 = div_by_bRel(Gb.polys[0].as_expr() - Adj0)
a1 = div_by_bRel(Gb.polys[1].as_expr() - Inv0/3)
a3 = div_by_bRel(Gb.polys[3].as_expr() - Inv1/3)
a4 = div_by_bRel(Gb.polys[4].as_expr() - (Pm1*Inv1/3 - P0**2*c3*Adj1/3))
assert Gb.polys[2].as_expr() == Adj1
assert Gb.polys[5].as_expr() == bRel

q0 = sp.expand(qg[0])
q1 = sp.expand(qg[1]/3)
q2 = sp.expand(qg[2] - qg[4]*P0**2*c3/3)
q3 = sp.expand(qg[3]/3 + qg[4]*Pm1/3)
q4 = sp.expand(qg[5] + qg[0]*a0 + qg[1]*a1 + qg[3]*a3 + qg[4]*a4)

for i, qi in enumerate([q0, q1, q2, q3, q4]):
    print(f'q{i} = {sp.sstr(qi)}')
    print()

assert sp.expand(G - (q0*Adj0 + q1*Inv0 + q2*Adj1 + q3*Inv1 + q4*bRel)) == 0
print('OK')
```

## Printed cofactors and verification output

```text
q0 = -P0*P1**3*P2*Pm1*b2**2*x**5 - 5*P0*P1**3*P2*Pm1*b2*b4*x**4 - 4*P0*P1**3*P2*Pm1*b2*b6*x**3 - P0*P1**3*P2*Pm1*b2*b8*x**2 - 7*P0*P1**3*P2*Pm1*b2*x**6 - 6*P0*P1**3*P2*Pm1*b4**2*x**3 - 9*P0*P1**3*P2*Pm1*b4*b6*x**2 - 2*P0*P1**3*P2*Pm1*b4*b8*x - 18*P0*P1**3*P2*Pm1*b4*x**5 - 3*P0*P1**3*P2*Pm1*b6**2*x - P0*P1**3*P2*Pm1*b6*b8 - 15*P0*P1**3*P2*Pm1*b6*x**4 - 4*P0*P1**3*P2*Pm1*b8*x**3 - 12*P0*P1**3*P2*Pm1*x**7

q1 = P0**3*P1*P3*b2*x**2 + 2*P0**3*P1*P3*b4*x + P0**3*P1*P3*b6 + 4*P0**3*P1*P3*x**3

q2 = -P0**4*P1**2*b2**3*b6*x**3/3 + P0**4*P1**2*b2**2*b4**2*x**3/3 - P0**4*P1**2*b2**2*b4*b6*x**2 - P0**4*P1**2*b2**2*b6**2*x - P0**4*P1**2*b2**2*b6*b8/3 + 4*P0**4*P1**2*b2**2*b8*x**3/3 + P0**4*P1**2*b2*b4**3*x**2 + P0**4*P1**2*b2*b4**2*b6*x + P0**4*P1**2*b2*b4**2*b8/3 + 6*P0**4*P1**2*b2*b4*b6*x**3 + 4*P0**4*P1**2*b2*b4*b8*x**2 + 9*P0**4*P1**2*b2*b6**2*x**2 + 8*P0**4*P1**2*b2*b6*b8*x + 4*P0**4*P1**2*b2*b8**2/3 - 6*P0**4*P1**2*b4**3*x**3 - 9*P0**4*P1**2*b4**2*b6*x**2 - 4*P0**4*P1**2*b4**2*b8*x - 24*P0**4*P1**2*b4*b8*x**3 - 36*P0**4*P1**2*b6*b8*x**2 - 16*P0**4*P1**2*b8**2*x - 3*P0**3*P1*P2*Pm1*b2**2*x**5 - 15*P0**3*P1*P2*Pm1*b2*b4*x**4 - 12*P0**3*P1*P2*Pm1*b2*b6*x**3 - 3*P0**3*P1*P2*Pm1*b2*b8*x**2 - 21*P0**3*P1*P2*Pm1*b2*x**6 - 18*P0**3*P1*P2*Pm1*b4**2*x**3 - 27*P0**3*P1*P2*Pm1*b4*b6*x**2 - 6*P0**3*P1*P2*Pm1*b4*b8*x - 54*P0**3*P1*P2*Pm1*b4*x**5 - 9*P0**3*P1*P2*Pm1*b6**2*x - 3*P0**3*P1*P2*Pm1*b6*b8 - 45*P0**3*P1*P2*Pm1*b6*x**4 - 12*P0**3*P1*P2*Pm1*b8*x**3 - 36*P0**3*P1*P2*Pm1*x**7

q3 = -P0**4*P1*b2*x**2 - 2*P0**4*P1*b4*x - P0**4*P1*b6 - 4*P0**4*P1*x**3 + P0**2*P1**2*Pm1*b2**2*b6/3 + P0**2*P1**2*Pm1*b2**2*x**3 - P0**2*P1**2*Pm1*b2*b4**2/3 + 3*P0**2*P1**2*Pm1*b2*b4*x**2 - 3*P0**2*P1**2*Pm1*b2*b6*x - 4*P0**2*P1**2*Pm1*b2*b8/3 + 10*P0**2*P1**2*Pm1*b2*x**4 + 6*P0**2*P1**2*Pm1*b4**2*x + P0**2*P1**2*Pm1*b4*b6 + 16*P0**2*P1**2*Pm1*b4*x**3 + 6*P0**2*P1**2*Pm1*b6*x**2 + 16*P0**2*P1**2*Pm1*b8*x + 24*P0**2*P1**2*Pm1*x**5 + P0*P1*P2*Pm1**2*b2*x**2 + 2*P0*P1*P2*Pm1**2*b4*x + P0*P1*P2*Pm1**2*b6 + 4*P0*P1*P2*Pm1**2*x**3

q4 = -P0**5*P1**2*P2*b2**2*x**3/3 - P0**5*P1**2*P2*b2*b4*x**2 - P0**5*P1**2*P2*b2*b6*x - P0**5*P1**2*P2*b2*b8/3 + P0**5*P1**2*P2*b2*x**4 + 8*P0**5*P1**2*P2*b4*x**3 + 10*P0**5*P1**2*P2*b6*x**2 + 4*P0**5*P1**2*P2*b8*x + 4*P0**5*P1**2*P2*x**5 + P0**4*P1**4*b2**3*x**6/3 + 2*P0**4*P1**4*b2**2*b4*x**5 + 2*P0**4*P1**4*b2**2*b6*x**4 + 2*P0**4*P1**4*b2**2*b8*x**3/3 + P0**4*P1**4*b2**2*x**7 + 3*P0**4*P1**4*b2*b4**2*x**4 + 6*P0**4*P1**4*b2*b4*b6*x**3 + 2*P0**4*P1**4*b2*b4*b8*x**2 - 3*P0**4*P1**4*b2*b4*x**6 + 3*P0**4*P1**4*b2*b6**2*x**2 + 2*P0**4*P1**4*b2*b6*b8*x - 6*P0**4*P1**4*b2*b6*x**5 + P0**4*P1**4*b2*b8**2/3 - 3*P0**4*P1**4*b2*b8*x**4 - 18*P0**4*P1**4*b4**2*x**5 - 45*P0**4*P1**4*b4*b6*x**4 - 18*P0**4*P1**4*b4*b8*x**3 - 18*P0**4*P1**4*b4*x**7 - 27*P0**4*P1**4*b6**2*x**3 - 21*P0**4*P1**4*b6*b8*x**2 - 27*P0**4*P1**4*b6*x**6 - 4*P0**4*P1**4*b8**2*x - 12*P0**4*P1**4*b8*x**5 + 2*P0**4*P1**2*P3*Pm1*b2*x**4 + 4*P0**4*P1**2*P3*Pm1*b4*x**3 + 2*P0**4*P1**2*P3*Pm1*b6*x**2 + 8*P0**4*P1**2*P3*Pm1*x**5 + P0**3*P1**3*P2*Pm1*b2**3*x**4/3 + 4*P0**3*P1**3*P2*Pm1*b2**2*b4*x**3/3 + 2*P0**3*P1**3*P2*Pm1*b2**2*b6*x**2/3 + P0**3*P1**3*P2*Pm1*b2**2*b8*x/3 - 3*P0**3*P1**3*P2*Pm1*b2**2*x**5 + 4*P0**3*P1**3*P2*Pm1*b2*b4**2*x**2/3 + P0**3*P1**3*P2*Pm1*b2*b4*b6*x + P0**3*P1**3*P2*Pm1*b2*b4*b8/3 - 17*P0**3*P1**3*P2*Pm1*b2*b4*x**4 - 7*P0**3*P1**3*P2*Pm1*b2*b6*x**3 - 5*P0**3*P1**3*P2*Pm1*b2*b8*x**2/3 - 47*P0**3*P1**3*P2*Pm1*b2*x**6 - 24*P0**3*P1**3*P2*Pm1*b4**2*x**3 - 22*P0**3*P1**3*P2*Pm1*b4*b6*x**2 - 6*P0**3*P1**3*P2*Pm1*b4*b8*x - 118*P0**3*P1**3*P2*Pm1*b4*x**5 - 3*P0**3*P1**3*P2*Pm1*b6**2*x - P0**3*P1**3*P2*Pm1*b6*b8 - 93*P0**3*P1**3*P2*Pm1*b6*x**4 - 44*P0**3*P1**3*P2*Pm1*b8*x**3 - 108*P0**3*P1**3*P2*Pm1*x**7 - P0**2*P1**5*Pm1*b2**4*x**7/3 - 7*P0**2*P1**5*Pm1*b2**3*b4*x**6/3 - 5*P0**2*P1**5*Pm1*b2**3*b6*x**5/3 - P0**2*P1**5*Pm1*b2**3*b8*x**4/3 + P0**2*P1**5*Pm1*b2**3*x**8/3 - 16*P0**2*P1**5*Pm1*b2**2*b4**2*x**5/3 - 22*P0**2*P1**5*Pm1*b2**2*b4*b6*x**4/3 - 4*P0**2*P1**5*Pm1*b2**2*b4*b8*x**3/3 + 32*P0**2*P1**5*Pm1*b2**2*b4*x**7/3 - 7*P0**2*P1**5*Pm1*b2**2*b6**2*x**3/3 - 2*P0**2*P1**5*Pm1*b2**2*b6*b8*x**2/3 + 22*P0**2*P1**5*Pm1*b2**2*b6*x**6/3 + 4*P0**2*P1**5*Pm1*b2**2*b8*x**5/3 + 92*P0**2*P1**5*Pm1*b2**2*x**9/3 - 4*P0**2*P1**5*Pm1*b2*b4**3*x**4 - 8*P0**2*P1**5*Pm1*b2*b4**2*b6*x**3 - 4*P0**2*P1**5*Pm1*b2*b4**2*b8*x**2/3 + 44*P0**2*P1**5*Pm1*b2*b4**2*x**6 - 5*P0**2*P1**5*Pm1*b2*b4*b6**2*x**2 - 4*P0**2*P1**5*Pm1*b2*b4*b6*b8*x/3 + 60*P0**2*P1**5*Pm1*b2*b4*b6*x**5 + 32*P0**2*P1**5*Pm1*b2*b4*b8*x**4/3 + 176*P0**2*P1**5*Pm1*b2*b4*x**8 - P0**2*P1**5*Pm1*b2*b6**3*x - P0**2*P1**5*Pm1*b2*b6**2*b8/3 + 19*P0**2*P1**5*Pm1*b2*b6**2*x**4 + 16*P0**2*P1**5*Pm1*b2*b6*b8*x**3/3 + 128*P0**2*P1**5*Pm1*b2*b6*x**7 + 80*P0**2*P1**5*Pm1*b2*b8*x**6/3 + 144*P0**2*P1**5*Pm1*b2*x**10 + 48*P0**2*P1**5*Pm1*b4**3*x**5 + 96*P0**2*P1**5*Pm1*b4**2*b6*x**4 + 16*P0**2*P1**5*Pm1*b4**2*b8*x**3 + 240*P0**2*P1**5*Pm1*b4**2*x**7 + 60*P0**2*P1**5*Pm1*b4*b6**2*x**3 + 16*P0**2*P1**5*Pm1*b4*b6*b8*x**2 + 336*P0**2*P1**5*Pm1*b4*b6*x**6 + 64*P0**2*P1**5*Pm1*b4*b8*x**5 + 384*P0**2*P1**5*Pm1*b4*x**9 + 12*P0**2*P1**5*Pm1*b6**3*x**2 + 4*P0**2*P1**5*Pm1*b6**2*b8*x + 108*P0**2*P1**5*Pm1*b6**2*x**5 + 32*P0**2*P1**5*Pm1*b6*b8*x**4 + 288*P0**2*P1**5*Pm1*b6*x**8 + 64*P0**2*P1**5*Pm1*b8*x**7 + 192*P0**2*P1**5*Pm1*x**11 - P0**2*P1**2*P2**2*Pm1**2*b2**2*x**3/3 - P0**2*P1**2*P2**2*Pm1**2*b2*b4*x**2 - P0**2*P1**2*P2**2*Pm1**2*b2*b6*x - P0**2*P1**2*P2**2*Pm1**2*b2*b8/3 + 2*P0**2*P1**2*P2**2*Pm1**2*b2*x**4 + 10*P0**2*P1**2*P2**2*Pm1**2*b4*x**3 + 11*P0**2*P1**2*P2**2*Pm1**2*b6*x**2 + 4*P0**2*P1**2*P2**2*Pm1**2*b8*x + 8*P0**2*P1**2*P2**2*Pm1**2*x**5

OK
```
