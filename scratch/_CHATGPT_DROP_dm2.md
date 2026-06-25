# Q240 (dm2): Bezout separability certificate for `preΨ'_5`, short Weierstrass

Short Weierstrass curve:

```text
y^2 = x^3 + A x + B
```

For odd `n=5`, the reduced division polynomial is the usual `ψ₅`, so

```text
preΨ'_5 = ψ₅ ∈ ℤ[A,B][X].
```

## Results

### `preΨ'_5`

```text
preΨ'_5 = 5*X**12 + 62*A*X**10 + 380*B*X**9 - 105*A**2*X**8 + 240*A*B*X**7 - 300*A**3*X**6 - 240*B**2*X**6 - 696*A**2*B*X**5 - 125*A**4*X**4 - 1920*A*B**2*X**4 - 80*A**3*B*X**3 - 1600*B**3*X**3 - 50*A**5*X**2 - 240*A**2*B**2*X**2 - 100*A**4*B*X - 640*A*B**3*X + A**6 - 32*A**3*B**2 - 256*B**4
```

It has degree `12` in `X`, as expected from `(25-1)/2 = 12`.

### Derivative

```text
(preΨ'_5)' = 60*X**11 + 620*A*X**9 + 3420*B*X**8 - 840*A**2*X**7 + 1680*A*B*X**6 - 1800*A**3*X**5 - 1440*B**2*X**5 - 3480*A**2*B*X**4 - 500*A**4*X**3 - 7680*A*B**2*X**3 - 240*A**3*B*X**2 - 4800*B**3*X**2 - 100*A**5*X - 480*A**2*B**2*X - 100*A**4*B - 640*A*B**3
```

### Resultant

```text
Res_X(preΨ'_5, (preΨ'_5)') = 75557863725914323419136000000000000*(4*A**3 + 27*B**2)**22
```

Factored constant:

```text
75557863725914323419136000000000000 = 2^88 * 5^12
```

For short Weierstrass,

```text
Δ = -16*(4*A**3 + 27*B**2)
```

so, since the exponent is even,

```text
Res_X(preΨ'_5, (preΨ'_5)') = 5^12 * Δ^22.
```

Thus the separability obstruction is exactly `5 * Δ`, as expected: over a field, `preΨ'_5` is separable when `(5 : k) ≠ 0` and `Δ ≠ 0`.

### Bezout cofactors

I computed integer cofactors `U,V ∈ ℤ[A,B][X]` with

```text
U*preΨ'_5 + V*(preΨ'_5)' = Res_X(preΨ'_5, (preΨ'_5)').
```

The computation used a weighted-homogeneous linear ansatz rather than the full Sylvester adjugate, because the Sylvester adjugate over `ℤ[A,B]` is slow in plain SymPy for this `23 × 23` system.

Weights:

```text
wt(X)=1, wt(A)=2, wt(B)=3.
```

Then:

```text
wt(preΨ'_5) = 12
wt((preΨ'_5)') = 11
wt(Res) = 132
```

so one can take:

```text
wt(U)=120, deg_X(U) ≤ 10
wt(V)=121, deg_X(V) ≤ 11.
```

The solved integer certificate has:

```text
terms(U) = 216
terms(V) = 236
```

Both are above the requested `< 200` cutoff, so I am not printing them explicitly here.  The script below computes them and asserts the exact Bezout identity.

## Complete runnable SymPy script

```python
import sympy as sp

X, A, B = sp.symbols('X A B')

# Short-Weierstrass initial division polynomials.
psi3 = 3*X**4 + 6*A*X**2 + 12*B*X - A**2
pre4 = (
    X**6 + 5*A*X**4 + 20*B*X**3 - 5*A**2*X**2
    - 4*A*B*X - 8*B**2 - A**3
)

# ψ5 = ψ4*ψ2^3 - ψ1*ψ3^3.
# For short Weierstrass, ψ2 = 2Y and ψ4 = 4Y*pre4, hence
# ψ4*ψ2^3 = 32*Y^4*pre4 = 32*(X^3 + A*X + B)^2*pre4.
f = sp.expand(32*(X**3 + A*X + B)**2*pre4 - psi3**3)
df = sp.diff(f, X)

Delta = -16*(4*A**3 + 27*B**2)
R = sp.resultant(f, df, X)

print('prePsi5 =', sp.sstr(f))
print()
print('d_prePsi5 =', sp.sstr(df))
print()
print('degree_X(prePsi5) =', sp.Poly(f, X).degree())
print('terms(prePsi5) =', len(sp.Poly(f, X, A, B).terms()))
print()
print('resultant =', sp.sstr(sp.factor(R)))
print('resultant_factorint_constant =', sp.factorint(sp.Poly(R, A, B).content()))
print('resultant_equals_5^12_Delta^22 =', sp.expand(R - 5**12 * Delta**22) == 0)
print()

# Weighted-homogeneous ansatz for Bezout cofactors.
# wt(X)=1, wt(A)=2, wt(B)=3.
# wt(f)=12, wt(df)=11, wt(R)=132, so wt(U)=120 and wt(V)=121.
def monoms_weight(weight, max_x_degree):
    mons = []
    for i in range(max_x_degree + 1):
        rem = weight - i
        if rem < 0:
            continue
        for j in range(rem // 2 + 1):
            rem2 = rem - 2*j
            if rem2 % 3 == 0:
                k = rem2 // 3
                mons.append((i, j, k))
    return mons

monsU = monoms_weight(120, 10)  # deg_X(U) < deg_X(df)=11
monsV = monoms_weight(121, 11)  # deg_X(V) < deg_X(f)=12

u = sp.symbols('u0:' + str(len(monsU)))
v = sp.symbols('v0:' + str(len(monsV)))
unknowns = list(u) + list(v)

U_ansatz = sum(c * X**i * A**j * B**k for c, (i, j, k) in zip(u, monsU))
V_ansatz = sum(c * X**i * A**j * B**k for c, (i, j, k) in zip(v, monsV))

expr = sp.Poly(sp.expand(U_ansatz*f + V_ansatz*df - R), X, A, B)
equations = [coeff for _monom, coeff in expr.terms()]

print('Bezout ansatz unknowns U =', len(monsU))
print('Bezout ansatz unknowns V =', len(monsV))
print('linear equations =', len(equations))

sol_set = sp.linsolve(equations, unknowns)
sol_tuple = next(iter(sol_set))

# This particular system has a unique integer solution.
free_symbols = set().union(*(s.free_symbols for s in sol_tuple)) - set(unknowns)
assert not free_symbols

U = sp.expand(sum(sol_tuple[i] * X**a * A**b * B**c for i, (a, b, c) in enumerate(monsU)))
V = sp.expand(sum(sol_tuple[len(monsU) + i] * X**a * A**b * B**c for i, (a, b, c) in enumerate(monsV)))

PU = sp.Poly(U, X, A, B, domain=sp.QQ)
PV = sp.Poly(V, X, A, B, domain=sp.QQ)
assert all(coeff.q == 1 for _monom, coeff in PU.terms())
assert all(coeff.q == 1 for _monom, coeff in PV.terms())

print('terms(U) =', len(PU.terms()))
print('terms(V) =', len(PV.terms()))
print('deg_X(U) =', sp.Poly(U, X).degree())
print('deg_X(V) =', sp.Poly(V, X).degree())
print('content(U) =', PU.content())
print('content(V) =', PV.content())

assert sp.expand(U*f + V*df - R) == 0
print('Bezout verification = OK')

if len(PU.terms()) < 200:
    print('U =', sp.sstr(U))
else:
    print('U omitted: term count >= 200')

if len(PV.terms()) < 200:
    print('V =', sp.sstr(V))
else:
    print('V omitted: term count >= 200')
```

## Script output

```text
prePsi5 = A**6 - 50*A**5*X**2 - 100*A**4*B*X - 125*A**4*X**4 - 32*A**3*B**2 - 80*A**3*B*X**3 - 300*A**3*X**6 - 240*A**2*B**2*X**2 - 696*A**2*B*X**5 - 105*A**2*X**8 - 640*A*B**3*X - 1920*A*B**2*X**4 + 240*A*B*X**7 + 62*A*X**10 - 256*B**4 - 1600*B**3*X**3 - 240*B**2*X**6 + 380*B*X**9 + 5*X**12

d_prePsi5 = -100*A**5*X - 100*A**4*B - 500*A**4*X**3 - 240*A**3*B*X**2 - 1800*A**3*X**5 - 480*A**2*B**2*X - 3480*A**2*B*X**4 - 840*A**2*X**7 - 640*A*B**3 - 7680*A*B**2*X**3 + 1680*A*B*X**6 + 620*A*X**9 - 4800*B**3*X**2 - 1440*B**2*X**5 + 3420*B*X**8 + 60*X**11

degree_X(prePsi5) = 12
terms(prePsi5) = 19

resultant = 75557863725914323419136000000000000*(4*A**3 + 27*B**2)**22
resultant_factorint_constant = {2: 88, 5: 12}
resultant_equals_5^12_Delta^22 = True

Bezout ansatz unknowns U = 216
Bezout ansatz unknowns V = 236
linear equations = 474
terms(U) = 216
terms(V) = 236
deg_X(U) = 10
deg_X(V) = 11
content(U) = 73786976294838206464000000000000
content(V) = 3689348814741910323200000000000
Bezout verification = OK
U omitted: term count >= 200
V omitted: term count >= 200
```
