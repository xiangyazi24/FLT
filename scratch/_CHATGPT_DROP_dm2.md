# Q249 (dm2): CAS computation for `preΨ'_7` and `preΨ'_11`, short Weierstrass

Curve:

```text
y^2 = x^3 + A x + B
```

For odd `n`, the reduced division polynomial is the usual odd division polynomial:

```text
preΨ'_n = ψ_n ∈ ℤ[A,B][X].
```

I computed the polynomials `preΨ'_7` and `preΨ'_11`, their derivatives, and the resultant shape.  The exact Bezout cofactor solve is the bottleneck: a plain SymPy exact solve did **not** complete for these larger cases in this environment.  The weighted-homogeneous supports already show that `n=11` is not in the `<5000 terms each` range for the straightforward per-`n` certificate.

## Summary results

Use the unnormalized short discriminant factor

```text
D0 = 4*A^3 + 27*B^2
```

and the usual short Weierstrass discriminant

```text
Δstd = -16*D0.
```

### `n = 7`

```text
degree_X(preΨ'_7) = 24
terms(preΨ'_7)    = 61
terms((preΨ'_7)') = 56
```

Exact symbolic resultant was computed and verified:

```text
Res_X(preΨ'_7, (preΨ'_7)') = -7^24 * Δstd^92
                            = -2^368 * 7^24 * (4*A^3 + 27*B^2)^92
```

So the `Δ` power is:

```text
k = 92
```

Weighted Bezout ansatz:

```text
wt(X)=1, wt(A)=2, wt(B)=3
wt(preΨ'_7)  = 24
wt((preΨ'_7)') = 23
wt(Res_7) = 24*23 = 552
```

A natural weighted certificate has:

```text
wt(U_7)=528, deg_X(U_7) ≤ 22, monomial support size = 1992
wt(V_7)=529, deg_X(V_7) ≤ 23, monomial support size = 2080
```

I did **not** obtain exact `U_7,V_7` in SymPy; the sparse/modular linear solve for the `4164 × 4072` system timed out in this environment.  The support sizes are below 5000, so `n=7` still looks plausible with a better CAS backend such as Singular/F4/F5/modular linear algebra, but I am not reporting exact term counts for `U_7,V_7` because I did not compute the cofactors.

### `n = 11`

```text
degree_X(preΨ'_11) = 60
terms(preΨ'_11)    = 331
terms((preΨ'_11)') = 320
```

Full symbolic resultant was not expanded in this environment.  The expected formula, verified by exact integer specialization checks in the script below, is:

```text
Res_X(preΨ'_11, (preΨ'_11)') = -11^60 * Δstd^590
                             = -2^2360 * 11^60 * (4*A^3 + 27*B^2)^590
```

So the `Δ` power is:

```text
k = 590
```

Weighted Bezout ansatz:

```text
wt(preΨ'_11)    = 60
wt((preΨ'_11)') = 59
wt(Res_11)      = 60*59 = 3540
```

A natural weighted certificate has:

```text
wt(U_11)=3480, deg_X(U_11) ≤ 58, monomial support size = 33960
wt(V_11)=3481, deg_X(V_11) ≤ 59, monomial support size = 34540
```

This is already far beyond the `<5000 terms each` target before solving.  I would treat `n=11` as **not tractable** for the naive per-`n` Bezout certificate approach.

## Feasibility verdict

```text
n=7:  polynomial/resultant tractable; Bezout solve not completed in plain SymPy.
      Natural supports: U≈1992, V≈2080, so probably feasible with stronger CAS.

n=11: polynomial tractable; exact symbolic resultant/cofactor solve not tractable here.
      Natural supports: U≈33960, V≈34540, so not feasible for a Lean certificate of this style.
```

This strongly suggests the per-`n` resultant/Bezout route is fine for `n=3,4,5`, maybe possible for `n=7`, and not a realistic path for `n=11` unless a much more structured certificate is found.

## Complete runnable Python script

The script computes the odd division polynomials, verifies the exact symbolic resultant for `n=7`, performs exact specialization checks for the `n=11` resultant formula, and reports weighted Bezout support sizes.

```python
import math
import sympy as sp

X, Y, A, B = sp.symbols('X Y A B')
S = X**3 + A*X + B
D0 = 4*A**3 + 27*B**2
Delta_std = -16*D0


def rem_y(expr):
    """Reduce modulo Y^2 = X^3 + A*X + B."""
    return sp.expand(
        sp.rem(sp.Poly(sp.expand(expr), Y), sp.Poly(Y**2 - S, Y)).as_expr()
    )


def exact_div(expr, den, vars=(Y, X, A, B)):
    q, r = sp.div(sp.expand(expr), sp.expand(den), *vars, domain=sp.QQ)
    return sp.expand(q), sp.expand(r)


def compute_division_polynomials(N):
    """Compute ψ_n up to N for y^2 = x^3 + A*x + B."""
    psi = {
        0: sp.Integer(0),
        1: sp.Integer(1),
        2: 2*Y,
        3: 3*X**4 + 6*A*X**2 + 12*B*X - A**2,
    }
    pre4 = (
        X**6 + 5*A*X**4 + 20*B*X**3 - 5*A**2*X**2
        - 4*A*B*X - 8*B**2 - A**3
    )
    psi[4] = 4*Y*pre4

    for n in range(5, N + 1):
        if n in psi:
            continue
        if n % 2 == 1:
            m = (n - 1) // 2
            psi[n] = rem_y(psi[m+2]*psi[m]**3 - psi[m-1]*psi[m+1]**3)
        else:
            m = n // 2
            num = psi[m] * (psi[m+2]*psi[m-1]**2 - psi[m-2]*psi[m+1]**2)
            q, r = exact_div(num, 2*Y)
            assert r == 0, (n, r)
            psi[n] = rem_y(q)
    return psi


def monoms_weight(weight, max_x_degree):
    """Monomials X^i A^j B^k of weighted degree weight, wt(X)=1, wt(A)=2, wt(B)=3."""
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


def resultant_formula(n):
    D = (n*n - 1)//2
    k = (n*n - 1)*(n*n - 3)//24
    # For n=7 and n=11 the sign is negative with this normalization.
    return -n**D * Delta_std**k, D, k


psi = compute_division_polynomials(11)

for n in [7, 11]:
    f = psi[n]
    df = sp.diff(f, X)
    D = (n*n - 1)//2
    Wres = D*(D-1)
    k = (n*n - 1)*(n*n - 3)//24
    U_support = monoms_weight(Wres - D, D - 2)
    V_support = monoms_weight(Wres - (D - 1), D - 1)

    print(f'n = {n}')
    print('degree_X(prePsi) =', sp.Poly(f, X).degree())
    print('terms(prePsi) =', len(sp.Poly(f, X, A, B).terms()))
    print('terms(derivative) =', len(sp.Poly(df, X, A, B).terms()))
    print('Delta_power k =', k)
    print('weighted_support_U =', len(U_support))
    print('weighted_support_V =', len(V_support))
    print()

# Exact symbolic resultant for n=7.
f7 = psi[7]
df7 = sp.diff(f7, X)
R7 = sp.resultant(f7, df7, X)
R7_expected, D7, k7 = resultant_formula(7)
print('n=7 exact symbolic resultant check:', sp.expand(R7 - R7_expected) == 0)
print('n=7 resultant factor: -7^24 * Delta_std^92')
print('n=7 unnormalized: -2^368 * 7^24 * (4*A^3 + 27*B^2)^92')
print()

# n=11: exact symbolic resultant is too large for plain SymPy here.
# Verify the expected formula by exact integer specializations.
f11 = psi[11]
df11 = sp.diff(f11, X)
R11_expected, D11, k11 = resultant_formula(11)
for a, b in [(1, 1), (2, 3), (-1, 2), (3, -2)]:
    f_spec = sp.Poly(f11.subs({A: a, B: b}), X, domain=sp.ZZ)
    df_spec = sp.Poly(df11.subs({A: a, B: b}), X, domain=sp.ZZ)
    res_spec = sp.resultant(f_spec, df_spec, X)
    pred_spec = int(R11_expected.subs({A: a, B: b}))
    print(f'n=11 specialization A={a}, B={b}:', res_spec == pred_spec)
print('n=11 expected resultant factor: -11^60 * Delta_std^590')
print('n=11 unnormalized: -2^2360 * 11^60 * (4*A^3 + 27*B^2)^590')
```

## Output from the script

```text
n = 7
degree_X(prePsi) = 24
terms(prePsi) = 61
terms(derivative) = 56
Delta_power k = 92
weighted_support_U = 1992
weighted_support_V = 2080

n = 11
degree_X(prePsi) = 60
terms(prePsi) = 331
terms(derivative) = 320
Delta_power k = 590
weighted_support_U = 33960
weighted_support_V = 34540

n=7 exact symbolic resultant check: True
n=7 resultant factor: -7^24 * Delta_std^92
n=7 unnormalized: -2^368 * 7^24 * (4*A^3 + 27*B^2)^92

n=11 specialization A=1, B=1: True
n=11 specialization A=2, B=3: True
n=11 specialization A=-1, B=2: True
n=11 specialization A=3, B=-2: True
n=11 expected resultant factor: -11^60 * Delta_std^590
n=11 unnormalized: -2^2360 * 11^60 * (4*A^3 + 27*B^2)^590
```

## Note on exact Bezout cofactors

The exact Bezout identities requested are:

```text
U_n * preΨ'_n + V_n * (preΨ'_n)' = R_n.
```

For a homogeneous certificate, the supports above are the natural ones.  The linear systems have sizes:

```text
n=7:  4164 equations, 4072 unknowns
n=11: 69090 equations, 68500 unknowns
```

I attempted the `n=7` solve with plain SymPy / sparse modular linear algebra, but it did not complete in this environment.  For `n=11`, the system size alone is already enough to rule out a small `<5000 terms each` straightforward certificate.

So the honest answer to the feasibility question is:

```text
n=7: maybe feasible with Singular/modular sparse linear algebra; not completed here.
n=11: not feasible for the naive per-n Bezout certificate; expected cofactors are far too large.
```
