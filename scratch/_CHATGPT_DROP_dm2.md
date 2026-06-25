# Q340 (dm2): Discriminants/resultants of short-Weierstrass `preΨ'_n`, `n=3..8`

Curve:

```text
y² = x³ + A x + B
```

For odd `n`, `preΨ'_n = ψ_n`.  For even `n`, `preΨ'_n = ψ_n / ψ₂`, so the leading coefficient is `n/2`, not `n`.

I use the standard short-Weierstrass discriminant

```text
Δstd = -16*(4A³ + 27B²).
```

If instead you use the normalized quantity

```text
Δsmall = -(4A³ + 27B²)/16,
```

then `Δstd = 256 * Δsmall`, so multiply every coefficient below by `256^e = 2^(8e)`.

## Result table

Here `d = deg_X(preΨ'_n)` and `e = d(d-1)/6`.

| n | d | e | leading coeff | computed `Disc_X(preΨ'_n)` | claimed `± n^(d-1) Δstd^e`? | computed `Res(f,f')` | claimed `± n^d Δstd^e`? |
|---:|---:|---:|---:|---|---|---|---|
| 3 | 4 | 2 | 3 | `-3^3 * Δstd^2` | YES | `-3^4 * Δstd^2` | YES |
| 4 | 6 | 5 | 2 | `-2^8 * Δstd^5` | NO: expected abs `4^5 = 2^10` | `2^9 * Δstd^5` | NO: expected abs `4^6 = 2^12` |
| 5 | 12 | 22 | 5 | `5^11 * Δstd^22` | YES | `5^12 * Δstd^22` | YES |
| 6 | 16 | 40 | 3 | `2^16 * 3^12 * Δstd^40` | NO: expected abs `6^15 = 2^15*3^15` | `2^16 * 3^13 * Δstd^40` | NO: expected abs `6^16 = 2^16*3^16` |
| 7 | 24 | 92 | 7 | `-7^23 * Δstd^92` | YES | `-7^24 * Δstd^92` | YES |
| 8 | 30 | 145 | 4 | `-2^82 * Δstd^145` | NO: expected abs `8^29 = 2^87` | `2^84 * Δstd^145` | NO: expected abs `8^30 = 2^90` |

## Conclusion

The claimed pattern

```text
Disc(preΨ'_n) = ± n^(d-1) * Δ^e
Res(preΨ'_n, (preΨ'_n)') = ± n^d * Δ^e
```

is correct for the **odd** reduced division polynomials `n = 3,5,7` using the standard curve discriminant `Δstd`.

It is **not** correct for the even reduced polynomials `preΨ'_n = ψ_n/ψ₂`.  The even cases have different powers of small primes because the reduced even polynomial has leading coefficient `n/2` and different normalization.

## Complete runnable SymPy script

```python
import sympy as sp

X, Y, A, B = sp.symbols('X Y A B')
S = X**3 + A*X + B
FW = Y**2 - S
D0 = 4*A**3 + 27*B**2
Delta_std = -16*D0


def rem_curve(poly):
    """Reduce modulo Y^2 = X^3 + A*X + B."""
    return sp.expand(
        sp.rem(sp.Poly(sp.expand(poly), Y), sp.Poly(FW, Y)).as_expr()
    )


def exact_div(num, den):
    q, r = sp.div(sp.expand(num), sp.expand(den), Y, X, A, B, domain=sp.QQ)
    assert sp.expand(r) == 0, r
    return sp.expand(q)


def compute_psi(N):
    psi = {
        0: sp.Integer(0),
        1: sp.Integer(1),
        2: 2*Y,
        3: 3*X**4 + 6*A*X**2 + 12*B*X - A**2,
    }
    pre4lite = (
        X**6 + 5*A*X**4 + 20*B*X**3 - 5*A**2*X**2
        - 4*A*B*X - 8*B**2 - A**3
    )
    psi[4] = 4*Y*pre4lite

    for n in range(5, N + 1):
        if n % 2:
            m = (n - 1) // 2
            psi[n] = rem_curve(psi[m+2]*psi[m]**3 - psi[m-1]*psi[m+1]**3)
        else:
            m = n // 2
            psi[n] = rem_curve(exact_div(
                psi[m]*(psi[m+2]*psi[m-1]**2 - psi[m-2]*psi[m+1]**2),
                2*Y,
            ))
    return psi


psi = compute_psi(9)

pre = {}
for n in range(3, 9):
    if n % 2:
        pre[n] = psi[n]
    else:
        pre[n] = rem_curve(exact_div(psi[n], 2*Y))

# Coefficients C such that Disc = C * Delta_std^e and Res = C * Delta_std^e.
# These are what the script verifies by exact symbolic equality.
expected_disc_coeff = {
    3: -3**3,
    4: -2**8,
    5: 5**11,
    6: 2**16 * 3**12,
    7: -7**23,
    8: -2**82,
}
expected_res_coeff = {
    3: -3**4,
    4: 2**9,
    5: 5**12,
    6: 2**16 * 3**13,
    7: -7**24,
    8: 2**84,
}

print('| n | d | e | lc | Disc coefficient C in C*Delta_std^e | Disc formula check | naive Disc abs match | Res coefficient C in C*Delta_std^e | Res formula check | naive Res abs match |')
print('|---:|---:|---:|---:|---:|:---:|:---:|---:|:---:|:---:|')

for n in range(3, 9):
    f = pre[n]
    df = sp.diff(f, X)
    P = sp.Poly(f, X)
    d = P.degree()
    e = d*(d-1)//6
    lc = P.LC()

    disc = sp.discriminant(f, X)
    res = sp.resultant(f, df, X)

    Cdisc = expected_disc_coeff[n]
    Cres = expected_res_coeff[n]

    disc_ok = sp.expand(disc - Cdisc * Delta_std**e) == 0
    res_ok = sp.expand(res - Cres * Delta_std**e) == 0

    naive_disc_ok = abs(Cdisc) == n**(d-1)
    naive_res_ok = abs(Cres) == n**d

    print(f'| {n} | {d} | {e} | {lc} | {sp.factorint(abs(Cdisc))} sign={sp.sign(Cdisc)} | {disc_ok} | {naive_disc_ok} | {sp.factorint(abs(Cres))} sign={sp.sign(Cres)} | {res_ok} | {naive_res_ok} |')
```

## Script output

```text
| n | d | e | lc | Disc coefficient C in C*Delta_std^e | Disc formula check | naive Disc abs match | Res coefficient C in C*Delta_std^e | Res formula check | naive Res abs match |
|---:|---:|---:|---:|---:|:---:|:---:|---:|:---:|:---:|
| 3 | 4 | 2 | 3 | {3: 3} sign=-1 | True | True | {3: 4} sign=-1 | True | True |
| 4 | 6 | 5 | 2 | {2: 8} sign=-1 | True | False | {2: 9} sign=1 | True | False |
| 5 | 12 | 22 | 5 | {5: 11} sign=1 | True | True | {5: 12} sign=1 | True | True |
| 6 | 16 | 40 | 3 | {2: 16, 3: 12} sign=1 | True | False | {2: 16, 3: 13} sign=1 | True | False |
| 7 | 24 | 92 | 7 | {7: 23} sign=-1 | True | True | {7: 24} sign=-1 | True | True |
| 8 | 30 | 145 | 4 | {2: 82} sign=-1 | True | False | {2: 84} sign=1 | True | False |
```

## Note on the normalized `Δsmall`

If you insist on

```text
Δsmall = -(4A³+27B²)/16,
```

then

```text
Δstd = 256 * Δsmall.
```

So the displayed coefficient `C` becomes

```text
Csmall = C * 256^e = C * 2^(8e).
```

For example, for `n=7`,

```text
Disc(preΨ'_7) = -7^23 * Δstd^92
              = -2^736 * 7^23 * Δsmall^92.
```

This is why the standard curve discriminant `Δstd = -16(4A³+27B²)` is the cleaner normalization for the table.
