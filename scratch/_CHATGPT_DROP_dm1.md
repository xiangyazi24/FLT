# Q3091 (dm1): Q-series identification for the even-row missing-kernel residual

Date: 2026-07-02

## Executive answer

I do not get a direct identification of the coefficient sequence as a standard OEIS sequence, eta quotient, Rogers-Ramanujan product, or classical scalar theta series.

The best structural identification is more specific and, in my view, more useful for the formalization:

```text
residual = ordinary level-5 unary theta factor
           times ordinary level-5 unary theta factor
           times a discriminant-5 Hecke-type false/indefinite theta cone sum.
```

So the discriminant-5 signal is real, but it points to the Zwegers/Hecke-Rogers indefinite-theta side of Rogers-Ramanujan theory, not to a plain eta quotient.  I would not expect this holomorphic q-series by itself to be an honest holomorphic modular form.  I would expect it to be the holomorphic/false part of a completed indefinite theta series of total weight 2, attached to a rank-4 lattice of signature (3,1).  In the variable x = q^18, the natural scalar levels to test first are around 20 or 40, with a Weil-representation formulation being cleaner than scalarization.  In the original q variable, the V_18 substitution pushes those scalar levels to multiples such as 360 or 720, depending on the half-integral/odd-lattice convention used.

## OEIS search result

I searched the requested exact subsequences and nearby variants as web-indexed OEIS searches:

```text
3, 1, -5, 4, -2, -1, -1, 4, 7
-3, 3, 1, -5, 4, -2
3, 3, 1, 5, 4, 2, 1, 1, 4, 7, 6, 5, 5, 12
```

I did not find a relevant OEIS hit.  This is not a proof that OEIS has no related entry, because OEIS search can miss sequences when signs, offsets, dilation, or normalizations differ.  But it is evidence against a simple direct identification.

The exact query URLs worth keeping for manual follow-up are:

```text
https://oeis.org/search?q=3%2C1%2C-5%2C4%2C-2%2C-1%2C-1%2C4%2C7
https://oeis.org/search?q=-3%2C3%2C1%2C-5%2C4%2C-2
https://oeis.org/search?q=3%2C3%2C1%2C5%2C4%2C2%2C1%2C1%2C4%2C7%2C6%2C5%2C5%2C12
```

## Factorization forced by the separated variables

Let x be the q^18 variable, so the listed sequence is

```text
F(x) = -3 + 3*x + x^2 - 5*x^3 + 4*x^4 - 2*x^5 - x^6 - x^7
       + 4*x^8 + 7*x^9 - 6*x^10 + ... .
```

The exponent N is E/2, where E is the original quadratic expression.  The u and v blocks are positive definite unary theta blocks:

```text
U(x) = sum_{u in Z} (-1)^u x^((5u^2 - 3u)/2),
V(x) = sum_{v in Z} (-1)^v x^((5v^2 - 7v)/2).
```

Using the Jacobi triple-product notation

```text
j(z; Q) = sum_{n in Z} (-1)^n Q^(n(n-1)/2) z^n
        = (z; Q)_infty (Q/z; Q)_infty (Q; Q)_infty,
```

we get

```text
U(x) = j(x; x^5),
V(x) = j(x^(-1); x^5) = -x^(-1) j(x; x^5).
```

Thus, if the u and v variables are genuinely independent full-lattice variables, their product is

```text
U(x) * V(x) = -x^(-1) j(x; x^5)^2.
```

Equivalently,

```text
j(x; x^5) = (x; x^5)_infty (x^4; x^5)_infty (x^5; x^5)_infty.
```

This is exactly the level-5 theta/Rogers-Ramanujan world.  It is related to the Rogers-Ramanujan product

```text
G(x) = 1 / ((x; x^5)_infty (x^4; x^5)_infty),
```

by

```text
j(x; x^5) = (x^5; x^5)_infty / G(x).
```

But this is not a pure eta quotient by itself; it involves the level-5 residue-class product.  That explains why the sequence smells like Rogers-Ramanujan or quintuple-product mathematics without matching one of the simplest positive product series.

## The discriminant-5 cone factor

After the u and v factors are removed, the remaining kernel is the mixed-quadrant sum in k and r.  With the sign convention in the prompt, it is naturally

```text
C(x) =   sum_{k >= 0, r < 0}  (-1)^r x^B(k,r)
       - sum_{k < 0, r >= 0}  (-1)^r x^B(k,r),
```

where

```text
B(k,r) = (4k^2 + 2k + r^2 + (6k + 1)r) / 2.
```

Putting n = 2k gives the quadratic part

```text
n^2 + 3*n*r + r^2,
```

with discriminant 5.  This is the real-quadratic, indefinite-theta datum.  The mixed-sign cone is exactly the kind of sign kernel that produces a Hecke-type indefinite theta series or false theta series.  Its modular completion should use error-function corrections along the two real boundary rays of the cone.

So the conceptual identification is

```text
F(x) = theta_5(x)^2 * false_theta_discriminant_5(x),
```

up to the global x-shift and the exact convention for the second quadrant sign.  More explicitly, under the independent-variable assumption,

```text
F(x) = -x^(-1) j(x; x^5)^2 C(x),
```

again with the warning that any global shift or truncation in the formalization must be matched before using this as a literal coefficient identity.

## Why I would not call it an eta quotient

There are three reasons.

1. The coefficient signs and the cone definition are characteristic of a false/indefinite theta contribution, not of a positive-definite theta or eta product alone.

2. The discriminant-5 binary block is indefinite.  A positive-definite theta series of rank r has weight r/2 and honest modular transformation.  Here the k,r part requires a sign-kernel completion, so the holomorphic q-series alone is generally mock, false, or quantum modular rather than classical modular.

3. The u,v factors are standard theta products, but the k,r factor is not an eta product.  Multiplying by a standard theta product does not remove the need for an indefinite-theta completion unless there is an additional identity, and the listed coefficients do not suggest one of the classical Rogers-Ramanujan products directly.

## Expected modular object: weight and level

Write the N-exponent as

```text
N = 1/2 * X^T A X + 1/2 * b^T X,
X = (u, v, k, r)^T,
```

with

```text
A = [[5, 0, 0, 0],
     [0, 5, 0, 0],
     [0, 0, 4, 3],
     [0, 0, 3, 1]],

b = [-3, -7, 2, 1]^T.
```

The determinant is

```text
det(A) = 25 * det([[4, 3], [3, 1]]) = 25 * (-5) = -125.
```

The signature is

```text
signature(A) = (3, 1),
```

because the u and v directions are positive and the k,r block has determinant -5.  The completion should therefore have total theta weight

```text
rank(A) / 2 = 4 / 2 = 2.
```

The shift obtained by completing the square is

```text
A^(-1) b = (-3/5, -7/5, 1/5, 2/5)^T.
```

The quadratic module therefore has a denominator 5.  The sign (-1)^(u+v+r) adds a denominator-2 additive characteristic.  Thus the natural vector-valued object has denominator lcm(5,2) = 10.  Since the lattice is not even in the most naive integral presentation, scalar congruence-group tests should include the usual odd-lattice factor, so the first practical scalar levels in the x variable are

```text
10, 20, 40
```

with 20 or 40 being the safer initial scalar guesses.  If the series is then viewed as a q-series with x = q^18, a scalar form at level L in x becomes a V_18 pullback at level roughly 18L in q.  Thus the first original-q scalar levels to test are

```text
180, 360, 720.
```

I would regard the vector-valued Weil-representation statement as primary and the scalar level as a downstream consequence of choosing a component and character.

## Recommended computational tests

The most direct test is not an eta-quotient search.  It is:

1. Verify the factorization by separately computing the u,v theta factor and the k,r mixed-cone factor.
2. Divide the known coefficients by the theta factor formally, if possible, to recover the cone coefficient sequence.
3. Compare that cone sequence against discriminant-5 Hecke-type false theta families.
4. Only after that, test scalar modular spaces M_2 or weakly holomorphic M_2^! at the candidate scalar levels.

Here is a Sage skeleton for the scalar holomorphic test.  It is not a proof of non-modularity if it fails, because the expected object is false/mock rather than holomorphic modular, but it quickly rules out the simplest scalar modular explanations.

```python
from sage.all import Gamma0
from sage.all import ModularForms
from sage.all import QQ
from sage.all import matrix
from sage.all import vector

coeffs = [
    -3, 3, 1, -5, 4, -2, -1, -1, 4, 7,
    -6, 5, -5, -12, 2, 3, 4, 2, 9, -4,
    -12, -1, 11, -3, 3, 4, -9, -8, -2, -4,
    6, 17, 5, 7, -2, 0, -11, -8, -14, 3,
    -7,
]


def fit_trivial_character_space(level: int, weight: int = 2):
    prec = len(coeffs)
    space = ModularForms(Gamma0(level), weight)
    basis = [f.q_expansion(prec) for f in space.basis()]
    if not basis:
        return None

    mat = matrix(QQ, [[basis[j][n] for j in range(len(basis))]
                      for n in range(prec)])
    rhs = vector(QQ, coeffs)
    try:
        sol = mat.solve_right(rhs)
    except ValueError:
        return None
    return space, sol


for level in [10, 20, 40, 50, 100, 180, 360, 720]:
    ans = fit_trivial_character_space(level, 2)
    if ans is not None:
        space, sol = ans
        print('possible holomorphic scalar fit at level', level)
        print('dimension =', space.dimension())
        print('coordinates =', list(sol))
```

For the actual expected object, I would implement the theta and cone pieces explicitly.  This code records the formal factorization ingredients.

```python
from collections import defaultdict
from typing import DefaultDict


def u_exp(u: int) -> int:
    return (5 * u * u - 3 * u) // 2


def v_exp(v: int) -> int:
    return (5 * v * v - 7 * v) // 2


def b_exp(k: int, r: int) -> int:
    return (4 * k * k + 2 * k + r * r + (6 * k + 1) * r) // 2


def theta_u_coeffs(nmax: int) -> dict[int, int]:
    out: DefaultDict[int, int] = defaultdict(int)
    bound = 2 * nmax + 10
    for u in range(-bound, bound + 1):
        n = u_exp(u)
        if 0 <= n <= nmax:
            out[n] += -1 if u % 2 else 1
    return dict(out)


def theta_v_coeffs(nmax: int) -> dict[int, int]:
    out: DefaultDict[int, int] = defaultdict(int)
    bound = 2 * nmax + 10
    for v in range(-bound, bound + 1):
        n = v_exp(v)
        if 0 <= n <= nmax:
            out[n] += -1 if v % 2 else 1
    return dict(out)


def cone_weight(k: int, r: int) -> int:
    if k >= 0 and r < 0:
        return -1 if r % 2 else 1
    if k < 0 and r >= 0:
        return 1 if r % 2 else -1
    return 0
```

For the cone alone, coefficient extraction must be done with the same finite-support/convergence convention as the formalization.  The indefinite form is unbounded on naive mixed quadrants, so a blind rectangular cutoff is not a mathematically invariant definition.  The correct implementation should use the exact Hecke-Rogers truncation or wall-pairing already present in the kernel.

## Answers to the four questions

### 1. Known q-series, eta quotient, theta function, or modular form?

Not as a direct classical scalar object from the listed coefficients.  The convincing identification is a product of two level-5 unary theta factors with a discriminant-5 Hecke-type false/indefinite theta cone sum.  This is Rogers-Ramanujan territory, but not the Rogers-Ramanujan product itself.

### 2. OEIS subsequences?

No direct hit from the requested exact subsequence searches.  I would next search the cone factor after dividing out the level-5 theta product, because OEIS is more likely to recognize the primitive one- or two-variable false theta than the already-multiplied residual.

### 3. Partial theta times standard theta or eta product?

Yes, structurally.  Under the independent u,v lattice assumption,

```text
F(x) = -x^(-1) j(x; x^5)^2 C(x),
```

where j(x; x^5) is a standard level-5 theta product and C(x) is the mixed-cone discriminant-5 false theta.  I would say `partial/false theta times standard theta product`, not `eta quotient`.

### 4. What modular form space should it live in?

The completed object should have weight 2 and should be vector-valued for the Weil representation of the signature-(3,1) lattice with Gram matrix A above, characteristic denominator 10, and determinant -125.  If forced into scalar congruence subgroups, test weight 2 at levels 20 and 40 in the x = q^18 variable, and levels 360 and 720 in the original q variable.  But the expected holomorphic series is not an ordinary holomorphic modular form; it is the false/mock part of an indefinite theta object.

## References checked

Useful background references for interpreting the structure:

```text
OEIS:
https://oeis.org/

Jacobi triple product:
https://en.wikipedia.org/wiki/Jacobi_triple_product

Rogers-Ramanujan identities and products:
https://en.wikipedia.org/wiki/Rogers%E2%80%93Ramanujan_identities

Zwegers, Mock Theta Functions, indefinite theta completions:
https://arxiv.org/abs/0807.4834

Moore, Modular Transformations of Ramanujan's Tenth Order Mock Theta Functions:
https://arxiv.org/abs/1207.0909

Mortenson, On the tenth-order mock theta functions:
https://arxiv.org/abs/1609.04974
```
