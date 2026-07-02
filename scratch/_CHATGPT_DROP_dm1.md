# Q3100 (dm1): Hecke-Rogers cone difference identification for the discriminant-5 form

Date: 2026-07-02

## Executive answer

Let

```text
C(q) := D(q) - A(q)
```

with

```text
A(q) = sum_{k >= 0, r >= 0} (-1)^r q^{Q(k,r)},
D(q) = sum_{k < 0, r < 0} (-1)^r q^{Q(k,r)},
Q(k,r) = 4k^2 + 2k + r^2 + (6k + 1)r.
```

Then the clean identification is:

```text
C(q) = - f_{8,6,2}(-q^6, q^2, q),
```

where `f_{a,b,c}` is Hickerson-Mortenson's Hecke-type double-sum block. Equivalently, after setting `n = 2k`, it is the even-`n` projection of the standard discriminant-5 block

```text
C(q) = -1/2 * ( f_{2,3,2}(-q^2, q^2, q) + f_{2,3,2}(q^2, q^2, q) ).
```

The second formula is the most useful bridge to Hickerson-Mortenson, because `f_{2,3,2}` is exactly the `f_{n,n+p,n}` family with `n = 2`, `p = 1`, hence it falls under their main Appell-Lerch expansion theorem.

So I would not try to identify `D - A` first as an eta quotient. It is a Hecke-type indefinite theta cone sum. It has two complementary descriptions:

```text
1. HM/mock side:     Appell-Lerch sums + finite theta correction.
2. Cone/false side:  a two-variable partial/false theta over a discriminant-5 cone.
```

The norm-`-1` unit and the fixed-point-free involution explain the bilateral cancellation, but they do not by themselves force all Appell-Lerch pieces to cancel. Any such cancellation would be an additional special-value identity that should be checked from the explicit HM expression.

References useful for this normalization:

```text
Hickerson--Mortenson, Hecke-type double sums, Appell-Lerch sums, and mock theta functions (I):
https://arxiv.org/abs/1208.1421

Mortenson, On the tenth-order mock theta functions:
https://arxiv.org/abs/1609.04974

Zwegers, Mock Theta Functions:
https://dspace.library.uu.nl/handle/1874/881
```

## 1. Exact match with the Hickerson-Mortenson block

Use the Hickerson-Mortenson convention

```text
f_{a,b,c}(x,y,q)
  = sum_{sg(r)=sg(s)} sg(r) (-1)^{r+s} x^r y^s
      q^{a*binom(r,2) + b*r*s + c*binom(s,2)},

sg(t) = +1 if t >= 0,
sg(t) = -1 if t < 0.
```

Take `(r,s) = (k,r)` and `(a,b,c) = (8,6,2)`, with `x = -q^6`, `y = q^2`. Then

```text
(-1)^{k+r} (-q^6)^k (q^2)^r
  = (-1)^r q^{6k+2r},
```

and

```text
8*binom(k,2) + 6kr + 2*binom(r,2) + 6k + 2r
  = 4k^2 - 4k + 6kr + r^2 - r + 6k + 2r
  = 4k^2 + 2k + 6kr + r^2 + r
  = Q(k,r).
```

Therefore

```text
f_{8,6,2}(-q^6, q^2, q)
  = A(q) - D(q),
```

and hence

```text
D(q) - A(q) = - f_{8,6,2}(-q^6, q^2, q).
```

This is already a closed identification.

There is also a better HM-theorem normalization. Put `n = 2k`, so

```text
Q(k,r) = n^2 + 3nr + r^2 + n + r,
```

with the congruence condition `n even`. The full, unrestricted `n` version is

```text
f_{2,3,2}(-q^2, q^2, q),
```

because

```text
2*binom(n,2) + 3nr + 2*binom(r,2) + 2n + 2r
  = n^2 + 3nr + r^2 + n + r.
```

Replacing `x = -q^2` by `x = q^2` multiplies each `n`-term by `(-1)^n`. Therefore the even-`n` projection is the average:

```text
A(q) - D(q)
  = 1/2 * ( f_{2,3,2}(-q^2, q^2, q)
          + f_{2,3,2}( q^2, q^2, q) ),
```

so

```text
C(q) = D(q) - A(q)
     = -1/2 * ( f_{2,3,2}(-q^2, q^2, q)
              + f_{2,3,2}( q^2, q^2, q) ).
```

This formula is the one I would use for the book/formalization because it puts the object directly in the `f_{n,n+p,n}` family.

## 2. Does the norm-`-1` unit force Appell-Lerch cancellation?

No, not by itself.

The unit of norm `-1` explains why a reflection/involution exists and why the full bilateral sum cancels. In your coordinates the relevant reflection is

```text
sigma(k,r) = (k, -r - 6k - 1).
```

In the `n = 2k` variable this is

```text
sigma(n,r) = (n, -r - 3n - 1).
```

It preserves `Q` and flips `(-1)^r`, so the bilateral sum over all `r` cancels in pairs. But `D - A` is exactly the wall term left after cutting the lattice into cones. The walls are where mock/false behavior lives. The unit symmetry does not remove the wall; it identifies the two sides of the wall.

In Hickerson-Mortenson language, the generic theorem expresses `f_{n,n+p,n}` as

```text
f_{n,n+p,n}(x,y,q)
  = Appell-Lerch part + finite theta correction.
```

For us this says schematically

```text
D - A
  = -1/2 * [HM_Appell(-q^2,q^2) + HM_Appell(q^2,q^2)]
    -1/2 * [HM_theta(-q^2,q^2)  + HM_theta(q^2,q^2)].
```

The average over `x = +/- q^2` kills the odd-`n` part. It does not formally kill all Appell-Lerch terms. To prove total Appell-Lerch cancellation one would have to simplify those terms using the functional equations for `m(x,q,z)` and verify exact cancellation. I would not assume it from the norm-`-1` unit alone.

A better interpretation is:

```text
Appell-Lerch expression = mock/completion-facing description.
Partial-theta expression = cone/wall-facing description.
```

They are two descriptions of the same Hecke-Rogers cone sum, not evidence that one side must vanish.

## 3. Removing the linear terms

Let

```text
Q0(n,r) = n^2 + 3nr + r^2,
Q(n,r)  = Q0(n,r) + n + r.
```

Then the linear terms are removed by a rational coset shift:

```text
Q(n,r) + 1/5
  = Q0(n + 1/5, r + 1/5).
```

Indeed,

```text
Q0(n+a, r+a) = Q0(n,r) + 5a(n+r) + 5a^2,
```

and `a = 1/5` gives `Q0(n,r) + n + r + 1/5`.

In real-quadratic notation, let

```text
K = Q(sqrt(5)),
phi = (1 + sqrt(5))/2,
phi^2 = (3 + sqrt(5))/2.
```

Since

```text
Norm(n + r*phi^2) = n^2 + 3nr + r^2,
```

we have

```text
Q(n,r) + 1/5
  = Norm(n + r*phi^2 + (1 + phi^2)/5).
```

Equivalently,

```text
Norm((5n + 1) + (5r + 1)*phi^2) = 5*(5Q(n,r) + 1).
```

So the linear terms do not disappear under an integral change of variables. They say that the series lives on the coset

```text
(n,r) + (1/5,1/5)
```

of the discriminant-5 norm lattice. The extra condition `n even` and the character `(-1)^r` are mod-2/ray-class data on top of this mod-5 coset.

The shifted-coordinate form also explains the reflection. With

```text
N = n + 1/5,
R = r + 1/5,
```

the involution becomes

```text
(N,R) -> (N, -R - 3N),
```

which is the root reflection preserving

```text
N^2 + 3NR + R^2.
```

## 4. Candidate closed forms

### 4.1 Exact double partial-theta form

Change variables in the negative cone by

```text
k = -a - 1,
r = -b - 1,
```

with `a,b >= 0`. Then

```text
Q(-a-1,-b-1)
  = 4a^2 + 6ab + b^2 + 12a + 7b + 8,
```

and

```text
(-1)^{-b-1} = -(-1)^b.
```

Therefore

```text
D(q) - A(q)
  = - sum_{a,b >= 0} (-1)^b q^{4a^2 + 6ab + b^2 + 2a + b}
    - sum_{a,b >= 0} (-1)^b q^{4a^2 + 6ab + b^2 + 12a + 7b + 8}.
```

Equivalently, define the one-variable partial theta

```text
P_M(q) = sum_{b >= 0} (-1)^b q^{b^2 + M b}.
```

Then

```text
D(q) - A(q)
  = - sum_{a >= 0} q^{4a^2 + 2a}      P_{6a+1}(q)
    - sum_{a >= 0} q^{4a^2 + 12a + 8} P_{6a+7}(q).
```

This is probably the most useful exact false/partial-theta expression for numerical verification.

### 4.2 Exact HM/Appell-Lerch form

Hickerson-Mortenson's main theorem gives, for generic `x,y`,

```text
f_{2,3,2}(x,y,q)
  = g_{2,3,2}(x,y,q,-1,-1) + Theta_{2,1}(x,y,q) / barJ_{0,10},
```

where `Theta_{2,1}` is their finite theta correction and `barJ_{0,10} = j(-1;q^10)` in the standard notation.

For this special case the Appell-Lerch part can be written as

```text
g_{2,3,2}(x,y,q,-1,-1)
  = sum_{t=0}^{1} (-y)^t j(q^{3t} x; q^2)
      m(-q^{6-5t} * (-y)^2 / (-x)^3, q^10, -1)

    + sum_{t=0}^{1} (-x)^t j(q^{3t} y; q^2)
      m(-q^{6-5t} * (-x)^2 / (-y)^3, q^10, -1).
```

Thus the closed HM candidate is

```text
D(q) - A(q)
  = -1/2 * sum_{delta in {-1,+1}}
      [ g_{2,3,2}(delta*q^2, q^2, q, -1, -1)
        + Theta_{2,1}(delta*q^2, q^2, q) / barJ_{0,10} ].
```

Important implementation detail: the values `x = +/- q^2`, `y = q^2` are not fully generic; some `j(...)` factors vanish and some Appell-Lerch parameters may be singular before cancellation. Use the HM formula as a generic identity and specialize by taking the simplified limit. The direct `f`-sum and the double partial-theta formula above avoid this regularization issue.

## 5. Algebraic-number-theory interpretation

The form

```text
n^2 + 3nr + r^2
```

is the norm form of the order `Z[phi] = Z[phi^2]` in `Q(sqrt(5))`:

```text
Norm(n + r*phi^2) = n^2 + 3nr + r^2.
```

The inhomogeneous form is the same norm on the coset

```text
n + r*phi^2 + (1 + phi^2)/5.
```

The congruences are:

```text
n even,                       from n = 2k,
(5n + 1) coefficient mod 10,  from the 1/5 shift and evenness,
(5r + 1) coefficient mod 5,   from the 1/5 shift,
(-1)^r,                       a mod-2 additive/ray character.
```

The standard techniques I would apply are:

1. **Shintani cone decomposition.**  Work in the two real embeddings of `Q(sqrt(5))` and decompose the positive cone modulo totally positive units. The totally positive unit `phi^2` acts on the coefficient vector by

   ```text
   (n,r) -> (-r, n + 3r).
   ```

   This preserves the pure norm. Because the parity condition `n even` is not stable under one application of this matrix, pass to the subgroup preserving the mod-2 class. Modulo 2 the matrix has order 3, so `phi^6` is the natural first unit to try for a parity-stable Shintani reduction.

2. **Ray-class or narrow-ray-class packaging.**  The shift by `1/5` and the sign `(-1)^r` are congruence data. Encode them as a finite character on a ray class modulo a modulus dividing `10` times the different. This is cleaner than treating the signs as ad hoc coefficients.

3. **Pell/norm equation extraction.**  For fixed exponent, the representation problem reduces to a norm equation in a fixed coset. This gives a finite set of reduced representatives modulo units, then all unreduced representatives by unit action.

4. **Indefinite theta completion.**  The cone sign is a Zwegers-type sign kernel. The completion is obtained by replacing signs with error functions attached to the two boundary rays. The holomorphic part is the `D - A` false/Hecke-Rogers cone sum.

5. **Hecke character comparison.**  After the ray-class packaging, compare the resulting coefficient formula with Hecke theta series for `Q(sqrt(5))`. Because the object is cone-truncated, expect a mock/false or Eichler-integral correction rather than a plain holomorphic Hecke theta series.

## 6. Closed form for the support of `D - A`

For the cone factor alone, a coefficient at exponent `b` can be characterized by a Pell-type equation.

Solve `Q(n,r) = b` as a quadratic in `r`:

```text
r^2 + (3n + 1)r + (n^2 + n - b) = 0.
```

The discriminant condition is

```text
s^2 = 5n^2 + 2n + 1 + 4b,
```

and then

```text
r = (-3n - 1 +/- s) / 2.
```

Since `n` is even, `s` is automatically odd when the equation holds. Equivalently,

```text
(5n + 1)^2 - 5s^2 = -4(5b + 1).
```

Thus the cone coefficient is the signed representation number

```text
c_C(b)
  = sum over n even, r integer, Q(n,r)=b of
      eps(n,r) * (-1)^r,
```

where

```text
eps(n,r) = -1  if n >= 0 and r >= 0,    positive cone A,
eps(n,r) = +1  if n <  0 and r <  0,    negative cone D,
eps(n,r) =  0  otherwise.
```

Equivalently, in norm language:

```text
b is represented by the cone iff there are integers n,r such that

  Norm((5n + 1) + (5r + 1)*phi^2) = 5*(5b + 1),
  n == 0 mod 2,
  (n,r) lies in A or D.
```

The sign of the contribution is `eps(n,r) * (-1)^r`. This is a closed support formula. It is not just a congruence condition; it is a ray-class norm-representability condition plus cone inequalities.

## 7. Closed form for keyWeight exponents

For the full missing kernel, the factorization you verified says

```text
Missing_kernel = Theta_u * Theta_v * C(q).
```

In the `n = 2k` normalization, define

```text
R(u,v,n,r)
  = (5u^2 - 3u + 5v^2 - 7v + n^2 + 3nr + r^2 + n + r) / 2.
```

Then the coefficient at `N` in the `q^18` variable is the signed representation number

```text
KW_even(N)
  = sum_{u,v,n,r in Z}
      (-1)^{u+v+r} eps(n,r)
      [ n even ]
      [ R(u,v,n,r) = N ].
```

Here `[condition]` is `1` if the condition holds and `0` otherwise, and `eps` is the cone sign from the previous section.

Therefore the closed support criterion is:

```text
KW_even(N) != 0
```

where `KW_even(N)` is the ray-class/cone representation number above. If one only wants the existence of sigma-straddling atoms before signed cancellation, replace `KW_even(N) != 0` by the existence of at least one tuple `(u,v,n,r)` satisfying the same equation and cone condition.

In the original exponent normalization of this even-row residual, the exponents are

```text
e = 18N.
```

So, for this exact even-row component, a failure exponent must lie in `18Z`. Since `11763 = 9 * 1307` is not divisible by `18`, either the `e=11763` keyWeight counterexample is using a different exponent normalization, or it belongs to a different parity/coset component rather than this even-row residual alone. The same representability method still applies: change the congruence condition `n even` and the coset shift to the component containing that fiber.

A practical closed-form extraction procedure is:

1. Convert each parity/coset component to a shifted norm equation in `Q(sqrt(5))`.
2. Determine the finite ray-class character encoding the signs.
3. Reduce representatives modulo the parity-preserving totally positive unit subgroup, likely generated first by `phi^6`.
4. For each reduced representative, write the associated Pell orbit.
5. Convolve the resulting cone coefficient formula with the two unary theta factors `Theta_u` and `Theta_v`.

That gives a finite union of norm-representability conditions and Pell recurrences for exactly the exponents where keyWeight can fail.

## 8. Verification code skeleton

The following code is only a coefficient-level oracle. It avoids analytic Appell-Lerch regularization and verifies the exact cone and partial-theta descriptions.

```python
from collections import defaultdict
from math import isqrt
from typing import DefaultDict, Dict, List, Tuple


def q_nr(n: int, r: int) -> int:
    """Inhomogeneous discriminant-5 form after n = 2k."""
    return n * n + 3 * n * r + r * r + n + r


def q_kr(k: int, r: int) -> int:
    """Original k,r form."""
    return 4 * k * k + 2 * k + r * r + (6 * k + 1) * r


def parity_sign(r: int) -> int:
    return -1 if r % 2 else 1


def cone_eps_n(n: int, r: int) -> int:
    """Cone sign for C = D - A in n,r coordinates."""
    if n >= 0 and r >= 0:
        return -1
    if n < 0 and r < 0:
        return 1
    return 0


def cone_coeffs_direct(max_b: int) -> Dict[int, int]:
    """Direct finite-box oracle for coefficients of C(q) up to q^max_b.

    The bound is deliberately conservative for testing. For proof code, replace
    it with a lemma bounding same-sign cone representatives of q_nr(n,r) <= max_b.
    """
    out: DefaultDict[int, int] = defaultdict(int)
    bound = 4 * isqrt(max_b + 1) + 100
    for n in range(-bound, bound + 1):
        if n % 2 != 0:
            continue
        for r in range(-bound, bound + 1):
            eps = cone_eps_n(n, r)
            if eps == 0:
                continue
            b = q_nr(n, r)
            if 0 <= b <= max_b:
                out[b] += eps * parity_sign(r)
    return dict(out)


def cone_coeffs_partial_theta(max_b: int) -> Dict[int, int]:
    """Coefficients from the exact two-variable partial-theta expression."""
    out: DefaultDict[int, int] = defaultdict(int)
    bound = 4 * isqrt(max_b + 1) + 100
    for a in range(0, bound + 1):
        for b in range(0, bound + 1):
            sgn = parity_sign(b)
            e1 = 4 * a * a + 6 * a * b + b * b + 2 * a + b
            e2 = 4 * a * a + 6 * a * b + b * b + 12 * a + 7 * b + 8
            if e1 <= max_b:
                out[e1] -= sgn
            if e2 <= max_b:
                out[e2] -= sgn
    return dict(out)


def pell_representations(b: int, n_bound: int) -> List[Tuple[int, int, int]]:
    """Return triples (n, r, s) satisfying Q(n,r)=b via the Pell discriminant.

    This is a search oracle for the closed condition
        (5n + 1)^2 - 5s^2 = -4(5b + 1).
    """
    reps: List[Tuple[int, int, int]] = []
    for n in range(-n_bound, n_bound + 1):
        if n % 2 != 0:
            continue
        disc = 5 * n * n + 2 * n + 1 + 4 * b
        if disc < 0:
            continue
        s = isqrt(disc)
        if s * s != disc:
            continue
        for ss in (s, -s):
            numerator = -3 * n - 1 + ss
            if numerator % 2 != 0:
                continue
            r = numerator // 2
            if q_nr(n, r) == b and cone_eps_n(n, r) != 0:
                reps.append((n, r, ss))
    return reps


def compare_oracles(max_b: int) -> None:
    direct = cone_coeffs_direct(max_b)
    partial = cone_coeffs_partial_theta(max_b)
    for b in range(max_b + 1):
        if direct.get(b, 0) != partial.get(b, 0):
            raise AssertionError((b, direct.get(b, 0), partial.get(b, 0)))
```

For the full missing kernel, convolve `cone_coeffs_direct` with the coefficient dictionaries for `Theta_u` and `Theta_v`. For a formal proof, the code-level oracle should be replaced by the exact representation-number formula in Sections 6 and 7.

## Answers to the five questions

### Q1. Does the norm-`-1` unit force Appell-Lerch parts to cancel?

No. It explains the fixed-point-free sign-reversing involution and hence the bilateral cancellation. It does not force the HM Appell-Lerch terms of the cone residual to cancel. The residual is precisely the wall/cone term where mock or false behavior is expected.

### Q2. Can `D - A` be identified as a known function, and can the linear terms be removed?

Yes: it is exactly `-f_{8,6,2}(-q^6,q^2,q)`, or equivalently the even-`n` projection of `-f_{2,3,2}` at `(x,y)=(-q^2,q^2)` and `(q^2,q^2)`. The linear terms are removed by the rational shift `(n,r) -> (n+1/5,r+1/5)`, not by an integral substitution.

### Q3. Candidate closed form?

The strongest candidate is exact:

```text
D(q) - A(q)
  = - sum_{a >= 0} q^{4a^2 + 2a}      P_{6a+1}(q)
    - sum_{a >= 0} q^{4a^2 + 12a + 8} P_{6a+7}(q),

P_M(q) = sum_{b >= 0} (-1)^b q^{b^2 + M b}.
```

The HM/Appell-Lerch form is the averaged `f_{2,3,2}` formula above.

### Q4. What algebraic-number-theory techniques apply?

Use the real-quadratic norm form in `Q(sqrt(5))`, package the `1/5` shift and `(-1)^r` as ray-class data modulo a modulus dividing `10`, decompose cones via Shintani domains modulo a parity-preserving unit subgroup, and extract coefficients through Pell/norm equations. The automorphic completion is an indefinite theta completion, not an ordinary positive-definite theta series.

### Q5. Closed form for keyWeight failure exponents?

For the cone factor, support is exactly norm representability:

```text
Norm((5n + 1) + (5r + 1)*phi^2) = 5*(5b + 1),
n even,
(n,r) in the positive or negative cone.
```

For the full missing kernel, convolve this cone representation number with the two unary theta representation numbers. Equivalently, `keyWeight` in this component is the signed count of representations by the inhomogeneous rank-4 form `R(u,v,n,r)` above. Nonzero keyWeight means that signed representation number is nonzero; sigma-straddling existence means the same formula with signs ignored.
