# Q3096 (dm2): Q-series identification for the even-row missing-kernel residual

Date: 2026-07-02

Let `T = q^18` and `R(T) = sum_N a_N T^N` be the residual series with the coefficients supplied in the prompt.

## Executive answer

I do **not** identify the coefficient list as a known named Rogers--Ramanujan series, Watson quintuple-product specialization, eta quotient, or scalar holomorphic modular form. The natural identification is instead:

```text
level-5 unary Rogers--Ramanujan theta product
    times
rank-2 discriminant-5 Hecke-type false/indefinite theta wall term.
```

So the discriminant-5 clue is meaningful, but it points to the Hecke-type/Appell--Lerch/mock-theta setting rather than to a plain eta quotient. After the standard Zwegers-style completion of the sign kernel, the expected object is a weight-2 real-analytic indefinite theta object. The holomorphic series alone should be treated as a false/mock/partial-theta holomorphic part unless an additional cancellation is proved.

## OEIS search result

I searched exact OEIS-indexed strings and exact quoted web strings for the requested subsequences:

```text
3, 1, -5, 4, -2, -1, -1, 4, 7
-3, 3, 1, -5, 4, -2
3, 3, 1, 5, 4, 2, 1, 1, 4, 7, 6, 5, 5, 12
```

I also searched no-space variants and the first few formal q-expansion strings. I did not find a plausible OEIS A-number or a direct sequence hit. This is a negative search result, not a proof that OEIS has no related entry.

## Unary factors: explicit Rogers--Ramanujan theta products

The exponent in the `T` variable is

```text
N = E/2
  = (5u^2 - 3u)/2
  + (5v^2 - 7v)/2
  + (4k^2 + 2k + r^2 + (6k+1)r)/2.
```

If the `u,v` sums are the unrestricted independent theta sums, then the two unary blocks are explicit level-5 theta products. Let

```text
Theta_U(T) = sum_{u in Z} (-1)^u T^((5u^2 - 3u)/2).
```

Using Ramanujan's general theta function / Jacobi triple product,

```text
Theta_U(T) = f(-T,-T^4)
           = (T;T^5)_infty (T^4;T^5)_infty (T^5;T^5)_infty.
```

This is exactly in Rogers--Ramanujan level 5. Since the first Rogers--Ramanujan product is

```text
G(T) = 1 / ((T;T^5)_infty (T^4;T^5)_infty),
```

one may also write

```text
Theta_U(T) = (T^5;T^5)_infty / G(T).
```

Similarly,

```text
Theta_V(T) = sum_{v in Z} (-1)^v T^((5v^2 - 7v)/2)
           = f(-T^(-1), -T^6)
           = -T^(-1) Theta_U(T),
```

where the last equality follows from the change of variable `v -> 1-v`.

Thus the positive/unary part is

```text
Theta_U(T) Theta_V(T) = -T^(-1) Theta_U(T)^2.
```

This explains the Rogers--Ramanujan flavor, but it does not identify the whole residual as a Rogers--Ramanujan product; the hard part is the binary wall kernel.

## Binary wall kernel

The mixed-sign rule with the extra sign flip is

```text
epsilon(k,r) = (sgn(k + 1/2) - sgn(r + 1/2))/2.
```

This gives `+1` on `k >= 0, r < 0`, `-1` on `k < 0, r >= 0`, and `0` in the same-sign quadrants. The binary factor is therefore schematically

```text
Psi(T) = sum_{k,r in Z} epsilon(k,r) (-1)^r
         T^((4k^2 + 2k + r^2 + (6k+1)r)/2).
```

The quadratic part in `(k,r)` has Gram matrix

```text
[ 4  3 ]
[ 3  1 ]
```

with determinant `-5`. Equivalently, using `n = 2k`, the binary form is

```text
n^2 + 3 n r + r^2,
```

whose discriminant is `5`. In the usual Hecke-type notation this is the discriminant-5 family with parameters essentially `(a,b,c) = (4,3,1)`, since `b^2 - a c = 9 - 4 = 5`, up to the linear specialization and cone convention.

Hickerson--Mortenson type formulas express these Hecke-type double sums in terms of Appell--Lerch sums plus theta functions. That is the correct class for this object.

Consequently, modulo any extra atom-range restrictions not shown in the prompt, the residual has the schematic factorization

```text
R(T) = -T^(-1) Theta_U(T)^2 Psi(T).
```

This is a standard level-5 theta/Rogers--Ramanujan product times a rank-2 discriminant-5 false/indefinite theta. I would not call it a plain eta quotient.

## Is it a partial theta times a standard theta or eta product?

Yes in the broad sense, but not as a one-variable partial theta times a simple eta quotient.

The explicit standard factor is

```text
Theta_U(T)^2
= ((T;T^5)_infty (T^4;T^5)_infty (T^5;T^5)_infty)^2.
```

The remaining factor `Psi(T)` is a binary Hecke-type false/indefinite theta with a wall sign kernel. It should decompose into Appell--Lerch pieces plus theta pieces. Only in special cases do the Appell--Lerch pieces cancel and leave a pure product. The coefficient data and exact searches do not show such a cancellation.

## Expected weight and level

For `N = E/2`, the quadratic part in `x = (u,v,k,r)^t` has Gram matrix

```text
A = [ 5  0  0  0 ]
    [ 0  5  0  0 ]
    [ 0  0  4  3 ]
    [ 0  0  3  1 ].
```

Its signature is `(3,1)` and its determinant is `-125`. The linear terms are absorbed by the shift

```text
h = A^(-1) (-3/2, -7/2, 1, 1/2)^t
  = (-3/10, -7/10, 1/10, 1/5)^t.
```

Then

```text
N = (1/2) (x+h)^t A (x+h) - 31/20.
```

Thus `T^(31/20) R(T)` is naturally a coset component of a rank-4 indefinite theta series. The expected completed weight is therefore

```text
weight = rank/2 = 2.
```

Because the discriminant module has order `125` and the shift has denominator `10`, the natural scalar level in the `T` variable should divide `20`; `40` is a conservative upper bound if one keeps odd-lattice theta multipliers instead of packaging the object vector-valuedly. Since the original variable is `T = q^18`, scalar levels scale by `18`:

```text
first scalar place to look: Gamma_0(360), weight 2;
conservative upper-bound place: Gamma_0(720), weight 2.
```

The invariant statement is cleaner:

```text
weight-2 vector-valued real-analytic indefinite theta for the Weil representation attached to (A,h).
```

If a holomorphic scalar modular form remains after cancellation of the false/mock part, search in a weight-2 space of level `360` or `720`, with the multiplier/quadratic character coming from the discriminant form.

The current 41 coefficients are not enough to certify a scalar level-360 identity by a Sturm test. For `Gamma_0(360)`, the index is

```text
360 * (1 + 1/2) * (1 + 1/3) * (1 + 1/5) = 864,
```

so the weight-2 Sturm bound is

```text
(2/12) * 864 = 144.
```

At level `720`, the analogous conservative bound is `288`. So more coefficients are needed before one can prove or disprove equality to a scalar holomorphic modular form by finite coefficient comparison.

## Bottom line

My best identification is:

```text
a discriminant-5 Hecke--Rogers cone-boundary residual,
namely a level-5 unary theta product times a binary false/indefinite theta,
with expected completed modular weight 2 and natural level 20 in T=q^18
(or level 360 in the original q variable, with 720 as a conservative multiplier-safe bound).
```

I do not find a direct known OEIS sequence, eta quotient, or named Rogers--Ramanujan/quintuple-product q-series for the supplied coefficients.
