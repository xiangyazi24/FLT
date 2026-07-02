# Q3111 (dm1): Q(sqrt(5)) ADH-type identity from Chan's Theta_10

Date: 2026-07-02

## Executive answer

This looks genuinely interesting.  I would formulate the discovery as follows.

Let

```text
K = Q(sqrt(5)),
phi = (1 + sqrt(5)) / 2,
N(a + b*phi) = a^2 + a*b - b^2.
```

For the cone exponent

```text
E(k,r) = (4*k^2 + 2*k + r^2 + (6*k + 1)*r) / 2
       = 2*k^2 + k + 3*k*r + r*(r + 1)/2,
```

define

```text
beta(k,r) = (r - 2*k) + (4*k + 3*r + 1)*phi.
```

Then the key identity is the exact norm identity

```text
-N_{K/Q}(beta(k,r)) = 10*E(k,r) + 1.
```

Therefore every nonzero coefficient of the cone series is supported on integers `10*n + 1` represented by the norm form of `Z[phi]`.  Since the rational primes inert in `Q(sqrt(5))` are exactly

```text
p == 2 or 3 mod 5,
```

the necessary norm criterion is exactly:

```text
every prime p == 2 or 3 mod 5 divides 10*n + 1 to even order.
```

Because `Q(sqrt(5))` has class number one and has a unit of norm `-1`, this inert-prime parity condition is also the usual global norm criterion for positive rational integers prime to 5.  The important point is that the coefficient can still vanish by signed cone cancellation even when the norm condition holds.

I did not find an obvious web-indexed prior occurrence of this precise `10n + 1` / golden-field q-series.  The closest literature I found treats the ADH `Q(sqrt(6))` case and later real-quadratic q-hypergeometric families for `Q(sqrt(2))`, `Q(sqrt(3))`, and `Q(sqrt(6))`, but not this exact `Q(sqrt(5))` / `10n+1` cone series.  That is not a proof of novelty; MathSciNet/Zentralblatt and direct full-text checking of Andrews, Hickerson, Mortenson, Lovejoy, Osburn, Bringmann, Kane, Chern, Patkowski, and collaborators would still be needed.  But the first-pass signal is positive.

My strongest recommendation is to treat this as a new **ADH-type false-indefinite theta component** attached to the golden field, with Chan's tenth-order theta identity providing the source identity.

## 0. Sign convention warning

There is one sign convention to lock down before writing the theorem.

Hickerson-Mortenson use

```text
f_{a,b,c}(x,y,q)
  = sum_{sg(r)=sg(s)} sg(r) * (-1)^(r+s) * x^r * y^s
      * q^(a*binom(r,2) + b*r*s + c*binom(s,2)),
```

where `sg(t)=+1` for `t >= 0` and `sg(t)=-1` for `t < 0`.

With that standard convention,

```text
F(X) := f_{1,3,4}(X, -X^3, X)
```

has term

```text
sg(r) * (-1)^r * X^(r*(r+1)/2 + 3*r*s + 2*s^2 + s).
```

After the identification `s = k`, this is the positive cone minus the negative cone:

```text
F(X) = A(X) - D(X).
```

Thus, if your `B` is defined as

```text
B(X) = D(X) - A(X),
```

then under the standard HM convention the precise statement is

```text
B(X) = -f_{1,3,4}(X, -X^3, X).
```

If your local convention for `f` has the opposite cone sign, then your displayed statement `B=f_{1,3,4}` is exactly correct.  The norm-support theorem is unaffected by this global sign.

In what follows I write `B = D - A`, matching the missing-kernel factorization in the prompt:

```text
Missing_kernel = -q^(-1) * j(q;q^5)^2 * B(q^2).
```

## 1. Has the Q(sqrt(5)) ADH case been done before?

I found no obvious prior exact match for this `10n+1` golden-field series.

Searches that produced no relevant direct hit included variants of:

```text
"10n+1" norm "golden ratio" q-series
"10n+1" "Q(sqrt(5))" "q-series"
"10n+1" "mock theta" "norm" "sqrt(5)"
"10n+1" "Andrews" "Hickerson" "Mortenson"
"10n+1" "Z[phi]"
"10n+1" "real quadratic" "q-hypergeometric"
"f_{1,3,4}" "Hickerson" "Mortenson"
```

The nearest established literature I found is:

```text
Andrews--Dyson--Hickerson, Partitions and indefinite quadratic forms, Invent. Math. 91 (1988).
```

This is the original `sigma(q)` / `Q(sqrt(6))` source.

```text
Sander Zwegers, Maass waveforms arising from sigma and related indefinite theta functions.
https://arxiv.org/abs/1002.1175
```

This places the ADH sigma story into the mock Maass / false-indefinite theta framework.

```text
Hickerson--Mortenson, Hecke-type double sums, Appell-Lerch sums, and mock theta functions (I).
https://arxiv.org/abs/1208.1421
```

This gives the Appell-Lerch and theta-correction technology for Hecke-type double sums.

```text
Bringmann--Kane, Multiplicative q-hypergeometric series arising from real quadratic fields.
https://arxiv.org/abs/0812.4397
```

This explicitly describes ADH-type q-series related to `Q(sqrt(2))` and `Q(sqrt(3))`, with partition interpretations.

```text
Lovejoy--Osburn, Real quadratic double sums.
https://arxiv.org/abs/1502.01109
```

This gives a dozen double sums for ideals in real quadratic fields, specifically including `Q(sqrt(2))`, `Q(sqrt(3))`, and `Q(sqrt(6))` in the main theorems.  I did not see a `Q(sqrt(5))` theorem there.

```text
Folsom--Males--Rolen--Storzer, Oscillating asymptotics for a Nahm-type sum and conjectures of Andrews.
https://arxiv.org/abs/2305.16654
```

This gives modern context for ADH-type phenomena, including the original relation of `sigma(q)` to `Q(sqrt(6))` and related partition-rank asymptotics.

```text
Bringmann--Craig--Nazaroglu, Precision Asymptotics for Partitions Featuring False-Indefinite Theta Functions.
https://arxiv.org/abs/2409.17818
```

This is useful context for current interest in false-indefinite theta functions and partition asymptotics.

My current assessment is:

```text
No direct prior Q(sqrt(5)), 10n+1, f_{1,3,4}(X,-X^3,X) ADH sibling was found in a first-pass search.
```

That should be phrased cautiously in a paper as:

```text
"We are not aware of this example in the literature."
```

not as an absolute novelty claim until a deeper bibliography search is complete.

## 2. Publication value

I think this is potentially publishable if the final write-up contains more than a numerical observation.

A publishable package would have the following theorem stack.

### Theorem A: Chan-kernel factorization

Prove, from the Chan `Theta_10` formalism, that the even-row missing residual factors as

```text
Missing_kernel = -q^(-1) * j(q;q^5)^2 * B(q^2),
```

where `B` is the cone difference.

### Theorem B: Hecke-Rogers / HM identification

With standard HM signs,

```text
B(X) = -f_{1,3,4}(X, -X^3, X).
```

Equivalently, without relying on HM notation,

```text
B(X)
  = - sum_{a,b >= 0} (-1)^b X^(2*a^2 + a + 3*a*b + b*(b+1)/2)
    - sum_{a,b >= 0} (-1)^b X^(2*a^2 + 6*a + 3*a*b + (b^2 + 7*b)/2 + 4).
```

This is an exact two-variable false/partial theta expression.

### Theorem C: golden-field norm support

For `B(X)=sum B_N X^N`,

```text
B_N != 0  ==>  10*N + 1 is a norm from Z[phi].
```

Equivalently, every inert prime `p == 2,3 mod 5` occurs in `10*N+1` with even exponent.

The proof is the explicit identity

```text
-N((r - 2*k) + (4*k + 3*r + 1)*phi)
  = 10*(2*k^2 + k + 3*k*r + r*(r+1)/2) + 1.
```

### Theorem D: signed ray-class formula

Strengthen Theorem C to a signed representation formula:

```text
B_N = sum epsilon(alpha)
```

over elements or principal ideals in a specified ray class of `Z[phi]` with norm `10*N+1`, reduced to a Shintani cone, with sign determined by the cone side and `(-1)^r`.

This theorem would explain the 91 cancellation zeros.

### Theorem E: HM/Appell-Lerch expression and completion

Give the Appell-Lerch plus theta correction expression, and explain the modular completion as a signature `(1,1)` indefinite theta object.  This places the example in the modern ADH/Zwegers/Hickerson-Mortenson framework.

### Publication target

If the note is short and focused, good venues would include:

```text
The Ramanujan Journal
Research in Number Theory
Journal of Number Theory
Hardy-Ramanujan Journal
Integers
Journal of Integer Sequences, if the coefficient/norm formula and sequence angle are emphasized
```

If the paper also includes a partition interpretation or a systematic search method, it becomes stronger and more suitable for `The Ramanujan Journal`, `Research in Number Theory`, or `Journal of Number Theory`.

The new contribution should be framed as:

```text
A golden-field ADH-type component arising naturally from the tenth-order mock theta / Chan Theta_10 setting.
```

That is a better pitch than just “a new q-series sequence”.

## 3. Explicit identification of B

### 3.1 Exact Hecke-type double-sum identification

Let `X` be the variable of `B`.  With standard HM signs,

```text
B(X) = -f_{1,3,4}(X, -X^3, X).
```

Proof: HM's summand is

```text
sg(r) * (-1)^(r+s) * X^r * (-X^3)^s
  * X^(binom(r,2) + 3*r*s + 4*binom(s,2)).
```

The sign is

```text
(-1)^(r+s) * (-1)^s = (-1)^r,
```

and the exponent is

```text
r + 3*s + binom(r,2) + 3*r*s + 4*binom(s,2)
= r*(r+1)/2 + 3*r*s + 2*s^2 + s.
```

Putting `s=k`, this is

```text
2*k^2 + k + 3*k*r + r*(r+1)/2
= Q(k,r)/2.
```

The positive same-sign cone contributes `A`; the negative same-sign cone contributes `-D` because of the factor `sg(r)`.  Therefore standard HM gives `f=A-D`, hence `B=D-A=-f`.

### 3.2 Exact false-theta form

The positive cone is already

```text
A(X) = sum_{a,b >= 0} (-1)^b
       X^(2*a^2 + a + 3*a*b + b*(b+1)/2).
```

For the negative cone set

```text
k = -a - 1,
r = -b - 1,
```

with `a,b >= 0`.  Then

```text
Q(-a-1,-b-1)/2
  = 2*a^2 + 6*a + 3*a*b + (b^2 + 7*b)/2 + 4,
```

and

```text
(-1)^(-b-1) = -(-1)^b.
```

Thus

```text
B(X) = D(X) - A(X)
     = - sum_{a,b >= 0} (-1)^b X^(2*a^2 + a + 3*a*b + b*(b+1)/2)
       - sum_{a,b >= 0} (-1)^b X^(2*a^2 + 6*a + 3*a*b + (b^2 + 7*b)/2 + 4).
```

This is currently the cleanest closed form for direct verification.

Define the one-variable partial theta

```text
P_M(X) = sum_{b >= 0} (-1)^b X^(b*(b+1)/2 + M*b).
```

Then

```text
B(X)
  = - sum_{a >= 0} X^(2*a^2 + a)       P_{3a}(X)
    - sum_{a >= 0} X^(2*a^2 + 6*a + 4) P_{3a+3}(X),
```

where the second formula uses

```text
(b^2 + 7*b)/2 + 3ab = b*(b+1)/2 + (3a+3)b.
```

This is a very compact false-theta candidate.

### 3.3 Appell-Lerch part from HM notation

Let

```text
F(X) = f_{1,3,4}(X, -X^3, X).
```

For generic `x,y,q`, HM's Appell part `g_{a,b,c}` gives

```text
f_{a,b,c}(x,y,q) = g_{a,b,c}(x,y,q,z1,z0) + finite theta correction,
```

with the exact correction depending on the theorem/specialization used.  Specializing the generic Appell part to

```text
a = 1,
b = 3,
c = 4,
x = X,
y = -X^3,
q = X,
z0 = z1 = -1,
```

gives

```text
G(X)
  = j(X;X) * m(X^2, X^5, -1)
    + sum_{t=0}^{3} (-X)^t * X^(t*(t-1)/2)
        * j(-X^(3*t+3); X^4)
        * m(-X^(9-5*t), X^20, -1).
```

Since

```text
j(X;X) = 0,
```

the first term vanishes at this specialization, so the Appell part simplifies to

```text
G(X)
  = j(-X^3; X^4)  * m(-X^9,  X^20, -1)
    - X*j(-X^6; X^4) * m(-X^4,  X^20, -1)
    + X^3*j(-X^9; X^4) * m(-X^(-1), X^20, -1)
    - X^6*j(-X^12;X^4) * m(-X^(-6), X^20, -1).
```

Thus, in a compact HM-style form,

```text
F(X) = G(X) + T_{1,3,4}(X),
B(X) = -G(X) - T_{1,3,4}(X),
```

where `T_{1,3,4}` is the finite theta correction produced by HM after taking the non-generic specialization.  I would be careful here: the specialization `x=X`, `q=X` hits theta zeros, so the cleanest rigorous route is either:

```text
1. keep x,y generic, apply HM, simplify, and then take the specialization as a limit; or
2. use the exact false-theta expression above as the primary closed form, and cite HM for the Appell-Lerch/completion interpretation.
```

For numerical verification, the false-theta expression is safer than the Appell-Lerch expression because it avoids regularization of special Appell-Lerch parameters.

### 3.4 Alternative symmetric HM route

There is also an equivalent route through the symmetric discriminant-5 family

```text
f_{2,3,2},
```

which lies directly in the HM family `f_{n,n+p,n}` with `n=2`, `p=1`.  In the original unsquared variable `q`, the cone factor from the previous normalization can be written as an even-projection:

```text
D(q) - A(q)
  = -1/2 * ( f_{2,3,2}(-q^2, q^2, q)
           + f_{2,3,2}( q^2, q^2, q) ).
```

This form is often better for invoking the published HM theorem directly.  The `f_{1,3,4}` form is better for the integral-power `X=q^2` variable and for the `10N+1` norm statement.

## 4. Why the norm theorem is exactly the ADH-type statement

The atom-level identity is very simple and should be highlighted in the paper.

Let

```text
E(k,r) = 2*k^2 + k + 3*k*r + r*(r+1)/2.
```

Set

```text
beta(k,r) = (r - 2*k) + (4*k + 3*r + 1)*phi.
```

Since

```text
N(a + b*phi) = a^2 + a*b - b^2,
```

one computes

```text
N(beta(k,r))
  = (r - 2*k)^2
    + (r - 2*k)*(4*k + 3*r + 1)
    - (4*k + 3*r + 1)^2
  = -10*E(k,r) - 1.
```

Therefore

```text
10*E(k,r) + 1 = -N(beta(k,r)).
```

Because `phi` has norm `-1`, sign is immaterial for rational integer norm representability:

```text
10*E(k,r) + 1 = N(-phi * beta(k,r)).
```

So every represented cone exponent gives an actual norm from `Z[phi]`.

The converse, however, is not coefficient nonvanishing.  It is only support eligibility.  The coefficient is a signed count of cone representatives in a ray class.  Eligible norms can cancel.

## 5. The 91 cancellation zeros

The cancellation zeros should be characterized as signed ray-class cancellations, not as failures of norm representability.

Let

```text
M = 10*N + 1.
```

A representation by the cone gives an element

```text
beta = (r - 2*k) + (4*k + 3*r + 1)*phi
```

with

```text
N(beta) = -M.
```

The congruence and sign data are encoded by the inverse map

```text
b_phi = 4*k + 3*r + 1,
a_phi = r - 2*k.
```

Solving for `k,r`,

```text
r = (4*a_phi + 2*b_phi - 2) / 10,
k = (b_phi - 3*a_phi - 1) / 10.
```

Therefore the relevant ray/coset condition is

```text
4*a_phi + 2*b_phi - 2 == 0 mod 10,
b_phi - 3*a_phi - 1 == 0 mod 10.
```

Equivalently,

```text
a_phi + 2*b_phi == 1 mod 5,
b_phi - 3*a_phi == 1 mod 10.
```

Together with the cone condition

```text
k,r >= 0      for A,
k,r < 0       for D,
```

and the sign

```text
(-1)^r,
```

this gives a ray-class signed representation formula for `B_N`.

So the cancellation zeros are exactly those eligible norms `M=10N+1` for which the signed sum over representatives in this coset and Shintani cone is zero.

For example, the first listed zeros are all norm-eligible:

```text
N = 45:  10N+1 = 451  = 11 * 41
N = 84:  10N+1 = 841  = 29^2
N = 112: 10N+1 = 1121 = 19 * 59
N = 127: 10N+1 = 1271 = 31 * 41
N = 133: 10N+1 = 1331 = 11^3
```

All these primes split in `Q(sqrt(5))`, since they are `1` or `4` modulo `5`.  Thus they pass the inert-prime test.  Their vanishing is caused by cancellation among split-prime choices and unit translates.

A useful exact characterization should look like this:

```text
B_N = sum_{alpha in R(M)} chi_cone(alpha),
```

where:

```text
M = 10N+1,
R(M) = a finite set of reduced generators alpha = a + b*phi
       of principal ideals with |N(alpha)| = M,
       satisfying the two congruences above,
       chosen in a Shintani fundamental cone modulo a parity-preserving unit subgroup,
chi_cone(alpha) = +(-1)^r or -(-1)^r according to whether alpha comes from D or A.
```

Then

```text
B_N = 0
```

if and only if this signed ray-class sum vanishes.

Because `Z[phi]` has class number one, `R(M)` can be described multiplicatively: each split prime factor of `M` gives a choice of one of two conjugate prime ideals, inert primes contribute only through even powers, and units move representatives between cones.  The remaining work is to compute the induced finite character on the ray classes modulo `10` plus the real-place cone condition.

This is the right way to turn the 91 cancellations into a theorem.

## 6. General systematic method

Yes, this suggests a systematic ADH-component search method.

### Step 1: Find Hecke-Rogers cone terms

Decompose a q-series identity into pieces of the form

```text
sum_{same-sign cone} epsilon(r,s) q^{quadratic(r,s) + linear(r,s)}.
```

Use involutions to remove bilateral parts and isolate wall/cone residuals.

### Step 2: Normalize to HM blocks

Match each cone residual to

```text
f_{a,b,c}(x,y,q)
```

or to a projection of such an `f`.  Record

```text
Delta = b^2 - a*c.
```

The real quadratic field should be

```text
Q(sqrt(Delta))
```

up to square factors.

### Step 3: Complete the square over the real quadratic field

For each inhomogeneous binary form, find a coset of the norm lattice.  In this example the atom-level identity is better than completing the square:

```text
10*E(k,r)+1 = -N((r-2k) + (4k+3r+1)*phi).
```

In general, solve for constants `M,A,B` and a linear map `(r,s)->(u,v)` such that

```text
M*E(r,s) + A = ± N(u(r,s) + v(r,s)*omega).
```

### Step 4: Derive the inert-prime support test

For `Q(sqrt(D))`, primes with Kronecker symbol

```text
(D / p) = -1
```

must occur to even order in represented rational norms.  This gives a quick necessary support test.

### Step 5: Upgrade support to coefficients

Support is not enough.  Coefficients require:

```text
ray congruence + Shintani cone + sign character.
```

This gives the signed finite formula and explains cancellation zeros.

### Step 6: Search for Eulerian or partition forms

Use Bailey pairs, Bailey-chain transformations, or constant-term methods to convert the Hecke-type form into a q-hypergeometric series.  Then interpret the q-hypergeometric denominator as partitions and the numerator/sign as a rank or parity statistic.

This is exactly the ADH pattern.

## 7. Partition combinatorics

I would not yet claim a partition interpretation for `B` itself.  The safest statement is:

```text
B is a signed Hecke-Rogers / false-indefinite theta series.
```

However, the full residual

```text
-q^(-1) * j(q;q^5)^2 * B(q^2)
```

has much better combinatorial prospects because

```text
j(q;q^5) = (q;q^5)_infty (q^4;q^5)_infty (q^5;q^5)_infty.
```

Thus `j(q;q^5)^2` is a signed generating function for two colored collections of distinct parts in residue classes `1,4,0 mod 5`, with signs coming from the number of selected parts.  Multiplying by `B(q^2)` imposes the discriminant-5 cone statistic.

This suggests a partition-rank interpretation of the form:

```text
coefficient = # objects with even rank - # objects with odd rank,
```

where the objects are likely colored partitions with mod-5 restrictions and a cone/rank statistic inherited from `(k,r)`.

The ADH sigma function is also a signed rank difference, not a positive partition-count function.  So a signed interpretation is exactly the right target.

A concrete route is:

1. Start from the exact cone expression for `B`.
2. Multiply by `j(q;q^5)^2` and expand the two Jacobi triple products.
3. Try to collapse one or two sums with Bailey's lemma or a constant-term identity.
4. Extract a q-hypergeometric denominator.
5. Interpret the denominator as partitions and the numerator as a rank/parity involution.

Until that is done, the honest conclusion is:

```text
A partition interpretation is plausible and ADH-consistent, but not yet identified.
```

## 8. Code skeletons for verification

### 8.1 Coefficient and norm verifier

```python
from collections import defaultdict
from math import isqrt
from typing import DefaultDict, Dict, List, Tuple


def exponent_E(k: int, r: int) -> int:
    """Exponent E = Q(k,r)/2 in the B(X) variable."""
    numerator = 4 * k * k + 2 * k + r * r + (6 * k + 1) * r
    if numerator % 2 != 0:
        raise ValueError((k, r, numerator))
    return numerator // 2


def norm_phi(a: int, b: int) -> int:
    """Norm of a + b*phi, phi=(1+sqrt(5))/2."""
    return a * a + a * b - b * b


def beta_coeffs(k: int, r: int) -> Tuple[int, int]:
    """Return (a,b) such that beta = a + b*phi."""
    return r - 2 * k, 4 * k + 3 * r + 1


def check_norm_identity(k: int, r: int) -> bool:
    e = exponent_E(k, r)
    a, b = beta_coeffs(k, r)
    return -norm_phi(a, b) == 10 * e + 1


def cone_sign_for_B(k: int, r: int) -> int:
    """Sign for B = D - A.

    A: k>=0,r>=0 contributes -(-1)^r.
    D: k<0,r<0 contributes +(-1)^r.
    Mixed quadrants contribute 0.
    """
    parity = -1 if r % 2 else 1
    if k >= 0 and r >= 0:
        return -parity
    if k < 0 and r < 0:
        return parity
    return 0


def coefficients_B(nmax: int) -> Dict[int, int]:
    """Finite search oracle for coefficients of B(X) through X^nmax."""
    out: DefaultDict[int, int] = defaultdict(int)
    bound = 4 * isqrt(2 * nmax + 1) + 20
    for k in range(-bound, bound + 1):
        for r in range(-bound, bound + 1):
            sgn = cone_sign_for_B(k, r)
            if sgn == 0:
                continue
            e = exponent_E(k, r)
            if 0 <= e <= nmax:
                out[e] += sgn
                assert check_norm_identity(k, r)
    return dict(out)


def inert_prime_condition(m: int) -> bool:
    """Return True iff every p == 2,3 mod 5 occurs to even order.

    This is a simple trial-division implementation for verification.
    """
    if m <= 0:
        return False
    n = m
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            if p % 5 in (2, 3) and e % 2 != 0:
                return False
        p += 1 if p == 2 else 2
    if n > 1 and n % 5 in (2, 3):
        return False
    return True


def verify_support(nmax: int) -> List[Tuple[int, int]]:
    """Return counterexamples to B_N != 0 => inert-prime norm condition."""
    coeffs = coefficients_B(nmax)
    bad: List[Tuple[int, int]] = []
    for n, c in coeffs.items():
        if c != 0 and not inert_prime_condition(10 * n + 1):
            bad.append((n, c))
    return bad
```

### 8.2 Ray-class reconstruction in Sage

This is a computational outline, not polished production code.  The goal is to identify the finite ray classes and signs responsible for the cancellation zeros.

```python
from sage.all import QuadraticField
from sage.all import ZZ
from sage.all import factor


def golden_field_data():
    K = QuadraticField(5, 's')
    s = K.gen()
    phi = (1 + s) / 2
    OK = K.ring_of_integers()
    return K, OK, phi


def beta_element(k: int, r: int):
    K, OK, phi = golden_field_data()
    return OK((r - 2 * k) + (4 * k + 3 * r + 1) * phi)


def exponent_E(k: int, r: int) -> int:
    return (4 * k * k + 2 * k + r * r + (6 * k + 1) * r) // 2


def norm_identity_sage(k: int, r: int) -> bool:
    beta = beta_element(k, r)
    return -ZZ(beta.norm()) == 10 * exponent_E(k, r) + 1


def inverse_kr_from_phi_coeffs(a: int, b: int):
    """Given beta=a+b*phi, recover k,r if beta is in the target coset."""
    num_r = 4 * a + 2 * b - 2
    num_k = b - 3 * a - 1
    if num_r % 10 != 0 or num_k % 10 != 0:
        return None
    r = num_r // 10
    k = num_k // 10
    return k, r


def cone_sign_for_B(k: int, r: int) -> int:
    parity = -1 if r % 2 else 1
    if k >= 0 and r >= 0:
        return -parity
    if k < 0 and r < 0:
        return parity
    return 0


def eligible_by_factorization(N: int) -> bool:
    """Norm eligibility for M=10*N+1."""
    M = ZZ(10 * N + 1)
    for p, e in factor(M):
        if int(p % 5) in (2, 3) and e % 2:
            return False
    return True
```

The next step is to enumerate generators of ideals of norm `10N+1`, reduce by a unit subgroup preserving the congruence class, and compare the signed sum from `inverse_kr_from_phi_coeffs` with the coefficient of `B`.

## 9. Suggested theorem statement

Here is a concise theorem statement that I think is close to paper-ready.

```text
Theorem.
Let phi=(1+sqrt(5))/2 and define

  B(X) = D(X)-A(X),

where

  A(X)=sum_{k,r>=0} (-1)^r X^((4k^2+2k+r^2+(6k+1)r)/2),
  D(X)=sum_{k,r<0}  (-1)^r X^((4k^2+2k+r^2+(6k+1)r)/2).

Then, with the standard Hickerson-Mortenson convention,

  B(X) = -f_{1,3,4}(X,-X^3,X).

Moreover, if B(X)=sum_{N>=0} B_N X^N and B_N != 0, then

  10N+1 = N_{Q(sqrt(5))/Q}(alpha)

for some alpha in Z[phi].  Equivalently, every rational prime p congruent to 2 or 3
modulo 5 divides 10N+1 to even order.
```

The proof of the norm assertion is the explicit atom identity

```text
10N+1 = -N((r-2k)+(4k+3r+1)phi)
```

for every atom contributing to `X^N`.

A stronger second theorem should identify `B_N` itself as the signed ray-class representation number described above.

## 10. Answers to the six questions

### Q1. Has the Q(sqrt(5)) ADH case been done before?

I found no direct prior occurrence of this exact `10n+1` golden-field series in first-pass searches.  Existing ADH descendants prominently include `Q(sqrt(6))`, `Q(sqrt(2))`, and `Q(sqrt(3))`; I did not find this `Q(sqrt(5))` member.  Treat that as evidence of novelty, not proof.

### Q2. Publication value?

Yes, potentially.  A new golden-field ADH-type component arising naturally from Chan's tenth-order theta identity is a publishable observation if accompanied by proof, HM identification, norm-support theorem, and a ray-class coefficient formula.  The Ramanujan Journal, Research in Number Theory, Journal of Number Theory, Hardy-Ramanujan Journal, Integers, or Journal of Integer Sequences are plausible depending on depth.

### Q3. Identify B explicitly / HM closed form?

The exact identification is

```text
B(X) = -f_{1,3,4}(X,-X^3,X)
```

under standard HM signs.  A direct false-theta closed form is

```text
B(X)
  = - sum_{a,b >= 0} (-1)^b X^(2*a^2 + a + 3*a*b + b*(b+1)/2)
    - sum_{a,b >= 0} (-1)^b X^(2*a^2 + 6*a + 3*a*b + (b^2 + 7*b)/2 + 4).
```

The HM Appell-Lerch part specializes to

```text
G(X)
  = j(-X^3; X^4)  * m(-X^9,  X^20, -1)
    - X*j(-X^6; X^4) * m(-X^4,  X^20, -1)
    + X^3*j(-X^9; X^4) * m(-X^(-1), X^20, -1)
    - X^6*j(-X^12;X^4) * m(-X^(-6), X^20, -1),
```

plus the finite HM theta correction, with a specialization/limit caveat.

### Q4. Systematic method?

Yes.  Search for Hecke-Rogers cone residuals, match them to `f_{a,b,c}`, compute `b^2-ac`, convert the inhomogeneous form into a real-quadratic norm coset, derive inert-prime support, then upgrade to a signed ray-class/Shintani cone coefficient formula.

### Q5. Characterize the 91 cancellation zeros?

They are norm-eligible values for which the signed ray-class representation sum vanishes.  Equivalently, `10N+1` is a norm, but the cone representatives in the relevant congruence class cancel under the sign `(-1)^r` and the `D-A` cone orientation.  A complete characterization should be a finite ray-class character formula modulo `10` and the real-place cone.

### Q6. Partition combinatorics?

A signed partition interpretation is plausible but not yet identified.  The full residual includes the product `j(q;q^5)^2`, which has a direct signed distinct-part interpretation in mod-5 residue classes.  The right target is likely a rank/parity difference on colored partitions with mod-5 restrictions, obtained by finding a Bailey-pair or q-hypergeometric form for the product times the cone series.

## Bottom line

This is a strong lead.  The most valuable next step is to prove the signed ray-class formula for `B_N`.  Once that is in place, the result becomes a clean golden-field analogue of the ADH phenomenon rather than just a numerically verified support observation.
