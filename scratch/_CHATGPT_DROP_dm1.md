# Q3124 (dm1): R8 audit of theorem statements and proof routes

Date: 2026-07-02

## Executive summary

The core algebraic spine is good:

```text
beta(k,r) = (r - 2k) + (4k + 3r + 1) phi
-N(beta(k,r)) = 10 E(k,r) + 1
```

This really does give norm support for the coefficients of the cone series.  The main corrections before Lean formalization are:

1. `L` is **not a sublattice**.  It is an affine coset of the index-10 sublattice `{a+b phi : b-3a == 0 mod 10}`.  This matters in Lean: do not make `L` an `AddSubgroup`.
2. Theorems 1, 3, and 4 are correct as stated.
3. Theorem 2 is correct after replacing “sublattice” by “affine coset”; the inverse formula is the proof, while the Jacobian determinant is only supporting evidence.
4. Theorem 5 is correct if `B_N`, `A`/`D` cones, and finiteness are made explicit.  The norm corollary needs one extra sentence: since the identity gives `-N(beta)=10N+1`, positive norm representability follows by multiplying by `phi`, whose norm is `-1`.
5. Theorem 6’s calculation is correct, but the corollary is ill-posed/too strong.  Since `epsilon*beta` is usually not in `L`, a function whose domain is only `L` cannot even be evaluated at `epsilon*beta`.  The correct conclusion is that the indicator of `L` is not `epsilon`-invariant; it is not that no congruence character can exist.
6. Theorem 7 is essentially correct, but the proof should explicitly use ideals and CRT:
   `O_K/(2 sqrt(5)) ~= O_K/(2) x O_K/(sqrt(5)) ~= F_4 x F_5`.
   The order of `epsilon=phi^2` is indeed `lcm(3,2)=6`.  However, this does **not** by itself prove that the coefficient sequence is governed by an order-6 character.
7. Conjecture A is not really conjectural once the Hickerson-Mortenson sign convention is fixed.  It is a direct term-by-term identity.
8. The proof route for Conjecture B has a serious gap: “two prime ideals above `p`” does **not** imply “at most two atoms in `L`.”  Units give infinitely many generators, and `epsilon^6` preserves `L`.  The cone cut makes the coefficient finite, but the bound and noncancellation require a Shintani-sector theorem.
9. Conjecture E should be reformulated.  “`B` is not multiplicative” only needs one counterexample.  A universal statement `B(pq) != B(p)B(q)` for all tested-style prime pairs is much stronger and may have accidental exceptions.  Also define multiplicativity on the norm variable `M=10N+1`, not on the coefficient index `N`.

## Notation audit

You wrote:

```text
L = {a+b phi in Z[phi] : b-3a = 1 mod 10} (sublattice of index 10)
```

This is the first thing to fix.  `L` is an affine coset, not a sublattice.  It is not closed under addition and does not contain `0`.

Correct formulation:

```text
L0 = {a+b phi in Z[phi] : b-3a == 0 mod 10}
L  = {a+b phi in Z[phi] : b-3a == 1 mod 10}
```

Then `L0` is an index-10 sublattice of `O_K`, and `L` is one affine coset of `L0`.

Lean implication:

```text
Use Set O_K or a structure carrying a congruence predicate for L.
Do not define L as an AddSubgroup/Submodule.
```

## Theorem 1: exponent parity

### Statement

Correct.

For all integers `k,r`,

```text
Q(k,r) = 4k^2 + 2k + r^2 + (6k+1)r
```

is even.

### Proof

Correct and complete:

```text
Q(k,r) = 2(2k^2 + k + 3kr) + r(r+1).
```

The first term is even, and `r(r+1)` is even.

### Lean note

Define

```text
E(k,r) = Q(k,r) / 2
```

only after proving divisibility, or define directly as

```text
E(k,r) = 2*k^2 + k + 3*k*r + r*(r+1)/2.
```

The second definition is usually easier in Lean, because `r*(r+1)/2` still needs an integrality lemma but avoids quotienting the whole expression.

## Theorem 2: bijection

### Statement

Correct after changing “sublattice” to “affine coset.”

The map

```text
F : Z^2 -> L
F(k,r) = beta(k,r) = (r-2k) + (4k+3r+1) phi
```

is a bijection from `Z^2` to the affine coset `L`.

### Proof audit

Let

```text
a = r - 2k,
b = 4k + 3r + 1.
```

Then

```text
b - 3a = 4k + 3r + 1 - 3(r - 2k)
        = 10k + 1,
```

so `F(k,r) in L`.

Conversely, if `a+b phi in L`, then

```text
k = (b - 3a - 1) / 10,
r = a + 2k.
```

Since `b-3a == 1 mod 10`, `k` is an integer.  Then `r` is an integer.  Substitution gives

```text
r - 2k = a,
4k + 3r + 1 = b.
```

So the inverse formula proves both injectivity and surjectivity.

The Jacobian matrix of the affine map is

```text
[[-2, 1],
 [ 4, 3]],
```

with determinant `-10`.  This agrees with the index, but it is not by itself a proof of surjectivity onto the correct affine coset.  Keep it as a check, not as the main proof.

### Edge case

No issue at `k=0` or `r=0`.  The affine shift `+1` in `b` is essential; omitting it changes the coset.

## Theorem 3: norm identity

### Statement

Correct.

For

```text
a = r - 2k,
b = 4k + 3r + 1,
N(a+b phi) = a^2 + ab - b^2,
```

one has

```text
-N(beta(k,r)) = 10*E(k,r) + 1.
```

### Proof audit

Direct expansion gives

```text
N(beta(k,r))
  = (r-2k)^2
    + (r-2k)(4k+3r+1)
    - (4k+3r+1)^2

  = -20k^2 - 10k - 30kr - 5r^2 - 5r - 1.
```

Meanwhile

```text
10 E(k,r) + 1
  = 10 * (2k^2 + k + 3kr + r(r+1)/2) + 1
  = 20k^2 + 10k + 30kr + 5r^2 + 5r + 1.
```

So the identity follows.

### Hidden assumption

The norm convention must be fixed exactly as

```text
N(a+b phi) = a^2 + ab - b^2.
```

This uses `phi^2=phi+1`, trace `Tr(phi)=1`, and norm `N(phi)=-1`.

## Theorem 4: sign simplification

### Statement

Correct.

If `a = r - 2k`, then

```text
(-1)^r = (-1)^a.
```

### Proof

Since

```text
r = a + 2k,
```

`r` and `a` have the same parity.

### Corollary audit

The corollary is correct if `B = D - A` and the cone signs are as stated:

```text
A-cone contribution: -(-1)^r = -(-1)^a
D-cone contribution: +(-1)^r = +(-1)^a.
```

Make the boundary convention explicit:

```text
A-cone: k >= 0 and r >= 0
D-cone: k < 0 and r < 0
```

There is no overlap between these cones.

## Theorem 5: exact formula

### Statement

Correct after adding explicit definitions and finiteness.

Recommended statement:

```text
Let B(X) = D(X) - A(X) = sum_{N >= 0} B_N X^N,
where

A(X) = sum_{k>=0, r>=0} (-1)^r X^{E(k,r)},
D(X) = sum_{k<0, r<0} (-1)^r X^{E(k,r)}.

For N >= 0, let S(N) be the set of beta=a+b phi in L such that

  -N_{K/Q}(beta) = 10N + 1

and whose inverse atom (k,r) lies in the A-cone or D-cone.  Define

  W(beta) = -(-1)^a  in the A-cone,
  W(beta) = +(-1)^a  in the D-cone.

Then

  B_N = sum_{beta in S(N)} W(beta).
```

### Proof audit

The proof is direct from Theorems 2-4, but two details should not be skipped.

First, the cone conditions in `(a,b)` coordinates are:

```text
k = (b - 3a - 1) / 10,
r = (4a + 2b - 2) / 10 = (2a + b - 1) / 5.
```

So:

```text
A-cone: b - 3a - 1 >= 0 and 2a + b - 1 >= 0,
D-cone: b - 3a - 1 <  0 and 2a + b - 1 <  0.
```

Second, the coefficient sum is finite.  This is not automatic from the norm equation alone, because the unit group is infinite.  It follows from the cone definitions.  On the A-cone,

```text
E(k,r) = 2k^2 + k + 3kr + r(r+1)/2
```

grows positively for `k,r >= 0`.  On the D-cone, set `k=-u-1`, `r=-v-1` with `u,v >= 0`.  Then

```text
E(-u-1,-v-1)
  = 2u^2 + 6u + 3uv + (v^2 + 7v)/2 + 4,
```

which also grows positively.  Hence only finitely many atoms contribute to a fixed `N`.

### Norm-support corollary

The corollary needs a sign clarification.

Theorem 3 gives

```text
-N(beta) = 10N + 1.
```

This says `10N+1` is the negative of a norm.  Since `N(phi)=-1`, it is also a positive norm:

```text
N(phi * beta) = N(phi) N(beta) = -N(beta) = 10N + 1.
```

So the corrected corollary is:

```text
B_N != 0 implies 10N+1 is a norm from O_K.
```

The proof uses the existence of a contributing beta and multiplication by `phi`.

## Theorem 6: instability of L under epsilon=phi^2

### Statement

The computation is correct, but the statement should be worded more carefully.

Let

```text
epsilon = phi^2 = 1 + phi.
```

For `beta=a+b phi`,

```text
epsilon beta = (a+b) + (a+2b) phi.
```

Thus, if

```text
a' = a+b,
b' = a+2b,
```

then

```text
b' - 3a' = (a+2b) - 3(a+b) = -2a - b.
```

If `beta in L`, then `b == 3a+1 mod 10`, so

```text
b' - 3a' == -5a - 1 mod 10.
```

This is never congruent to `1 mod 10`: if `a` is even it is `9 mod 10`, and if `a` is odd it is `4 mod 10`.  Therefore

```text
epsilon L cap L = empty.
```

That is the clean theorem.

### Corollary problem

The proposed corollary

```text
No congruence character chi on L with chi(epsilon*beta)=chi(beta) can exist.
```

is not a good mathematical statement as written.

Problem: if `chi` is only defined on `L`, then `chi(epsilon*beta)` is usually not defined, because `epsilon*beta notin L`.

Also, if `chi` is instead a character on a larger residue group or on `O_K`, then such characters can certainly exist, for example any character with `chi(epsilon)=1` is invariant under multiplication by `epsilon` on its domain.

Correct replacement:

```text
The indicator function 1_L is not invariant under multiplication by epsilon.
Equivalently, the affine congruence support L is not stable under the full positive unit group generated by epsilon.
```

A useful strengthening is:

```text
epsilon^3 L is the coset b-3a == -1 mod 10,
epsilon^6 L = L.
```

So the first totally positive unit power preserving `L` is expected to be `epsilon^6`, not `epsilon`.

This is important for the Shintani proof route: reduce by the subgroup generated by `epsilon^6`, not by the full group generated by `epsilon`.

## Theorem 7: order of epsilon modulo 2 sqrt(5)

### Statement

The statement is correct:

```text
epsilon = phi^2 has order 6 in (O_K / (2 sqrt(5)))^x.
```

Here `(2 sqrt(5))` should be read as the principal ideal generated by `2 sqrt(5) = 2(2phi-1)`.

### Proof audit

The proof is basically right but needs the ideal details.

1. The ideals `(2)` and `(sqrt(5))` are coprime, so CRT gives

```text
O_K / (2 sqrt(5)) ~= O_K/(2) x O_K/(sqrt(5)).
```

2. Since the field discriminant is `5 == 5 mod 8`, the prime `2` is inert in `Q(sqrt(5))`.  Equivalently,

```text
O_K/(2) ~= F_4.
```

In this quotient, `phi` satisfies

```text
phi^2 + phi + 1 = 0,
```

so `phi` has order `3` in `F_4^x`.  Hence `epsilon=phi^2` also has order `3` modulo `(2)`.

3. The ideal `(sqrt(5))` is the unique ramified prime above `5`, and

```text
O_K/(sqrt(5)) ~= F_5.
```

Modulo `(sqrt(5))`, we have `sqrt(5)=0`, so

```text
phi = (1 + sqrt(5))/2 == 1/2 == 3 mod 5,
epsilon = phi^2 == 9 == 4 == -1 mod 5.
```

Therefore `epsilon` has order `2` modulo `(sqrt(5))`.

4. In the CRT product, the order is

```text
lcm(3,2) = 6.
```

### What this theorem does not prove

This theorem does **not** prove that `B` is controlled by a genuine order-6 Hecke character.  It only identifies the order of one unit in one finite quotient.

To connect this to the coefficients, you still need separate lemmas showing:

```text
1. how the affine coset L is encoded by a modulus,
2. how the sign (-1)^a or (-1)^r is encoded by the same or a larger modulus,
3. how the Shintani cone/window interacts with multiplication by epsilon^6.
```

The order-6 residue fact is useful, but it is not the same as the observed six-sector coefficient phenomenon.

## Conjecture A: HM identification

### Verdict

This should be promoted from conjecture to theorem once the HM convention is fixed.

With the standard Hickerson-Mortenson convention

```text
f_{a,b,c}(x,y,q)
  = sum_{sg(m)=sg(n)} sg(m) (-1)^{m+n} x^m y^n
      q^{a*binom(m,2) + bmn + c*binom(n,2)},
```

where `sg(t)=+1` for `t>=0` and `sg(t)=-1` for `t<0`, one gets

```text
f_{1,3,4}(X, -X^3, X) = A(X) - D(X).
```

Indeed the summand is

```text
sg(m) (-1)^{m+n} X^m (-X^3)^n
  X^{binom(m,2) + 3mn + 4binom(n,2)}.
```

The sign simplifies to `sg(m)(-1)^m`, and the exponent is

```text
m + 3n + binom(m,2) + 3mn + 4binom(n,2)
= m(m+1)/2 + 3mn + 2n^2 + n.
```

Setting `m=r` and `n=k` gives exactly `E(k,r)`.  The same-sign nonnegative cone contributes `A`, and the same-sign negative cone contributes `-D`.  Therefore

```text
B(X) = D(X) - A(X) = -f_{1,3,4}(X, -X^3, X).
```

If your local definition of `f` differs by a global sign or by the convention for `sg(0)`, this must be adjusted.  With HM's usual `sg(0)=+1`, the statement above is right.

## Conjecture B: prime nonvanishing

### Statement

The statement is plausible but needs sharper formulation.

Recommended statement:

```text
Let p be a rational prime with p == 1 mod 10, and set N=(p-1)/10.
Then B_N is in {-2,-1,+1,+2}.
```

This avoids ambiguity about “split prime,” since every prime `p == 1 mod 10` is split in `Q(sqrt(5))` and is represented in the `10N+1` family.

### Main gap in the proposed proof route

The proposed route says:

```text
(1) two ideals above p,
(2) <=2 atoms in L,
(3) same cone,
(4) same parity.
```

Step (2) is not justified and is the central hard point.

A split prime gives two prime ideals above `p`, but each ideal has infinitely many generators because the unit group is infinite.  Moreover `epsilon^6` preserves `L`, so even within the affine coset `L` there are infinite unit translates of a generator satisfying the same norm equation.  The cone restriction makes the coefficient finite, but it does not follow from “two ideals above p” that there are at most two contributing atoms.

The real statement you need is a Shintani-sector theorem:

```text
For each of the two prime-ideal unit orbits of norm p, after imposing
b-3a == 1 mod 10 and reducing modulo epsilon^6, the A/D cone window
selects at most one representative; and across the two orbits the selected
representatives have non-opposite weights.
```

That is much stronger than the current proof route.

### What must be proved

A sound proof route is:

1. Work with the coefficient formula from Theorem 5.
2. Replace the full unit group by the subgroup `Gamma=<epsilon^6>` that preserves `L`.
3. Describe a fundamental Shintani strip for `Gamma` in the real embeddings.
4. Make a finite residue table modulo a modulus large enough to encode:

```text
b-3a == 1 mod 10,
(-1)^a,
A-cone versus D-cone boundary behavior.
```

Modulo `20` is likely safer than modulo `10`, because parity signs are visible.

5. For a prime norm `p`, prove that the two prime-ideal orbits intersect the selected Shintani windows in either one or two representatives.
6. Prove a finite “no opposite-sign pair” lemma for those representatives.

Only after these steps do you get

```text
B_N in {-2,-1,+1,+2}.
```

### Boundary cases

Check primes where the representative lands on a cone boundary:

```text
k=0, r>=0,
r=0, k>=0
```

These belong to `A`, not to `D`.  For prime `p`, the constant term boundary `N=0` is irrelevant, but other boundary atoms can occur and must be included in the finite table.

## Conjecture C: cancellation zeros composite

This is essentially a corollary of Conjecture B, not an independent conjecture.

If Conjecture B is proved, then no coefficient with `10N+1` prime can vanish.  Therefore every zero among norm-eligible `N` with `B_N=0` must have composite `10N+1`.

Recommended formulation:

```text
Assuming Conjecture B, all cancellation zeros occur at composite norm values.
```

Do not state it as a separate theorem unless you prove Conjecture B.

## Conjecture D: equidistribution

### Statement

Plausible, but it depends on the same finite Shintani-sector table as Conjecture B.

You want something like:

```text
Among primes p == 1 mod 10,
|B_{(p-1)/10}| = 1 with density 2/3,
|B_{(p-1)/10}| = 2 with density 1/3.
```

### Hardest gap

You must prove that the prime coefficient is determined by a six-sector step function whose sectors have equal measure and whose values have absolute value pattern

```text
1, 1, 2, 1, 1, 2
```

up to cyclic order.

Then the density follows from equidistribution of prime ideal generators in the real-unit torus, with the finite ray class fixed.

So the proof splits into two independent hard facts:

```text
finite table: coefficient value = six-sector step function,
analytic number theory: split prime generators equidistribute among these sectors.
```

The second is standard Hecke equidistribution for real quadratic fields, but the first is your real work.

## Conjecture E: non-multiplicativity

### Statement problem

You should define the arithmetic function on norm values, not on coefficient indices.

Define

```text
a(M) = B_{(M-1)/10}
```

for positive integers `M == 1 mod 10`, and `a(M)=0` otherwise if you want a function on all positive integers.

Then multiplicativity means

```text
a(M1*M2) = a(M1)*a(M2)
```

for coprime `M1,M2`.

In terms of coefficient indices, if

```text
M1 = 10N1 + 1,
M2 = 10N2 + 1,
```

then the product corresponds to

```text
M1*M2 = 10N12 + 1,
N12 = (M1*M2 - 1)/10,
```

not to `N1*N2`.

### Proof status

The statement “`B` is not multiplicative” only needs one explicit coprime counterexample.  That should be a theorem once you record a single checked pair.

The stronger statement suggested by the data,

```text
a(pq) != a(p)*a(q) for all tested prime pairs,
```

is probably too strong to state as a theorem without a conceptual reason.  It may have accidental exceptions at larger primes.  A safer conjecture is:

```text
The equality a(pq)=a(p)a(q) has density 0 among eligible split-prime pairs.
```

or simply:

```text
The function a is not multiplicative; the obstruction is the Shintani cone carry.
```

### Correct structural explanation

The finite congruence data is multiplicative.  The archimedean cone window is not.

Multiplying two reduced generators usually leaves the chosen Shintani strip.  Reducing back into the strip requires multiplying by a power of `epsilon^6`; the exponent is a floor-function carry in logarithmic embedding coordinates.  That carry changes cone membership and sometimes parity signs.  This is the correct reason for non-multiplicativity.

## Theorem 7 and CRT: more detailed ideal checklist

Before Lean or paper formalization, state the following lemmas separately.

```text
sqrt5 = 2phi - 1 in O_K.
```

```text
(sqrt5)^2 = 5, so (sqrt5) is the unique prime over 5 and
O_K/(sqrt5) ~= F_5.
```

```text
The minimal polynomial of phi is T^2 - T - 1.
Modulo 2 this becomes T^2 + T + 1, irreducible over F_2, so
O_K/(2) ~= F_4.
```

```text
The ideals (2) and (sqrt5) are coprime, hence
O_K/(2sqrt5) ~= O_K/(2) x O_K/(sqrt5).
```

```text
epsilon=phi^2 has order 3 in F_4^x and order 2 in F_5^x.
Therefore epsilon has order 6 in (O_K/(2sqrt5))^x.
```

The theorem is fine if written this way.

## Minimal verification oracle

This is not needed for the proof, but it is a useful way to check the formulas before Lean formalization.

```python
from dataclasses import dataclass
from typing import Optional, Tuple


@dataclass(frozen=True)
class PhiElt:
    """Element a + b*phi in Z[phi], where phi^2 = phi + 1."""
    a: int
    b: int


def norm_phi(x: PhiElt) -> int:
    """Norm N(a+b*phi) = a^2 + ab - b^2."""
    return x.a * x.a + x.a * x.b - x.b * x.b


def beta(k: int, r: int) -> PhiElt:
    return PhiElt(a=r - 2 * k, b=4 * k + 3 * r + 1)


def q_form(k: int, r: int) -> int:
    return 4 * k * k + 2 * k + r * r + (6 * k + 1) * r


def exponent_E(k: int, r: int) -> int:
    q = q_form(k, r)
    if q % 2 != 0:
        raise ValueError((k, r, q))
    return q // 2


def in_L(x: PhiElt) -> bool:
    return (x.b - 3 * x.a - 1) % 10 == 0


def inverse_atom(x: PhiElt) -> Optional[Tuple[int, int]]:
    num_k = x.b - 3 * x.a - 1
    if num_k % 10 != 0:
        return None
    k = num_k // 10
    r = x.a + 2 * k
    return k, r


def epsilon_mul(x: PhiElt) -> PhiElt:
    """Multiply by epsilon=phi^2=1+phi."""
    return PhiElt(a=x.a + x.b, b=x.a + 2 * x.b)


def check_core_identity(k: int, r: int) -> bool:
    x = beta(k, r)
    return in_L(x) and inverse_atom(x) == (k, r) and -norm_phi(x) == 10 * exponent_E(k, r) + 1
```

## Final verdict table

```text
Theorem 1: correct.
Theorem 2: correct after replacing “sublattice” by “affine coset”; inverse proof is essential.
Theorem 3: correct.
Theorem 4: correct.
Theorem 5: correct after adding definitions, cone inequalities, and finiteness; norm corollary needs the phi sign fix.
Theorem 6: computation correct; corollary ill-posed/too strong.  Replace with non-invariance of 1_L and use epsilon^6 as stabilizer.
Theorem 7: correct, but write it with ideals and CRT; do not overinterpret it as an order-6 Hecke-character explanation.
Conjecture A: should be a theorem under standard HM signs.
Conjecture B: plausible, but current route has a major gap at “<=2 atoms.”  Needs a finite Shintani-sector table modulo epsilon^6.
Conjecture C: follows from B; not independent.
Conjecture D: plausible; depends on B plus equidistribution of prime generators among equal Shintani sectors.
Conjecture E: reformulate on norm values.  Non-multiplicativity is easy once one counterexample is recorded; universal prime-pair inequality is much stronger and may be false.
```

## Most important fix before Lean

Define the arithmetic object as an affine-coset Shintani count:

```text
B_N = sum_{beta in O_K,
          b-3a == 1 mod 10,
          -N(beta)=10N+1,
          beta in A/D cone}
        W(beta).
```

Then prove the bijection with `(k,r)` atoms and the norm identity.  After that, handle units only through the subgroup preserving the affine coset, expected to be generated by `epsilon^6`.  This avoids the two main traps: treating `L` as a sublattice, and treating the order-6 residue phenomenon as a genuine multiplicative character before the Shintani window has been analyzed.
