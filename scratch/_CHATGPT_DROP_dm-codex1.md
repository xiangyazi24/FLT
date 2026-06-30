# Q2548: audited descent route for primitive centered four-square APs

## Bottom line

The Q2536 route is the right one.  The direct published descent is Alf van der Poorten, *Fermat's Four Squares Theorem*, arXiv:0712.3850.  In the notation of the current Lean project, his proof translates cleanly as

```text
primitive centered AP
  -> EulerSquarePair(A,D): 4*A^2 + D^2 and 16*A^2 + D^2 are squares, with N = A*D
  -> smaller EulerSquarePair(a,d), with |a*d| < |A*D|
  -> smaller primitive centered AP with N' = a*d.
```

There is no polynomial one-line construction of roots of the smaller AP from the original roots.  The descent necessarily passes through Pythagorean parametrization and coprime square-product extraction.

One important correction: the residual

```lean
def PrimitiveCenteredFourSqAPDescent : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ T : PrimitiveCenteredFourSqAP, T.N.natAbs < S.N.natAbs
```

is false if `PrimitiveCenteredFourSqAP` permits the degenerate constant case `S.N = 0`, since no natural number is `< 0`.  The true theorem must either be

```lean
∀ S : PrimitiveCenteredFourSqAP,
  S.N ≠ 0 → ∃ T : PrimitiveCenteredFourSqAP, T.N.natAbs < S.N.natAbs
```

or the structure must already include nontriviality, e.g. `N ≠ 0`.

---

## 1. Normalized centered AP data

Use roots `p,q,r,s` and center `X` with

```text
p^2 = X - 6*N
q^2 = X - 2*N
r^2 = X + 2*N
s^2 = X + 6*N
```

so the common difference is

```text
q^2 - p^2 = r^2 - q^2 = s^2 - r^2 = 4*N.
```

The available identities

```text
p^2 + r^2 = 2*q^2,
q^2 + s^2 = 2*r^2,
(r-p)(r+p) = 8*N,
(s-q)(s+q) = 8*N
```

are exactly compatible with this centering.

For descent, normalize signs as follows.

```text
N > 0,
X > 6*N,
p,q,r,s odd,
the four roots are pairwise coprime.
```

If the original `N < 0`, reverse the AP.  This replaces `N` by `-N` and preserves `N.natAbs`.  Signs of `p,q,r,s` do not matter.

Because the roots are odd, odd squares are `1 mod 8`, hence the common difference `4*N` is divisible by `8`; therefore

```text
N is even.
```

This parity is useful below: after `N = A*D` with `D` odd, it implies `A` is even.

---

## 2. From primitive centered AP to EulerSquarePair

Let

```text
Y = p*q*r*s.
```

Then

```text
Y^2 = (X^2 - 36*N^2) * (X^2 - 4*N^2)
```

and therefore

```text
Y^2 + (16*N^2)^2 = (X^2 - 20*N^2)^2.        (1)
```

Indeed,

```text
(X^2 - 20*N^2)^2 - (16*N^2)^2
= X^4 - 40*X^2*N^2 + 144*N^4
= (X^2 - 36*N^2)(X^2 - 4*N^2).
```

Primitive hypotheses give

```text
gcd(16*N^2, Y) = 1.
```

Reason: roots are odd, and if an odd prime divides both `N` and one root, the centered equations force it to divide all four roots, contradicting primitivity.

Thus `(16*N^2, Y, X^2 - 20*N^2)` is a primitive Pythagorean triple.  Use the parametrization with even leg `4*u*v`:

```text
16*N^2 = 4*u*v,
Y = ±(4*u^2 - v^2),
X^2 - 20*N^2 = 4*u^2 + v^2,
gcd(2*u, v) = 1,
v odd,
u > 0,
v > 0.
```

From `u*v = 4*N^2` and `gcd(u,v)=1`, square extraction gives

```text
u = 4*A^2,
v = D^2,
N = A*D,
D odd,
gcd(A,D)=1.
```

Since `N` is even and `D` is odd, `A` is even.

Now use

```text
X^2 - 20*N^2 = 4*u^2 + v^2,
N^2 = u*v/4.
```

Then

```text
X^2 = 4*u^2 + 5*u*v + v^2 = (4*u + v)(u + v).
```

Substituting `u = 4*A^2`, `v = D^2`,

```text
X^2 = (16*A^2 + D^2) * (4*A^2 + D^2).       (2)
```

The two factors are coprime:

```text
gcd(16*A^2 + D^2, 4*A^2 + D^2) = 1.
```

Reason: any common prime divides their difference `12*A^2`; since it also divides `4*A^2 + D^2` and `gcd(A,D)=1`, it can only be `2` or `3`; `D` odd excludes `2`, and squares mod `3` exclude `3` unless both `A,D` are divisible by `3`.

Therefore both factors in (2) are squares.  There exist odd positive integers `B,C` such that

```text
B^2 = 16*A^2 + D^2,
C^2 = 4*A^2 + D^2.                           (E)
```

This is the EulerSquarePair package.

### Lean-facing intermediate theorem

```text
AP_to_EulerSquarePair:
Given a nontrivial primitive centered four-square AP with N > 0,
there exist A,D,B,C such that
  N = A*D,
  A ≠ 0,
  D ≠ 0,
  A is even,
  D is odd,
  gcd(A,D)=1,
  B^2 = 16*A^2 + D^2,
  C^2 = 4*A^2 + D^2.
```

---

## 3. Descent on EulerSquarePair

Assume the EulerSquarePair data

```text
A ≠ 0,
D ≠ 0,
A even,
D odd,
gcd(A,D)=1,
B^2 = 16*A^2 + D^2,
C^2 = 4*A^2 + D^2.
```

The two equations are primitive Pythagorean triples:

```text
(2*A)^2 + D^2 = C^2,
(4*A)^2 + D^2 = B^2.
```

### First parametrization

From `(2*A)^2 + D^2 = C^2`, choose coprime integers `U,V`, of opposite parity, with the even one named `U`, such that

```text
A = U*V,
σ*D = U^2 - V^2,
U even,
V odd,
gcd(U,V)=1,
σ ∈ {+1,-1}.
```

The sign `σ` is forced by `D mod 4`: since `U` is even and `V` odd,

```text
U^2 - V^2 ≡ -1 mod 4.
```

So `σ*D` is the representative of `±D` congruent to `-1 mod 4`.

### Second parametrization

From `(4*A)^2 + D^2 = B^2`, use the parametrization with even leg `4*U'*V'`:

```text
A = U'*V',
τ*D = 4*U'^2 - V'^2,
U' even,
V' odd,
gcd(2*U', V')=1,
τ ∈ {+1,-1}.
```

Again

```text
4*U'^2 - V'^2 ≡ -1 mod 4,
```

so the sign is the same as before:

```text
τ = σ.
```

This same-sign fact is important.  It is the sign point that can silently break the descent if omitted.

### Refining the two factorizations of `A`

We have two coprime factorizations of the same even integer:

```text
A = U*V = U'*V'.
```

With `U,U'` even and `V,V'` odd, refine the prime allocations as follows.  There exist integers `a,b,c,d`, nonzero, with `2*a,b,c,d` pairwise coprime, such that after sign changes

```text
U  = 2*a*b,
V  = c*d,
U' = 2*a*c,
V' = b*d.
```

Consequently

```text
A = 2*a*b*c*d.                               (3)
```

Substitute these into the two expressions for the same signed `D`:

```text
σ*D = 4*a^2*b^2 - c^2*d^2,
σ*D = 16*a^2*c^2 - b^2*d^2.                 (4)
```

Equating the right sides gives

```text
4*a^2*b^2 - c^2*d^2 = 16*a^2*c^2 - b^2*d^2.
```

Rearrange:

```text
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2). (5)
```

The factors on the right are coprime:

```text
gcd(4*a^2 + d^2, 16*a^2 + d^2) = 1.
```

Reason: a common prime divides `12*a^2`.  Since `gcd(a,d)=1`, it can only be `2` or `3`; `d` odd excludes `2`, and the mod-`3` square check excludes `3`.

Also `gcd(b,c)=1`.  Therefore (5) forces square extraction:

```text
c^2 = 4*a^2 + d^2,
b^2 = 16*a^2 + d^2.                         (E')
```

Thus `(a,d)` is a new EulerSquarePair.

### Strict inequality

From (3),

```text
A = 2*a*b*c*d.
```

Since `a,d` are nonzero and

```text
c^2 = 4*a^2 + d^2 > d^2,
b^2 = 16*a^2 + d^2 > d^2,
```

we have `|b| > 1` and `|c| > 1`.  Hence

```text
|a*d| < |2*a*b*c*d| = |A|.
```

Since `D` is a nonzero integer,

```text
|A| ≤ |A*D|.
```

Therefore

```text
0 < |a*d| < |A*D|.                           (6)
```

This is the required descent inequality.  If the original AP has `N = A*D`, then the smaller parameter is

```text
N' = a*d,
|N'| < |N|.
```

### Lean-facing intermediate theorem

```text
EulerSquarePair_descent:
Assume
  A ≠ 0, D ≠ 0,
  A even, D odd,
  gcd(A,D)=1,
  B^2 = 16*A^2 + D^2,
  C^2 = 4*A^2 + D^2.
Then there exist a,d,b,c such that
  a*d ≠ 0,
  2*a, b, c, d are pairwise coprime,
  d is odd,
  b^2 = 16*a^2 + d^2,
  c^2 = 4*a^2 + d^2,
  |a*d| < |A*D|.
```

This is the core classical descent step.

---

## 4. Reconstructing the smaller centered AP from EulerSquarePair(a,d)

Now assume

```text
b^2 = 16*a^2 + d^2,
c^2 = 4*a^2 + d^2,
a*d ≠ 0,
2*a,b,c,d pairwise coprime,
d odd.
```

Choose signs so that

```text
N' = |a*d| > 0,
X' = |b*c| > 0.
```

Equivalently, in an integer implementation, replace `a,d,b,c` by sign variants so that `a*d > 0` and `b*c > 0`.  The square equations are unchanged.

Define

```text
N' = a*d,
X' = b*c.
```

With the positive-sign convention, `N' > 0` and `X' > 0`.

The product identities are

```text
(X' - 2*N') * (X' + 2*N')
  = (b*c)^2 - 4*a^2*d^2
  = (d^2 + 8*a^2)^2,                         (7)
```

and

```text
(X' - 6*N') * (X' + 6*N')
  = (b*c)^2 - 36*a^2*d^2
  = (d^2 - 8*a^2)^2.                         (8)
```

The required positivity is automatic:

```text
X'^2 - 36*N'^2 = (d^2 - 8*a^2)^2 > 0,
```

where equality would imply `d^2 = 8*a^2`, impossible for nonzero integers.  Thus

```text
X' > 6*N' > 0.
```

Now prove the gcds:

```text
gcd(X' - 2*N', X' + 2*N') = 1,
gcd(X' - 6*N', X' + 6*N') = 1.
```

For the inner pair, any common divisor divides both `2*X' = 2*b*c` and `4*N' = 4*a*d`.  The two factors are odd, so it divides both `b*c` and `a*d`; pairwise coprimality excludes this.

For the outer pair, any common divisor divides both `2*b*c` and `12*a*d`.  Again the factors are odd; pairwise coprimality excludes all primes except possibly `3`.  But `3` cannot divide `b` or `c`, since

```text
b^2 = 16*a^2 + d^2 ≡ a^2 + d^2 mod 3,
c^2 = 4*a^2 + d^2  ≡ a^2 + d^2 mod 3,
```

and `a^2 + d^2 ≠ 0 mod 3` unless `3` divides both `a` and `d`, contradicting `gcd(a,d)=1`.

By (7), (8), positivity, and coprime-product square extraction, all four numbers

```text
X' - 6*N',
X' - 2*N',
X' + 2*N',
X' + 6*N'
```

are integer squares.  Choose roots `p',q',r',s'` by square extraction:

```text
p'^2 = X' - 6*N',
q'^2 = X' - 2*N',
r'^2 = X' + 2*N',
s'^2 = X' + 6*N'.                            (9)
```

Then

```text
q'^2 - p'^2 = 4*N',
r'^2 - q'^2 = 4*N',
s'^2 - r'^2 = 4*N'.
```

So `(p',q',r',s',N')` is a centered four-square AP.

The same divisor arguments, applied to differences among the four centered values, give primitivity and odd roots.  In particular, all four values are odd because `X' = b*c` is odd and `2*N'`, `6*N'` are even; hence all roots are odd.

### Lean-facing intermediate theorem

```text
EulerSquarePair_to_PrimitiveCenteredAP:
Assume
  a*d ≠ 0,
  2*a,b,c,d pairwise coprime,
  d odd,
  b^2 = 16*a^2 + d^2,
  c^2 = 4*a^2 + d^2.
Then there exists T : PrimitiveCenteredFourSqAP such that
  T.N = a*d        -- after sign normalization, or T.N.natAbs = |a*d|
```

For an integer-valued Lean implementation that avoids sign clutter, state the conclusion as

```text
∃ T : PrimitiveCenteredFourSqAP, T.N.natAbs = (a*d).natAbs.
```

That is enough for the final inequality.

---

## 5. Final descent theorem DAG

The clean proof of the corrected residual is:

```text
Input: S : PrimitiveCenteredFourSqAP, S.N ≠ 0.

1. Normalize S so N > 0.

2. Apply AP_to_EulerSquarePair:
     obtain A,D,B,C with
       S.N = A*D,
       B^2 = 16*A^2 + D^2,
       C^2 = 4*A^2 + D^2,
       gcd(A,D)=1,
       A even, D odd.

3. Apply EulerSquarePair_descent:
     obtain a,d,b,c with
       b^2 = 16*a^2 + d^2,
       c^2 = 4*a^2 + d^2,
       |a*d| < |A*D| = |S.N|.

4. Apply EulerSquarePair_to_PrimitiveCenteredAP:
     obtain T : PrimitiveCenteredFourSqAP with
       T.N.natAbs = |a*d|.

5. Conclude
       T.N.natAbs < S.N.natAbs.
```

Thus the precise replacement for the currently too-strong residual is:

```text
PrimitiveCenteredFourSqAPDescent_nontrivial:
  ∀ S : PrimitiveCenteredFourSqAP,
    S.N ≠ 0 →
      ∃ T : PrimitiveCenteredFourSqAP,
        T.N.natAbs < S.N.natAbs.
```

If the existing `PrimitiveCenteredFourSqAP` type already includes `N ≠ 0`, then the original residual follows directly.

---

## 6. Where `(xy-wz)(xy+wz)=2Δ^2` fits

For the original roots, with

```text
Δ = q^2 - p^2 = 4*N,
```

the checked identity is

```text
(q*r - p*s) * (q*r + p*s) = 2*Δ^2 = 32*N^2.
```

This identity is correct and useful for local gcd bookkeeping, but it is not by itself the descent map.  The descent map uses the larger Pythagorean triple

```text
(16*N^2)^2 + (p*q*r*s)^2 = (X^2 - 20*N^2)^2,
```

then obtains the concordant/Euler square pair

```text
D^2 + 4*A^2 = C^2,
D^2 + 16*A^2 = B^2,
N = A*D,
```

and finally descends by the explicit factorization

```text
U  = 2*a*b,
V  = c*d,
U' = 2*a*c,
V' = b*d,
A  = 2*a*b*c*d,
σ*D = 4*a^2*b^2 - c^2*d^2
    = 16*a^2*c^2 - b^2*d^2,
N' = a*d,
|N'| < |N|.
```

These are the formulas to formalize.
