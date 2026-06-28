# Q1995 (dm3): should `QuarticDescent.lean` and `QuarticDescentN16.lean` be unified?

## Executive answer

Yes, the N = 10 and N = 16 quartic descents can be unified **algebraically**.  The common signed quartic is

```text
s^2 = r^4 + eps*r^2*B^2 - B^4,
```

with

```text
eps = +1  for N = 10,
eps = -1  for N = 16.
```

The central identity is exactly

```text
(2*r^2 + eps*B^2)^2 - (2*s)^2 = 5*B^4.
```

However, I would **not immediately replace** the two existing 0-sorry files by one fully sign-parametric file.  Since you already have

```text
QuarticDescent.lean      -- N = 10, 1128 lines, 0 sorry
QuarticDescentN16.lean   -- N = 16,  652 lines, 0 sorry
```

the safest refactor is incremental:

```text
1. create a shared core file, e.g. QuarticDescentCore.lean;
2. move only the sign-stable lemmas into it;
3. keep QuarticDescent.lean and QuarticDescentN16.lean as thin specialization files;
4. only later consider a single public theorem parameterized by eps.
```

A full unification is possible, but it will probably save less code than it first appears, because the parity front end and some normalization lemmas remain sign-sensitive.

## How much code can be shared?

A realistic estimate is:

```text
Definitely shareable:        55%–70%
Better left duplicated/cased: 30%–45%
```

Given your current sizes, a good refactor might look like:

```text
QuarticDescentCore.lean       700–900 lines
QuarticDescent.lean           150–250 lines
QuarticDescentN16.lean        100–200 lines
```

So the total could drop from roughly

```text
1128 + 652 = 1780 lines
```

to perhaps

```text
950–1300 lines.
```

That is a meaningful cleanup, but not a reason to risk destabilizing two finished proofs unless you expect to maintain or generalize this descent further.

## Best conceptual boundary for sharing

The clean boundary is **after the sign-sensitive parity and factor-normalization stage**.

The shared core should start from a theorem of this shape:

```text
Given eps ∈ {+1,-1}, positive coprime a,b, and

  z^2 = (a^2 - eps*b^2)^2 + 4*b^4,

produce a smaller primitive solution to

  s^2 = r^4 + eps*r^2*B^2 - B^4.
```

This is the genuinely common descent step.  The proof is the same for both signs.

The front end should remain specialized, or at least branch heavily on `eps`, because N = 10 and N = 16 differ in the parity analysis before reaching this common Pythagorean identity.

## What is shared algebraically?

### 1. The master identity

For both signs,

```text
s^2 = r^4 + eps*r^2*B^2 - B^4
```

implies

```text
(2*r^2 + eps*B^2)^2 - (2*s)^2 = 5*B^4.
```

Indeed,

```text
(2*r^2 + eps*B^2)^2 - (2*s)^2
= 4*r^4 + 4*eps*r^2*B^2 + B^4 - 4*s^2
= 4*r^4 + 4*eps*r^2*B^2 + B^4
  - 4*(r^4 + eps*r^2*B^2 - B^4)
= 5*B^4.
```

Only `eps^2 = 1` is used.

### 2. The coprime product structure

The raw factors are

```text
L = 2*r^2 + eps*B^2 - 2*s,
R = 2*r^2 + eps*B^2 + 2*s.
```

They always satisfy

```text
L*R = 5*B^4.
```

After the appropriate parity normalization, the coprime fourth-power split has the same structure for both signs:

```text
U*V = 5*C^4,
gcd(U,V) = 1,
```

and therefore either

```text
U = a^4,      V = 5*b^4,     C = a*b,
```

or

```text
U = 5*a^4,    V = b^4,       C = a*b.
```

This factorization infrastructure should be shared.

### 3. The post-factorization identity

In the branch

```text
U = a^4,
V = 5*b^4,
C = a*b,
```

the sum of the factor equations gives the sign-parametric identity

```text
z^2 = (a^2 - eps*b^2)^2 + 4*b^4.
```

So the two concrete cases are:

```text
eps = +1:  z^2 = (a^2 - b^2)^2 + 4*b^4;
eps = -1:  z^2 = (a^2 + b^2)^2 + 4*b^4.
```

The reversed branch gives the symmetric version

```text
z^2 = (b^2 - eps*a^2)^2 + 4*a^4.
```

This is probably the single most valuable lemma to make sign-parametric.

### 4. The Pythagorean descent step

From

```text
z^2 = (a^2 - eps*b^2)^2 + (2*b^2)^2,
```

the primitive Pythagorean parametrization gives coprime `m,n` with

```text
b^2 = m*n.
```

Since `m` and `n` are coprime and their product is a square,

```text
m = r'^2,
n = B'^2.
```

The other Pythagorean equation is

```text
a^2 - eps*b^2 = r'^4 - B'^4.
```

Using `b^2 = r'^2*B'^2`, this becomes

```text
a^2 = r'^4 + eps*r'^2*B'^2 - B'^4.
```

That is the same quartic with the same sign.  Thus the descent preserves `eps`.

This part should be 100% shared.

## What does not share cleanly?

### 1. The odd-denominator branch

The parity analysis differs.

For a primitive solution with `B` odd, `r` must be odd.  Then modulo `8`,

```text
r^4 + eps*r^2*B^2 - B^4 ≡ 1 + eps - 1 ≡ eps  (mod 8).
```

So:

```text
eps = +1:  possible;
eps = -1:  impossible, since a square cannot be 7 mod 8.
```

Thus N = 10 has a real odd-`B` branch.  N = 16 does not.

A sign-parametric proof can encode this with a case split on `eps`, but the bodies of the branches will not look identical.

### 2. The even-denominator normalization

For even `B`, primitive parity forces `r` odd.  If `B ≡ 2 mod 4`, then

```text
s^2 ≡ 1 + eps*4  (mod 8) ≡ 5  (mod 8),
```

for both signs, impossible.  Hence

```text
4 ∣ B.
```

This conclusion is shared, but the normalized factors contain `eps`:

```text
U = (r^2 + 2*eps*C^2 - s)/2,
V = (r^2 + 2*eps*C^2 + s)/2,
```

where `B = 2*C`, depending on your file's naming convention.

The proof shape is shared, but Lean may need separate simplification lemmas for `eps = +1` and `eps = -1` to keep `ring_nf`, `omega`, and `norm_num` predictable.

### 3. Positivity side conditions

For `eps = -1`, the Pythagorean leg is

```text
a^2 + b^2,
```

which is automatically positive.

For `eps = +1`, the leg is

```text
a^2 - b^2,
```

so the N = 10 proof likely contains nontrivial ordering lemmas to prove the correct sign or choose the correct orientation.

This is another reason a fully symbolic `eps` proof can become uglier than two specialized front ends.

## Strong induction

The same strong-induction variable works: the positive primitive denominator.

If the original quartic is written as

```text
s^2 = r^4 + eps*r^2*B^2 - B^4,
```

then the descent produces a new primitive solution

```text
s'^2 = r'^4 + eps*r'^2*B'^2 - B'^4
```

with

```text
0 < B' < B.
```

In the even branch, the decrease is even stronger because one first normalizes `B = 2*C` or `B = 4*C`, and the new denominator is bounded by a proper factor coming from `C`.

So there is no need for a lexicographic measure such as `(eps, B)`.  Since `eps` is preserved, ordinary strong induction on `B.natAbs` is enough.

## Recommended Lean architecture

I would not make every theorem take an arbitrary integer parameter `eps : ℤ`.  That tends to make parity proofs and simplification fragile.

Use a tiny sign type instead:

```lean
inductive QuarticSign
  | plus
  | minus

def QuarticSign.eps : QuarticSign → ℤ
  | .plus => 1
  | .minus => -1
```

Then write shared lemmas over `σ : QuarticSign`, but freely use

```lean
cases σ <;> norm_num [QuarticSign.eps]
```

at parity-heavy boundaries.

The best file layout is:

```text
QuarticDescentCore.lean
  Sign type and eps function.
  Signed quartic definition.
  Master identity.
  Shared coprime/fourth-power split wrappers.
  Shared post-factorization identity:
      z^2 = (a^2 - eps*b^2)^2 + 4*b^4.
  Shared Pythagorean descent step.
  Shared strong-induction wrapper parameterized by a sign-specific front-end step.

QuarticDescent.lean
  N = 10 front end.
  Odd-B branch.
  Even-B branch.
  Calls shared core after factorization.

QuarticDescentN16.lean
  N = 16 front end.
  Odd-B contradiction modulo 8.
  Even-B branch.
  Calls shared core after factorization.
```

This gets the main benefits without forcing all parity proofs into a single symbolic proof.

## Is the refactor worth it?

My recommendation:

```text
Do not immediately replace the two working files.
Do extract a shared core if you expect to maintain or modify these descents.
```

Reasons to keep the two files separate for now:

```text
* both are already 0 sorry;
* the total size, 1780 lines, is not outrageous;
* a sign-parametric Lean proof may be harder to debug than two concrete proofs;
* N = 10 has a real odd-denominator branch while N = 16 does not;
* N = 10 has the harder `a^2 - b^2` positivity/orientation bookkeeping.
```

Reasons to refactor into a shared core:

```text
* the Pythagorean descent step is genuinely identical;
* the fourth-power factor split is identical after normalization;
* the strong-induction skeleton is identical;
* future changes to primitive normalization or factorization certificates would otherwise need to be patched twice;
* the sign-parametric theorem documents the mathematical unity of the N = 10 and N = 16 obstructions.
```

So the best compromise is:

```text
Keep the public N = 10 and N = 16 files as separate entry points,
but move the middle 60% of the proof into a shared signed core.
```

That gives you most of the maintainability win while preserving the readability and stability of the completed specialized proofs.
