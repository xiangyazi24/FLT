# Denominator step for `y² = x³ + x² - x`

This is a mathematical strategy note, not a Lean proof.

You have reached the following situation.  From the first 2-isogeny descent you know that, for a rational point with `x ≠ 0`, the `x`-coordinate has squareclass `1`, so

\[
x = \pm u^2,\qquad u\in \mathbb Q.
\]

For the positive square branch, write

\[
x=(p/q)^2,\qquad \gcd(p,q)=1,\qquad q\ge 2.
\]

After denominator/valuation cleanup, the equation becomes

\[
s^2=p^4+p^2q^2-q^4. \tag{1}
\]

The question is whether `(1)` has a uniform elementary contradiction for `q≥2`, or whether one needs the dual descent.

## 1. The equation is exactly the rational quartic again

Equation `(1)` is equivalent to

\[
(s/q^2)^2=(p/q)^4+(p/q)^2-1.
\]

So it is not merely a denominator side condition; it is the rational-point problem on the genus-one quartic

\[
C: V^2=U^4+U^2-1.
\]

Thus proving that `(1)` has no primitive solution with `q≥2` is essentially proving that all rational `U` on `C` are integral, hence proving the rank-zero/rational-point result for the associated elliptic curve.  In other words, this denominator lemma is not a harmless valuation lemma; it is almost the whole arithmetic content.

This also explains why the prime-divisor trick that works for the `d`-cover

\[
dv^2=d^2u^4+du^2-1
\]

does not apply here.  In `(1)`, reducing modulo a prime `ℓ | q` gives

\[
s^2\equiv p^4\pmod ℓ,
\]

which is perfectly consistent because `ℓ ∤ p`.  There is no local contradiction at primes dividing `q`.

## 2. A direct modular proof is unlikely

Modulo a prime divisor `ℓ | q`, the equation says only that `s ≡ ±p² mod ℓ`.  For prime powers, and especially for composite `q`, the signs can vary independently over the prime-power factors of `q`.  Tracking those signs is exactly the squareclass bookkeeping of a 2-descent.

Some congruences do eliminate special cases:

* if `q` is odd and `p` is even, then modulo `8` the right side is `7`, impossible;
* if `v₂(q)=1`, then modulo `16` one also gets a contradiction;
* many fixed small `q` can be eliminated by squeeze arguments.

But these do not give a uniform proof for all `q≥2`.  The surviving cases include, for example, `q` odd with `p` odd, or `4 | q` with `p` odd.  In those cases the elementary congruences are compatible with being a square.

## 3. The useful factorization and why it becomes descent

There is a promising factorization:

\[
(2p^2+q^2)^2-(2s)^2=5q^4,
\]

so

\[
(2p^2+q^2-2s)(2p^2+q^2+2s)=5q^4. \tag{2}
\]

Both factors are positive, since `(2p²+q²)^2 - 4s² = 5q^4 > 0`.

This factorization is the right starting point for an elementary infinite descent.  However, it is not a one-line divisibility argument.  One has to analyze the gcd of the two factors, distribute the prime-power factors of `q⁴` between them, and track a possible factor of `5`.  For each prime `ℓ | q`, the congruence `s² ≡ p⁴ mod ℓ` determines whether `ℓ` divides the left factor or the right factor, but the choice may differ from prime to prime.  That distribution is precisely a squareclass/Selmer datum.

So an elementary proof from `(2)` is possible in principle, but it will be a hand-unrolled 2-descent.  It will have the same core data as the isogeny descent:

1. attach a squareclass to a rational point;
2. prove the kernel is the image of the isogeny;
3. prove local conditions restrict the squareclass to a tiny finite set;
4. use the dual isogeny or a descent recurrence to rule out the remaining denominator possibilities.

## 4. There is a classical-theorem route, but it is not easier in Lean

The primitive equation

\[
s^2=p^4+p^2q^2-q^4,\qquad \gcd(p,q)=1
\]

is a known genus-one/quartic Diophantine equation, closely related to classical Ljunggren-type quartic equations.  One could quote a theorem classifying primitive solutions to

\[
X^4+X^2Y^2-Y^4=Z^2.
\]

Such a theorem would imply that the only primitive solutions have `|q|=1` in the branch relevant here.

But formalizing that theorem from scratch is not obviously easier than formalizing the 2-isogeny descent.  It would still require a nontrivial infinite descent, often via factorization in a quadratic order or equivalent Pell-type arguments.

## 5. Why the dual descent is probably the right next step

The first descent map tells you that the `x`-coordinate has squareclass `1`, i.e. `x = ±u²`.  That is not enough to control the denominator of `u`.

The denominator obstruction is exactly the kind of information supplied by the **dual isogeny descent**.  The dual descent map measures a different squareclass.  Once you know

\[
\mathrm{Sel}^{\hat\varphi}=\{1,5\},
\]

then a rational point whose denominator contains a prime should produce a dual-cover squareclass outside `{1,5}`, or force a locally impossible homogeneous space.  This is the clean conceptual explanation for why `q≥2` should be impossible.

In other words, the denominator step is not independent of the dual descent; it is one of the places where the dual descent is doing real work.

## 6. Minimal Lean framework I would aim for

I would not try to prove the denominator lemma by ad hoc modular/squeeze arguments for all `q`.  Instead, I would formalize one of the following two routes.

### Route A: explicit dual descent, no full cohomology

This is probably the best Lean path.

Define the two explicit descent maps for the 2-isogeny pair attached to

\[
E: y^2=x^3+x^2-x.
\]

Do not define `Sha`.  Do not build full Galois cohomology.  Instead prove directly:

* the descent map lands in `ℚˣ/(ℚˣ)^2`, or in a hand-coded finite squareclass set;
* the kernel is the image of the relevant isogeny;
* the local solubility tests restrict the image to the computed Selmer set;
* the two Selmer dimensions give the rank bound by a purely group-theoretic dual-isogeny lemma.

For the denominator step specifically, you can then state a corollary: if `x=(p/q)^2` in lowest terms and `q≥2`, then the corresponding dual descent squareclass violates the computed dual Selmer condition.

### Route B: elementary infinite descent from `(2)`

This avoids elliptic-curve vocabulary but not the mathematics.  One would prove a theorem like:

> If `gcd(p,q)=1` and `s²=p⁴+p²q²-q⁴`, then `|q|=1`.

The proof would start from

\[
(2p^2+q^2-2s)(2p^2+q^2+2s)=5q^4
\]

and then perform a squareclass factor split.  If `|q|>1`, the split should construct a smaller primitive solution, contradicting minimality of `|q|`.  This is likely viable, but it is essentially the same descent proof hidden inside a more elementary presentation.

## Bottom line

I do not think there is a short uniform denominator proof by congruences or simple divisibility.  The equation

\[
s^2=p^4+p^2q^2-q^4
\]

is the rational quartic itself, so proving `q=1` is essentially equivalent to proving the rank-zero/rational-point classification for `20.a4`.

For Lean, the most economical honest path is the explicit dual-isogeny descent, avoiding `Sha` and full cohomology.  The direct elementary alternative would be an infinite descent from the factorization `(2)`, but it will reproduce the same squareclass bookkeeping and may be harder to maintain than the descent framework already in progress.
