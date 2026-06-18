# Uniform strategy for the quartic `s⁴ + s²d² - d⁴ = t²`

This is a strategy note, not a Lean coding response.

We want a uniform proof that

\[
s^4+s^2d^2-d^4=t^2,\qquad d\ge 2,\qquad \gcd(s,d)=1
\]

has no solutions.  Dividing by `d^4`, with `r=s/d` and `z=t/d^2`, gives the rational genus-one curve

\[
z^2=r^4+r^2-1.
\]

The primitive integer problem with `d ≥ 2` is therefore the same as proving that the only rational `r` occurring on this quartic are the integral values `r = ±1`, which give the obvious `d=1` solutions.  Under the usual birational map, this is the rank-zero statement for the elliptic curve

\[
E: y^2=x^3+x^2-x
\]

labelled `20.a4`.

## 1. Is there a simpler self-contained proof avoiding Selmer?

I would not expect a purely congruence-based uniform proof.  The fixed-`d` squeeze arguments work because after `d` is fixed one can check a finite interval and then squeeze the large tail.  Uniformly in `d`, a naive squeeze can only handle a region such as `|s|` much larger than roughly `d^2`; it does not dispose of the full two-parameter range.

There is, however, a possible **self-contained infinite descent**, but it is essentially the same mathematics as the 2-isogeny descent written without the words “Selmer group”.  One useful identity is

\[
(2s^2+d^2)^2-(2t)^2=5d^4,
\]

or equivalently

\[
(2s^2+d^2-2t)(2s^2+d^2+2t)=5d^4.
\]

Trying to factor this directly leads to squareclass cases involving `1`, `-1`, `5`, and signs/local conditions.  Those squareclass cases are exactly what the 2-isogeny descent and its dual Selmer computation organize.  One can certainly present the argument as an elementary descent on this factorization or on the quartic model, but the proof will still contain the same ingredients:

* a map from a rational point to a squareclass,
* a proof that the kernel of that map is the image of the isogeny,
* local restrictions cutting the squareclasses down to the computed sets,
* and a dual descent/rank-count argument.

So the honest answer is: a self-contained proof may exist in the sense of “no cohomology vocabulary”, but it will be a hand-unpacked 2-isogeny descent.  It is unlikely to be shorter or easier to formalize than the descent framework you already have, unless the goal is only this single curve and you are willing to hard-code the two explicit descent maps and all squareclass cases.

## 2. Minimal framework needed to turn Selmer sizes into rank zero

You do **not** need the full statement

\[
|\mathrm{Sel}^{\varphi}|=|E'(\mathbb Q)/\varphi E(\mathbb Q)|\cdot |\Sha[\varphi]|.
\]

That statement is the cohomological exact sequence with the Tate–Shafarevich group.  For a rank upper bound, the `Sha` term can be avoided completely.  The only Selmer fact needed is the injection

\[
E'(\mathbb Q)/\varphi E(\mathbb Q)\hookrightarrow \mathrm{Sel}^{\varphi}(E'/\mathbb Q),
\]

and similarly for the dual isogeny.  Equivalently, in a completely explicit formalization, define a descent map into squareclasses and prove:

1. its kernel is exactly the isogeny image;
2. its image is contained in your finite Selmer set.

This gives the cardinality/dimension bound on the quotient without ever defining `Sha`.

The minimal algebraic framework is then the following.

### A. Elliptic curves as abelian groups with a dual 2-isogeny

You need two abelian groups of rational points, say

\[
E(\mathbb Q),\qquad E'(\mathbb Q),
\]

and homomorphisms

\[
\varphi:E(\mathbb Q)\to E'(\mathbb Q),\qquad
\hat\varphi:E'(\mathbb Q)\to E(\mathbb Q)
\]

such that

\[
\hat\varphi\circ\varphi=[2]_E,\qquad
\varphi\circ\hat\varphi=[2]_{E'}.
\]

For this curve, both kernels are rational of order `2`.

### B. Explicit Kummer/descent maps, not abstract cohomology

For each isogeny, define the concrete squareclass map.  In a Lean development this can be a map into a quotient such as `ℚˣ/(ℚˣ)^2`, or into a finite hand-coded set of squareclass representatives if you want to avoid quotient-group infrastructure.

For each map prove:

\[
\ker(\delta_\varphi)=\varphi E(\mathbb Q),
\]

and prove that the image lands in the finite set you computed by local solubility.  Then

\[
\dim_{\mathbb F_2} E'(\mathbb Q)/\varphi E(\mathbb Q)
\le
\dim_{\mathbb F_2}\mathrm{Sel}^{\varphi},
\]

and similarly for the dual.

For your computation,

\[
\mathrm{Sel}^{\varphi}=\{1,-1\},\qquad
\mathrm{Sel}^{\hat\varphi}=\{1,5\},
\]

so both Selmer dimensions are `1`.

### C. A purely group-theoretic dual-isogeny rank lemma

This is the key formal bridge and it does not require Galois cohomology.  For a dual pair of 2-isogenies, there is an exact sequence of finite `𝔽₂`-vector spaces of the form

\[
0\to
E'(\mathbb Q)[\hat\varphi]/\varphi(E(\mathbb Q)[2])
\to
E'(\mathbb Q)/\varphi E(\mathbb Q)
\to
E(\mathbb Q)/2E(\mathbb Q)
\to
E(\mathbb Q)/\hat\varphi E'(\mathbb Q)
\to 0.
\]

For the curve in question, the left-hand kernel term has dimension `1`, and `E(\mathbb Q)[2]` has dimension `1`.  Therefore

\[
\operatorname{rank} E(\mathbb Q)
\le
\dim \mathrm{Sel}^{\varphi}
+
\dim \mathrm{Sel}^{\hat\varphi}
-1-1.
\]

With the computed Selmer sets, this gives

\[
\operatorname{rank} E(\mathbb Q)
\le 1+1-1-1=0.
\]

Since rank is nonnegative, the rank is zero.

### D. Torsion/rational point cleanup

Rank zero alone says every rational point is torsion, once you also use the standard finiteness/rank framework for rational points.  You still need to identify the torsion points on `20.a4` and check that their preimages on the quartic give only the `d=1` primitive solutions.  This part is usually much easier than the descent: it can be done by explicit point computations, reduction modulo good primes, or direct torsion-order checks.

## Practical recommendation for Lean

The shortest realistic Lean path is not to formalize `Sha`.  Instead:

1. Prove a reusable abstract lemma for two abelian groups with dual degree-2 maps whose composites are multiplication by `2`.  The lemma should output the rank bound from the two quotient dimensions and the two kernel dimensions.
2. For this curve only, define explicit descent maps into squareclasses.
3. Prove kernel-is-image for those explicit maps by algebraic manipulation of the curve equations.
4. Prove the image lies in the already-computed finite Selmer sets `{1,-1}` and `{1,5}`.
5. Apply the abstract rank-bound lemma.
6. Enumerate torsion and transfer back through the birational equivalence to the quartic.

This avoids full Galois cohomology and avoids the `Selmer = quotient × Sha` theorem.  It still captures exactly the mathematical content needed to turn your two Selmer computations into `rank = 0`.
