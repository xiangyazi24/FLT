# N13 direct-curve descent: local square-class structure

This note studies the direct curve map

\[
  (x,y)\longmapsto \delta=x-\theta\in
  L^*/L^{*2},\qquad L=\mathbf Q[\theta]/(f),
\]

for the sixteen global `S={2,13}` representatives in
`N13_WEAK_2_DESCENT.md`.  It is deliberately narrower than a fake-Selmer
calculation: it asks whether the stated bad-place and archimedean conditions
can eliminate the sixteen classes *linearly*, without a 16-row proof.

Run the experiment with

```sh
gp -q scratch/n13_local_squareclasses.gp
```

The script reconstructs the field, the units, and the prime generators; it
does not read a saved PARI session.

## Exact arithmetic extracted from the ray characters

Write a candidate as

\[
  z(i,j,k,s)=\zeta^i e_1^j e_2^k(aq)^s,
  \qquad (i,j,k,s)\in\mathbf F_2^4.
\]

The `idealstar(...,2,2)` calculations give the following maps on these
sixteen global classes.  These are exact finite residue/ray-class
calculations in PARI, but still need independent certificates before they
could be used in Lean.

At the two primes above 13, recording valuation parity and the one residual
quadratic character, the restriction is simply

\[
  (i,j,k,s)\longmapsto (s,i,s,i).
\]

Thus the 13-adic restriction has rank two.  In particular it does **not**
see `j` or `k`.

At the unique prime above 2, use the seven characters of the unit quotient
modulo `P2^5` (the quotient stabilizes with seven order-two factors in the
PARI calculation).  In the character basis printed by the script, the four
columns for `zeta,e1,e2,aq` are

\[
\begin{array}{c|rrrr}
 &\zeta&e_1&e_2&aq\\ \hline
 \chi_1&0&1&0&0\\
 \chi_2&0&1&1&1\\
 \chi_3&1&0&1&1\\
 \chi_4&1&0&1&1\\
 \chi_5&1&1&0&0\\
 \chi_6&0&1&1&1\\
 \chi_7&1&0&1&0
\end{array}
\]

The real place has no quadratic squareclass obstruction: the recorded
signature is `[0,3]`, so `L tensor R` is `C^3`, and every nonzero complex
number is a square.

## What the local samples say

The script samples all integral `x mod 2^10` which lift to a point according
to the `2`-adic square test, and also `u/2^m` for odd `u mod 32` and
`1 <= m <= 8`.  Every observed direct-curve image has

\[
  \chi_1=\chi_2=\chi_3=\chi_4=0.
\]

The first three equations are the three coordinates of one intrinsic
`F_8`-valued first ramified logarithm.  The fourth row is independent on the
full local unit quotient but duplicates the third row on these four global
generators.  Consequently the single first-jet equation, rather than four
independent conditions or a representative table, solves to

\[
  i=j=0,\qquad k=s,
\]

so they reduce all sixteen classes at once to exactly

\[
  1 \quad\hbox{and}\quad e_2aq.
\]

This is a substantial structured reduction, not a 16-case argument.  The
second class is not an artefact of omitting nonintegral points: its
2-character is `[0,0,0,0,0,0,1]`, which occurs among the integral samples
(for example `x=4` modulo the tested precision).

At 13 the affine samples include both `(0,0,0,0)` and `(0,1,0,1)` in the
`(valuation,residue,valuation,residue)` basis.  Nonintegral points provide
the common valuation-parity direction, so this is consistent with all four
vectors `(s,i,s,i)`.  Hence 13 supplies no further linear elimination of the
two classes retained at 2.  The real place supplies none.

## Conclusion and proof boundary

The answer to the proposed question is **no** for the three stated local
places alone: they cannot prove that the only direct-curve squareclass is
the trivial one.  A very small 2-adic linear calculation reduces the problem
from 16 to two, but the class `e2*a*q` survives the tested 2-, 13-, and real
conditions.

There is a sharper structural explanation for that survivor.  The exact
unit identity already recorded in `N13_WEAK_2_DESCENT.md` implies

\[
  13=\zeta^2e_1^2e_2a^3q,
  \qquad\text{hence}\qquad
  e_2aq=13\,(\zeta e_1a)^{-2}.
\]

Thus the sole survivor is exactly the **rational scalar squareclass**
`[13]`.  The GP script now checks the polynomial equality
`(e2*a*q)*(zeta*e1*a)^2 = 13` exactly in `L`.

This also explains why searching for one more local obstruction is the wrong
goal.  For a monic even-degree model, points sufficiently near either
rational infinity have

\[
 x-\theta=x(1-\theta/x),\qquad
 y^2=x^6(1+4/x+6/x^2+\cdots).
\]

After making `x` sufficiently large in a local field, both parenthesized
units are squares (by the elementary Hensel square criterion).  Multiplying
`x` by a large local square does not change its local squareclass.  Therefore
every rational scalar class, including `[13]`, occurs in the direct local
image near infinity at every place.  In particular no additional odd-prime,
2-adic, or real condition on the direct local image can eliminate this
survivor.

For the usual **fake Jacobian descent**, whose target quotients by rational
scalars, `[13]` is already trivial.  Hence the same computation says that
the 16 global candidates become one class in the quotient by `Q^*`; it is
not a nontrivial fake-Selmer obstruction.  For the literal point map
`P -> x(P)-theta` without that quotient, `[13]` is an unavoidable scalar
ambiguity and must not be treated as a remaining geometric class.

What is proved here:

* the algebraic form of the global restriction matrices, conditional on the
  PARI integral-basis/prime-generator data already documented in
  `N13_WEAK_2_DESCENT.md`;
* the archimedean observation `C^3/(C^3)^2=0`.

What remains experimental:

* that the sampled 2-adic images exhaust `C(Q_2)`;
* that the `P2^5` character quotient is exactly the local squareclass
  quotient in the required normalization;
* the generic near-infinity local argument, although it is a short Hensel
  lemma rather than a large certificate.

To turn the structured reduction into a theorem, the right next lemma is a
local image containment:

\[
  \delta(C(\mathbf Q_2))\subseteq
  \ker(\chi_1,\chi_2,\chi_3,\chi_4).
\]

It should be proved by the two valuation regimes `v2(x)>=0` and `v2(x)<0`,
then a short residue calculation/Hensel argument.  It is a single local
lemma, not an enumeration of the 16 global squareclasses.  The final
interpretation is then the scalar quotient above, not an attempted local
elimination of `e2*a*q`.
