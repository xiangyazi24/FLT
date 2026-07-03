# Q3162 (dm1): Review of `paper/paper2_counterexample/paper2.tex`

Date: 2026-07-03

Repository reviewed: `xiangyazi24/Q-series-and-Chan-s-work`

File reviewed: `paper/paper2_counterexample/paper2.tex` on `main`

## Overall verdict

The paper has a strong and interesting algebraic core, but in its current form I would treat it as **major revision before submission**.

The strongest parts are:

1. the explicit `beta(k,r)` parametrization of the coset `L`;
2. the norm identity `-N(beta(k,r)) = 10E(k,r)+1`;
3. the identification with the Hickerson--Mortenson double sum, provided the sign convention is stated precisely;
4. the concrete non-multiplicativity witness `a(11*31) != a(11)a(31)`.

The weakest parts are:

1. the proof of the stabilizer/order theorem, which currently has a genuine arithmetic error modulo `sqrt(5)`;
2. the prime nonvanishing proof, where the “bad class” theorem is asserted but not proved;
3. the reflection/sector machinery, which is plausible but underdefined;
4. the equidistribution proof, where “by Chebotarev” is not justified unless the `iota` invariant is first shown to factor through a finite ray class or an appropriate Hecke/Shintani equidistribution theorem is invoked.

My current recommendation is: submit only after replacing the prime-value and equidistribution section with a fully explicit sector-table theorem.  The algebraic non-multiplicativity result alone may already be publishable as a shorter note, but the present headline claims about all split primes and density need more proof.

## A. Mathematical correctness audit

### 1. Definition of `E`: nonnegativity is false globally

The draft says that

```text
E(k,r) = 1/2 Q(k,r)
```

is “always a nonnegative integer.”  The integrality is correct, but global nonnegativity is false because the form is indefinite off the same-sign cones.

Example:

```text
E(1,-2) = 2*1^2 + 1 + 3*1*(-2) + (-2)(-1)/2
        = 2 + 1 - 6 + 1
        = -2.
```

Fix:

```text
E(k,r) is always an integer.  On the A- and D-cones used in the definition of B_N, it is nonnegative.
```

This matters because a referee will object to the phrase “always nonnegative” immediately.

### 2. Unit stabilizer theorem: the proof has a real modulo-`sqrt(5)` error

The theorem statement

```text
Stab_{<eps>}(L) = <eps^6>
```

is plausible and consistent with the prior computations, but the proof in the draft is wrong as written.

The draft claims:

```text
eps = phi^2 has eps mod sqrt(5) = 1 + sqrt(5) ≡ 1.
```

This is incorrect.  Since

```text
phi = (1 + sqrt(5))/2,
eps = phi^2 = phi + 1 = (3 + sqrt(5))/2,
```

and modulo `(sqrt(5))` we have `phi ≡ 1/2 ≡ 3 mod 5`, so

```text
eps = phi^2 ≡ 3^2 ≡ 9 ≡ 4 ≡ -1 mod 5.
```

Thus `eps` has order `2` modulo `(sqrt(5))`, not order `1`.

There is also a second issue.  The draft factors the `L` condition modulo `sqrt(5)` as

```text
-2a ≡ 1 mod 5, i.e. a ≡ 2 mod 5.
```

That is not the clean way to express the coset.  The condition

```text
b - 3a ≡ 1 mod 5
```

combined with `phi ≡ 3 mod sqrt(5)` gives

```text
alpha = a + b phi ≡ a + 3b ≡ a + 3(3a+1) = 10a + 3 ≡ 3 mod 5.
```

So the `sqrt(5)` component of `L` is better written as

```text
alpha ≡ 3 mod sqrt(5).
```

Multiplication by `eps ≡ -1` sends this to `-3 ≡ 2`, so it preserves the `sqrt(5)` condition only for even powers of `eps`.

The corrected CRT proof should be:

```text
O_K/(2 sqrt(5)) ≅ O_K/(2) × O_K/(sqrt(5)) ≅ F_4 × F_5.

L modulo 2: alpha mod 2 lies in {1, phi}, excluding eps = phi+1.
L modulo sqrt(5): alpha ≡ 3 mod sqrt(5).

eps mod 2 has order 3.
eps mod sqrt(5) is -1 and has order 2.

Therefore eps^j preserves L only if j ≡ 0 mod 3 and j ≡ 0 mod 2, i.e. 6 | j.
```

This also fixes the apparent inconsistency in the current proof: the draft says the mod-`sqrt(5)` condition is preserved for all `j`, but still concludes `6 | j`.  If it were preserved for all `j`, the conclusion would only be `3 | j`.

### 3. `eps*L ∩ L = empty` is correct, but do not overstate disjointness for all smaller powers

The theorem

```text
eps L ∩ L = empty
```

is correct.

However, be careful not to imply that all `eps^j L` for `1 <= j <= 5` are disjoint from `L`.  In earlier computations, `eps^2 L ∩ L` and `eps^4 L ∩ L` are nonempty.  For example,

```text
x = 1 + 4 phi ∈ L,
eps^2 x = 14 + 23 phi ∈ L.
```

So the precise statement should be about the stabilizer:

```text
eps^j L = L iff 6 | j.
```

and not about pairwise disjointness of the six translates.

### 4. The non-multiplicativity witness is solid, but the “character” corollary is too vague

The direct witness

```text
a(11)=B_1=1,
a(31)=B_3=-2,
a(341)=B_34=3
```

is a good theorem.  It proves non-multiplicativity cleanly.

The corollary saying

```text
chi_fin(eps) != 1, in fact chi(eps) is a primitive 6th root
```

needs a definition of `chi_fin` and a precise domain.  At present it reads as heuristic explanation, not a theorem.

Suggested fix:

- Keep the non-multiplicativity witness as the theorem.
- Replace the character statement with a remark unless `chi_fin` is explicitly defined as a finite ray/coset character on a quotient and its value on `eps` is proved.

A cautious wording:

```text
The failure of eps to stabilize L prevents the coefficient sum from descending to an ideal-level sum invariant under the full positive unit group.  This is the structural source of non-multiplicativity.
```

### 5. HM identification is likely correct, but should be stated as a theorem with the convention

The statement

```text
B(X) = -f_{1,3,4}(X,-X^3,X)
```

is likely correct under the standard Hickerson--Mortenson convention

```text
f_{a,b,c}(x,y,q)
= sum_{sg(r)=sg(s)} sg(r)(-1)^{r+s} x^r y^s
  q^{a binom(r,2)+brs+c binom(s,2)}.
```

But a referee will want the convention printed and the one-line exponent/sign check included.  The paper currently says it coincides with HM but does not prove it in the main text.

Recommended insertion:

```text
With HM variables (r,s)=(r,k), substituting x=X, y=-X^3, q=X gives sign
sg(r)(-1)^r and exponent
r(r+1)/2 + 3rk + 2k^2 + k = E(k,r).
Thus f_{1,3,4}(X,-X^3,X)=A(X)-D(X), hence B=D-A=-f.
```

### 6. Shintani fundamental sector statement needs more precision

The proposition that A is an exact fundamental domain for `<eps>` acting on

```text
Q = {sigma_1(alpha)>0, sigma_2(alpha)<0}
```

is plausible, but it needs a fully specified embedding convention and boundary convention.

Questions a referee will ask:

1. Are the boundary rays included on one side and excluded on the other?
2. How is `delta` defined on a boundary?
3. Are prime generators ever on a boundary?  If not, prove or state why.  Boundary norms may be exceptional and should be excluded explicitly.
4. Does the D-cone use the same `delta` after negation, or is it a separate sector in `-Q`?

The paper says “A-cone or D-cone is equivalent to delta=0.”  That needs a lemma.  For A it is direct; for D it is true only after clarifying whether `delta(alpha)` is sign-invariant or whether one applies `delta(-alpha)`.

### 7. Reflection identity: plausible but currently underproved

The reflection identity

```text
iota(bar p) ≡ -iota(p) - 1 mod 3
```

has the right shape.  The finite-field part is correct if `lambda` is the discrete logarithm to base `eps mod 2`:

```text
conjugation in F_4 is Frobenius x -> x^2,
lambda -> 2 lambda mod 3.
```

Indeed, in characteristic 2,

```text
bar(phi) = 1 - phi = 1 + phi = phi^2,
```

so the Frobenius statement is right.

The archimedean part is the part that needs proof.  The draft asserts:

```text
delta(bar pi) = -delta(pi) - 1 mod 6.
```

This is an off-by-one-sensitive floor-function statement.  It should be isolated as a lemma with exact interval conventions.  A safe version is:

```text
If R lies in [eps^j, eps^{j+1}) in log-ratio coordinates, then 1/R lies in
(eps^{-j-1}, eps^{-j}] and therefore has sector index -j-1, after the chosen
half-open boundary convention.
```

Then state that boundary cases do not occur for primes `p ≡ 1 mod 10`, or handle them separately.

Without this lemma, Theorem 4.7 is not referee-ready.

### 8. The bad class theorem is currently unproved

The paper states:

```text
An ideal p contributes an atom iff iota(p) != 2.
```

but the following proof block is labelled as the proof of the prime nonvanishing theorem, not as a proof of the bad class theorem.  As written, the bad class theorem has no proof.

More importantly, the bad class criterion suppresses several necessary lemmas:

1. **Sign modulo `sqrt(5)` lemma.**  L-membership is not only the mod-2 condition `lambda in {0,2}`.  It also includes the condition `alpha ≡ 3 mod sqrt(5)`.  Since replacing a generator by `-alpha` flips `3` and `2` modulo `sqrt(5)` while preserving `lambda` and `delta`, one can probably choose the sign appropriately for prime norms, but this must be stated and proved.

2. **Atom-sector lemma.**  For an element in `L`, being in the A- or D-cone must be shown equivalent to the correct sector condition, likely `delta=0` after a sign convention.

3. **Unique representative lemma.**  For a contributing ideal at prime norm, there is exactly one active element in the relevant unit orbit modulo `<eps^6>`.  The draft later says “each contributing ideal contributes exactly one atom,” but does not prove it.

4. **Parity coherence lemma.**  If both conjugate ideals contribute, their active atoms must have the same sign.  This is asserted, not proved.

The bad class theorem is the center of the paper.  It needs a full proof or at least a clearly stated finite table with all cases.

### 9. Prime nonvanishing logic: existence is not enough for the value set

The reflection identity plus bad class logic can prove that at least one of the two conjugate prime ideals contributes.  But to conclude

```text
B_{(p-1)/10} in {-2,-1,+1,+2}
```

you also need:

```text
at most one atom per contributing ideal;
no additional unit translates in the A/D cone;
if both ideals contribute, the two atom weights do not cancel.
```

These are currently summarized in one sentence as “bounded multiplicity from the cone-sector structure” and “coherent parity.”  A referee will not accept that as proof.

This is the single biggest mathematical gap in the paper.

### 10. Equidistribution proof is not justified by Chebotarev as written

The equidistribution proof says that `iota(p)` has density `1/3` by Chebotarev.

This needs much more justification.

The invariant

```text
iota = delta - lambda
```

contains `delta`, a Shintani sector/floor-function invariant defined using real embeddings.  Chebotarev directly applies to finite Galois/ray-class data, not to an archimedean sector index unless you first prove that `iota` factors through a finite ray class group.

There are two possible routes:

1. **Finite ray-class route.**  Prove that `iota` is actually a finite ray-class invariant modulo a stated modulus.  Then Chebotarev is appropriate.

2. **Shintani/Hecke equidistribution route.**  Treat `delta` as an archimedean sector condition and invoke equidistribution of prime ideals in Shintani sectors.  This is not plain Chebotarev; it is a Hecke prime ideal equidistribution statement for real quadratic fields with a finite congruence condition.

As written, the density theorem is not proved.

## B. What a referee would flag

A referee would likely flag the following points.

### Major flags

1. **False statement:** `E(k,r)` is not globally nonnegative.
2. **Incorrect arithmetic in the stabilizer proof:** `eps mod sqrt(5)` is `-1`, not `1`.
3. **Incorrect or unclear factorization of the coset condition modulo `sqrt(5)`.**  The clean condition is `alpha ≡ 3 mod sqrt(5)`, not `a ≡ 2 mod 5`.
4. **Theorem “Bad class” has no proof.**
5. **Prime nonvanishing proof relies on unproved bounded multiplicity and parity coherence.**
6. **Equidistribution by Chebotarev is unsupported unless `iota` is finite ray-class data.**
7. **Claims of novelty/firstness are too strong without a careful literature comparison.**
8. **The Lean formalization claim needs exact scope.**  The abstract says “All algebraic results (Theorems 1--9) are formalized.”  If prime nonvanishing and equidistribution are not formalized, make sure theorem numbering does not imply they are.

### Minor flags

1. The bibliography entry labelled `Chan2005` gives a 2010 publication; check label and title against the actual source for Chan's `Theta_10` dissection.
2. The phrase `chi(eps)=zeta_6` is not meaningful until `chi` is defined.
3. The theorem environments are awkward: the prime theorem is stated in the introduction and then later a proof appears without a restated theorem.  It is better to restate the theorem in Section 4.
4. Boundary conventions for Shintani sectors are missing.
5. The numerical evidence says “split primes through N=10^5” and “p up to 10^6+1”; make the indexing consistent.

## C. Does it distinguish itself from ADH/Cohen/Corson--Favero?

Conceptually, yes, but the paper needs to be more precise.

The promising distinction is:

```text
ADH/Cohen/Corson--Favero examples produce norm-supported series whose coefficients descend to ideal-level sums with unit-invariant weights, leading to multiplicative or Hecke-theoretic coefficient structures.

This example is norm-supported but does not descend to ideals because the defining coset is not stable under eps.  The coefficient sum remains element-level/Shintani-sector-level and is therefore non-multiplicative.
```

That is a strong story.

But I would soften claims like:

```text
first naturally occurring ...
all previously known examples ...
```

until the literature review is expanded.  A safer wording is:

```text
This appears to give a new type of ADH-style norm-supported kernel: it is naturally produced by a q-series dissection and has norm support, but the unit action prevents descent to a multiplicative ideal-sum.
```

Suggested additional comparison points:

1. ADH `sigma(q)` and Cohen's Maass waveform examples: emphasize multiplicative ideal-sum behavior.
2. Corson--Favero--Liesinger--Zubairy: emphasize character/q-series in `Q(sqrt(2))` and unit-compatible characters.
3. Bringmann--Kane and Lovejoy--Osburn real-quadratic double sums: check whether any examples are nonmultiplicative in the same coset/Shintani-window sense.
4. Hickerson--Mortenson: position your `f_{1,3,4}` identification in the Hecke-type double-sum framework.

## D. Strongest and weakest parts

### Strongest part

The strongest part is the algebraic construction:

```text
beta(k,r) maps Z^2 to L,
-N(beta(k,r)) = 10E(k,r)+1,
B is a cone-difference over A and D,
B = -f_{1,3,4}(X,-X^3,X),
B is not multiplicative by an explicit coefficient witness.
```

This is concrete, checkable, and compelling.  It also has Lean support, which is valuable.

### Weakest part

The weakest part is the prime-value theorem and density theorem.  The paper currently gives the outline of a beautiful argument, but the finite sector table has not actually been written down or proved.

The central missing theorem should look like this:

```text
Finite sector theorem.
For each split prime ideal orbit, after reducing by <eps^6>, the active set
L ∩ (A ∪ D) has either zero or one representative; the zero/one condition is
controlled by iota != 2; and for the two conjugate ideals, contributing
representatives have coherent weights.
```

Once that theorem is proved, the prime nonvanishing and value set follow.

Until then, the paper should not present prime nonvanishing and equidistribution as established theorems.

## E. Venue suggestion

### If the prime theorem and density are fully proved

Good targets:

```text
The Ramanuan Journal
Research in Number Theory
Journal of Number Theory
```

`The Ramanujan Journal` is probably the best thematic fit because the paper combines q-series, mock/false theta, and real quadratic arithmetic.

`Research in Number Theory` is a good fit if the Lean formalization and arithmetic novelty are emphasized.

`Journal of Number Theory` becomes realistic if the Shintani sector theorem and literature comparison are strengthened.

### If the paper is shortened to the algebraic/nonmultiplicative construction only

Good targets:

```text
Integers
Hardy-Ramanujan Journal
Journal of Integer Sequences
```

`Integers` or `Hardy-Ramanujan Journal` would be reasonable for a concise paper presenting a new q-series kernel, norm support, HM identification, numerical data, and a nonmultiplicativity witness.

## Suggested revision plan

### Revision 1: fix arithmetic and wording

1. Change “`E` is always nonnegative” to “`E` is always integral, and is nonnegative on the A/D cones.”
2. Correct the stabilizer proof:
   ```text
   L mod sqrt(5): alpha ≡ 3;
   eps mod sqrt(5): -1;
   eps mod 2: order 3;
   hence eps^j L = L iff 6 | j.
   ```
3. Define `chi_fin` or remove the primitive-sixth-root statement.
4. Add the HM convention and proof.
5. Clarify which results are actually Lean formalized.

### Revision 2: replace the prime section with explicit lemmas

Add lemmas:

1. `delta` is well-defined with half-open sectors.
2. Boundary cases do not occur for primes `p ≡ 1 mod 10`.
3. `lambda(bar alpha)=2lambda(alpha)`.
4. `delta(bar alpha)=-delta(alpha)-1`.
5. L-membership includes both the mod-2 and mod-`sqrt(5)` conditions, and the sign choice handles the latter.
6. Atom iff `iota != 2`, with a proof.
7. Each contributing prime ideal gives exactly one active atom.
8. The two conjugate contributing atoms, when both exist, have coherent parity/weight.

### Revision 3: justify density

Either prove that `iota` factors through a finite ray class group and use Chebotarev, or replace “Chebotarev” with the appropriate Hecke/Shintani prime-equidistribution theorem.

The current one-line density proof is not enough.

## Bottom line

I would frame the current draft as follows:

```text
The algebraic core and nonmultiplicativity result are strong and close to paper-ready.
The prime nonvanishing/equidistribution section is promising but not yet rigorous.
The stabilizer proof contains a concrete modulo-sqrt(5) error that must be fixed.
The reflection identity is plausible; the finite-field half is correct, but the floor/sector half needs a precise lemma.
The bad-class and prime-value claims need an explicit sector-table proof.
```

With those fixes, the paper could become a strong short note, especially if it presents the finite sector table cleanly and distinguishes “norm-supported but nonmultiplicative” from the classical ADH/Cohen/Corson--Favero paradigm.
