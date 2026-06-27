# Q1181 (dm2): worldwide status of Mazur torsion theorem formalization

## Bottom line

As of **27 June 2026**, I found **no public, completed formalization** in Lean, Coq/Rocq, Isabelle/HOL, Agda, Mizar, HOL Light, or another mainstream proof assistant of any of the following:

1. the full Mazur torsion classification

   ```text
   E(Q)_tors ≅ Z/nZ for n = 1..10,12
   or
   E(Q)_tors ≅ Z/2Z × Z/2nZ for n = 1..4;
   ```

2. the prime-level corollary

   ```text
   no elliptic curve over Q has a rational point of prime order p >= 11;
   ```

3. even the weaker uniform statement

   ```text
   no rational point of prime order p >= 13;
   ```

4. a proof-assistant formalization of modular curves `X_1(N)` as algebraic curves with genus computation and rational-point classification sufficient for Mazur;

5. Merel's uniform boundedness theorem.

This is necessarily a public-evidence statement, not a proof of nonexistence.  I checked the usual public signals: web-indexed project names, arXiv formalization papers, Mathlib documentation, and obvious exact theorem-name searches.  I did not find a reusable formal theorem that FLT can import for Mazur torsion.

So for the FLT repo, the practical conclusion is:

```text
Do not plan on importing Mazur's theorem or Merel's theorem.
Treat Mazur-prime as a genuine new formalization target or an explicit temporary axiom.
```

The best axiom boundary remains the one from the earlier A-Line plan:

```lean
import Mathlib

namespace FLT

/-- Placeholder for the actual rational point type used by FLT. -/
axiom HasRationalPointOfOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop

/--
Prime-level Mazur core.
Mathematical content: `X_1(p)(Q)` has no noncuspidal rational points for prime
`p >= 11`.
-/
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E p

end FLT
```

Then derive broad no-large-order results from this axiom plus finite composite exclusions, rather than axiomatizing all of Mazur.

---

## Direct answers to the four questions

### 1. Full Mazur torsion classification

I found no public proof-assistant formalization of the full classification:

```text
E(Q)_tors is one of:
  Z/nZ,        n = 1,2,3,4,5,6,7,8,9,10,12,
  Z/2Z × Z/2nZ, n = 1,2,3,4.
```

There are related Lean developments for elliptic curves, division polynomials, explicit Mordell-curve computations, cyclotomic number theory, and modular forms, but not the classification theorem.

In particular, Mathlib has a `WeierstrassCurve` API and division-polynomial API.  The Mathlib documentation describes `WeierstrassCurve`, `WeierstrassCurve.Δ`, `WeierstrassCurve.twoTorsionPolynomial`, and `WeierstrassCurve.IsElliptic`, and says this file models Weierstrass curves over commutative rings.  It also has division polynomials `preΨ`, `Ψ`, `Φ`, `ψ`, and `φ`, with recurrence and base-change lemmas.  This is useful groundwork, but it is not Mazur's theorem.

Relevant docs checked:

```text
https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.html
https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html
```

### 2. No rational point of prime order `p >= 11` or `p >= 13`

I found no public formalization of this theorem either.

This theorem is not a small corollary of existing formal group theory.  Mathematically it is the prime-level modular-curve part of Mazur's theorem:

```text
(E, P with P of order p over Q)
  <-> noncuspidal rational point of X_1(p)
```

and the theorem says that such noncuspidal rational points do not exist for prime `p >= 11`.

For `p = 11`, there are classical explicit genus-one computations of `X_1(11)(Q)`, but I found no public proof-assistant formalization of that computation as a theorem about rational torsion.

For `p = 13`, one needs a genus-two rational-points computation for `X_1(13)`.  Again, I found no public proof-assistant formalization of the theorem in a reusable form.

So the best FLT split is still:

```lean
import Mathlib

namespace FLT

axiom HasRationalPointOfOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop

/-- Temporary hard axiom.  Later replace by modular-curve proof. -/
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E p

end FLT
```

or, if the repo later proves the fixed small prime cases explicitly:

```lean
import Mathlib

namespace FLT

axiom HasRationalPointOfOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop

-- Prove these later from explicit `X_1(11)` and `X_1(13)` certificates.
axiom no_point_of_order_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 11

axiom no_point_of_order_13
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 13

-- Keep only the genuinely uniform prime Mazur core.
axiom no_point_of_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp17 : 17 ≤ p) :
    ¬ HasRationalPointOfOrder E p

end FLT
```

### 3. Modular curves `X_1(N)` with genus computation

I found no public formalization of the modular curves `X_1(N)` as algebraic curves with enough structure to run Mazur's proof:

```text
moduli interpretation,
compactification/cusps,
genus computation,
Jacobian or rational-point computation,
noncuspidal-rational-point exclusion.
```

Mathlib does have substantial analytic modular-form infrastructure.  The public docs show a directory

```text
Mathlib/NumberTheory/ModularForms
```

with files/folders such as:

```text
ArithmeticSubgroups.lean
Basic.lean
BoundedAtCusp.lean
CongruenceSubgroups.lean
CuspFormSubmodule.lean
Cusps.lean
DimensionFormulas
EisensteinSeries
LevelOne
QExpansion.lean
SlashActions.lean
SlashInvariantForms.lean
```

and `Mathlib.NumberTheory.ModularForms.Basic` defines `ModularForm` and `CuspForm` as bundled functions on the upper half-plane satisfying slash-invariance, holomorphicity, and boundedness/vanishing at cusps.

Relevant docs checked:

```text
https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/NumberTheory/ModularForms
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/Basic.html
```

This is important infrastructure, but it is **not** the same thing as algebraic modular curves `X_1(N)` with rational points and genus computations.  The gap from current modular-forms infrastructure to Mazur is still very large.

### 4. Merel's uniform boundedness theorem

I found no proof-assistant formalization of Merel's theorem.

Merel is not a shortcut for FLT anyway.  It is much deeper than the specific `Q`-torsion classification, and its proof also uses modular curves/arithmetic geometry.  Even if a non-sharp Merel-style bound existed, it would not immediately give the exact Mazur list or the prime-order cutoff `p >= 11` without additional computations.

So Merel should not be the dependency target for FLT.

---

## Closest related formalizations

### Lean: FLT for regular primes

There is a complete Lean 4 formalization of Fermat's Last Theorem for regular primes:

```text
Riccardo Brasca, Christopher Birkbeck, Eric Rodriguez Boidi,
Alex Best, Ruben van De Velde, Andrew Yang,
"A complete formalization of Fermat's Last Theorem for regular primes in Lean".
```

The arXiv abstract states that it formalizes a complete proof of the regular case of FLT in Lean 4 and includes Kummer's lemma.  The paper explicitly says the full Wiles proof is still a work in progress and likely to take several years.  It also notes that the regular-prime proof was chosen because it is amenable to existing Mathlib infrastructure.

Source checked:

```text
https://arxiv.org/abs/2410.01466
```

This is the closest high-level number-theory formalization, but it does not contain Mazur's torsion theorem.

### Lean: explicit class group computations and Mordell elliptic curves

There is a Lean 3 formalization of class group computations and integral points on certain Mordell elliptic curves:

```text
Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen,
"Formalized Class Group Computations and Integral Points on Mordell Elliptic Curves".
```

The abstract says it formalizes the resolution of Mordell equations `y^2 = x^3 + d` for several negative `d`, using descent and class groups, and formalizes supporting number-theory infrastructure such as ideal norms, quadratic fields/rings, and explicit class-number computations.

Source checked:

```text
https://arxiv.org/abs/2209.15492
```

This is relevant to the FLT repo's fixed-level descent/certificate strategy.  It is not a uniform Mazur theorem.

### Lean: Weierstrass elliptic-curve group law

There is a Lean formalization of the group law on Weierstrass elliptic curves in any characteristic:

```text
David Kurniadi Angdinata, Junyan Xu,
"An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves in any Characteristic".
```

The abstract says it formalizes nonsingular points of a Weierstrass curve over a field of any characteristic and a purely algebraic proof that they form an abelian group.

Source checked:

```text
https://arxiv.org/abs/2302.10640
```

This is foundational for torsion statements, but far below Mazur.

### Lean: Mathlib schemes

Mathlib has a schemes library.  The docs define `AlgebraicGeometry.Scheme` as a locally ringed space locally isomorphic to affine schemes `Spec R`, and provide morphisms, `Spec`, basic opens, zero loci, and related scheme infrastructure.

Source checked:

```text
https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Scheme.html
```

This is useful background for eventual modular-curve formalization, but it is not yet a modular-curve/rational-points library.

### Lean: modular forms

Mathlib has analytic modular forms and cusp forms on the upper half-plane, arithmetic/congruence subgroups, cusps, boundedness at cusps, q-expansions, Eisenstein series, and dimension-formula folders.

Sources checked:

```text
https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/NumberTheory/ModularForms
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/Basic.html
```

This is the closest imported infrastructure on the modular side.  It does not give `X_1(N)(Q)` or Mazur.

### Coq/Rocq and Isabelle: Fermat small cases, Mason-Stothers

There are older formalizations of Fermat's Last Theorem for small exponents and related elementary Diophantine results, for example:

```text
David Delahaye, Micaela Mayero,
"Diophantus' 20th Problem and Fermat's Last Theorem for n=4:
Formalization of Fermat's Proofs in the Coq Proof Assistant".
```

Source checked:

```text
https://arxiv.org/abs/cs/0510011
```

The Lean 4 regular-primes FLT paper also states that the `n = 3` case had been done previously in Isabelle, and the Mason-Stothers formalization paper compares a Lean 4 development with earlier Isabelle and Lean 3 formalizations of Mason-Stothers.

Sources checked:

```text
https://arxiv.org/abs/2410.01466
https://arxiv.org/abs/2408.15180
```

These are useful indicators of formalized Diophantine number theory, but they do not provide Mazur torsion.

---

## What about Faltings' theorem / Mordell conjecture?

I found no public proof-assistant formalization of Faltings' theorem / the Mordell conjecture.

Mathematically, Faltings says that a nonsingular curve of genus greater than one over a number field has finitely many rational points.  That theorem is far beyond the current public formalization state of arithmetic geometry.  Even if formalized, it would not by itself solve Mazur, because Mazur needs explicit rational-point classification on modular curves, not merely finiteness.

Reference for the mathematical theorem checked:

```text
https://en.wikipedia.org/wiki/Faltings%27_theorem
```

For FLT planning, Faltings is not an importable route.

---

## Can FLT import existing work?

### Importable directly into Lean

Likely useful:

```text
Mathlib algebra, number fields, class groups, cyclotomic fields;
Mathlib Weierstrass curves and group law;
Mathlib division polynomials;
Mathlib schemes/local ringed spaces;
Mathlib modular forms/q-expansions/cusps;
possibly compatible Lean 4 code from flt-regular if it is not already merged into Mathlib.
```

But none of these imports contains Mazur's theorem.

### Not directly importable

Coq/Rocq and Isabelle developments cannot be imported into Lean as trusted theorem dependencies.  They can guide proofs, but they are not Lean kernel objects.

Computer algebra systems such as Sage/Magma/LMFDB can provide models, rational-point lists, or certificates, but their output must be rechecked in Lean if it is to be part of a theorem.

---

## Recommended FLT strategy

Use an explicit axiom boundary around the true missing theorem, not around the whole A-Line.

```lean
import Mathlib

namespace FLT

axiom HasRationalPointOfOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop

/-- Critical composite orders to be eliminated by fixed-level certificates. -/
inductive CriticalComposite : ℕ → Prop
  | n14 : CriticalComposite 14
  | n15 : CriticalComposite 15
  | n16 : CriticalComposite 16
  | n18 : CriticalComposite 18
  | n20 : CriticalComposite 20
  | n21 : CriticalComposite 21
  | n24 : CriticalComposite 24
  | n25 : CriticalComposite 25
  | n27 : CriticalComposite 27
  | n35 : CriticalComposite 35
  | n49 : CriticalComposite 49

/-- Prime-level Mazur core.  Keep as the main temporary axiom. -/
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E p

/-- Fixed-level composite certificates.  Replace constructor-by-constructor. -/
axiom no_point_of_critical_composite_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : CriticalComposite n) :
    ¬ HasRationalPointOfOrder E n

end FLT
```

Then prove all the reductions in Lean:

```text
1. exact-order divisor lemma using `addOrderOf`;
2. arithmetic lemma: large `n` has either a prime divisor >= 11 or a critical composite divisor;
3. no-point-of-order-ge-17 from the prime axiom plus composite certificates;
4. low-order finite cases separately;
5. replace composite certificates one by one using existing Kubert/QuarticD/descent bridges.
```

This gives the best audit trail:

```text
formalized now:
  group theory + arithmetic reductions + fixed-level certificates as they are built;

one hard temporary axiom:
  prime-level Mazur theorem for X_1(p), p >= 11.
```

If the repo later proves `p = 11` and `p = 13` via explicit modular-curve certificates, shrink the hard axiom to `p >= 17`.

---

## Final conclusion

There is no known public proof-assistant formalization to import for Mazur torsion, the prime-order Mazur core, `X_1(N)` rational-point classification, or Merel uniform boundedness.

The closest related Lean work provides strong foundations:

```text
Weierstrass elliptic curves and group law;
division polynomials;
number fields, cyclotomic fields, class groups;
explicit class-group/integral-point computations;
analytic modular forms;
schemes;
FLT for regular primes.
```

But the actual Mazur A-Line still has to be built or axiomatically isolated.  The right isolation is:

```text
no_point_of_prime_order_ge_11
```

plus finite composite certificates, not a monolithic `mazur_torsion_theorem` axiom.
