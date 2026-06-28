# Q1999 (dm1): Weil pairing / full rational torsion planning

Goal:

```text
For an elliptic curve E / Q and m ≥ 1:
if E[m](\bar Q) is fully rational over Q, then Q contains a primitive m-th
root of unity.  Since the only rational roots of unity are ±1, this implies
m ≤ 2.
```

This is the standard Weil-pairing obstruction.  The hard part is not the final
`m ≤ 2` step; the hard part is producing enough infrastructure to obtain a
primitive `m`-th root of unity in `Q` from full rationality of `E[m]`.

## Current Mathlib situation, relevant to route choice

As of the current Mathlib files I checked:

* `WeierstrassCurve` is available for nonsingular Weierstrass curves, with
  discriminant and the 2-torsion polynomial.
* Nonsingular affine, projective, and Jacobian points on Weierstrass curves have
  abelian group instances.
* The affine coordinate ring and its fraction field are already present.
* Scheme-level function fields for integral schemes exist.
* `rootsOfUnity`, `IsPrimitiveRoot`, `HasEnoughRootsOfUnity`, modular
  cyclotomic characters, and finite abelian duality are already present.
* I did not find an existing elliptic-curve Weil pairing or Tate pairing in
  Mathlib.

So Mathlib already has the endpoint language on both sides:

```text
E(K) as an additive commutative group,
rootsOfUnity m K,
IsPrimitiveRoot ζ m,
modularCyclotomicCharacter.
```

The missing bridge is:

```text
e_m : E[m] × E[m] → μ_m
```

with bilinearity, alternating/skew symmetry, nondegeneracy, and either
base-field rationality or Galois equivariance.

## The tiny final theorem once the bridge exists

Once we have a pairing theorem, the final obstruction is small.

A convenient interface theorem would be:

```lean
-- Informal shape only.
theorem exists_primitive_root_of_full_rational_torsion
    (E : WeierstrassCurve over Q)
    (m : ℕ) [NeZero m]
    (hfull : FullRationalMTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Then prove separately:

```lean
theorem rat_isPrimitiveRoot_le_two
    {ζ : ℚ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) : m ≤ 2
```

This last lemma should be easy: a rational root of unity is `1` or `-1`, so its
order is `1` or `2`.  It does not require elliptic curves.

The planning question is therefore: what is the least painful way to prove the
pairing theorem?

---

# Route 1: Full Weil pairing via divisors on elliptic curves

## Mathematical idea

Construct the classical Weil pairing using divisors and rational functions.

For `P,Q ∈ E[m]`, choose functions `f_P`, `f_Q` with

```text
div(f_P) = m(P) - m(O),
div(f_Q) = m(Q) - m(O).
```

Then define a Weil pairing by evaluating translated functions on suitable
auxiliary divisors, or by one of the equivalent divisor formulas.  Prove:

```text
e_m(P,Q) ∈ μ_m,
e_m is bilinear,
e_m is alternating,
e_m is nondegenerate,
e_m is Galois equivariant / defined over the base field.
```

If all `m`-torsion points are rational over `Q`, pick a `ZMod m`-basis
`P,Q` of `E[m]`.  Nondegeneracy gives `e_m(P,Q)` primitive of order `m`;
rationality gives `e_m(P,Q) ∈ Q`.

## (a) Mathematical prerequisites

* Divisors on a nonsingular complete curve.
* Principal divisors of rational functions.
* Translation of divisors by elliptic-curve points.
* Existence of `f_P` with divisor `m(P)-m(O)`.
* Evaluation of functions on divisors with disjoint support.
* Weil reciprocity.
* Proof of bilinearity, alternatingness, and nondegeneracy.
* Base change or Galois equivariance.

## (b) What Mathlib already has

Useful pieces:

* Weierstrass curves and nonsingular point group laws.
* Affine coordinate rings and function fields for Weierstrass curves.
* Scheme-level function fields for integral schemes.
* `rootsOfUnity` and primitive roots.
* General finite abelian group facts.

Likely missing:

* Divisors on arbitrary curves in the form needed here.
* Orders of vanishing/poles of rational functions at elliptic-curve points.
* Principal divisors of line functions and vertical-line functions.
* Weil reciprocity specialized to elliptic curves.
* Any existing `WeilPairing` definition for elliptic curves.

## (c) Estimated new code

Rough estimate: **5k--12k lines** if done cleanly and reusable in Mathlib.

A highly specialized version for Weierstrass curves over fields of characteristic
zero might fit in **3k--7k lines**, but it would still be a major project.

## (d) Main technical obstruction

The bottleneck is divisor infrastructure, not the group law.  You must make
rational functions, supports, orders, and evaluations usable enough to prove
nondegeneracy.  The nondegeneracy proof is the hard theorem: it is where
Riemann-Roch/divisor-class facts normally enter.

## Verdict

Mathematically canonical and best long-term Mathlib contribution, but not the
least new infrastructure.

---

# Route 1b: Explicit Miller-function Weil pairing, avoiding general divisors as much as possible

## Mathematical idea

Use the computational definition of the Weil pairing from Miller functions.
For a point `P`, recursively define functions `f_{n,P}` using line functions
and vertical-line functions satisfying the divisor identity

```text
div(f_{n,P}) = n(P) - (nP) - (n-1)(O).
```

For `P,Q ∈ E[m]`, evaluate a normalized expression such as

```text
e_m(P,Q) = (-1)^m * f_{m,P}(Q) / f_{m,Q}(P)
```

with the usual support-avoidance or shifted-divisor trick.

This route proves only the pieces needed for Weierstrass curves, using explicit
line equations rather than a full curve-divisor API.

## (a) Mathematical prerequisites

* Explicit line function through two points and tangent line at a point.
* Vertical line function through `P` and `-P`.
* Divisor identity for each line/vertical function.
* Miller recursion and its divisor identity.
* A safe evaluation API avoiding zeros/poles, or a shifted auxiliary point.
* Bilinearity and alternatingness.
* Nondegeneracy.

## (b) What Mathlib already has

Strongly useful:

* Explicit formulas for affine/projective/Jacobian addition.
* Affine coordinate ring and function field for a Weierstrass curve.
* Polynomial/rational-function algebra.
* `rootsOfUnity`.
* Finite abelian groups and `ZMod`.

Likely missing:

* A lightweight divisor/order-of-vanishing API even for explicit functions.
* The divisor identities for line and vertical functions.
* The nondegeneracy proof.

## (c) Estimated new code

Rough estimate: **2k--5k lines** for a specialized, non-Mathlib-perfect file.

If made reusable and polished enough for Mathlib, probably **4k--8k lines**.

## (d) Main technical obstruction

Even “divisor-free” Miller pairing is not really divisor-free: to prove the
recursion correct and prove nondegeneracy, you still need enough divisor/order
language.  But the required divisor language can be much narrower than in Route
1.

## Verdict

This is probably the **least new infrastructure for a real theorem**.  It uses
the existing Weierstrass and function-field work and avoids building all of
curve divisor theory first.

Recommended if the goal is to discharge the Mazur axiom without waiting for a
complete algebraic-geometry divisor library.

---

# Route 1c: Abstract Weil-pairing interface first, implementation later

## Mathematical idea

Introduce a narrow interface containing just the facts needed:

```lean
class HasWeilPairingForFullLevel (E m K) where
  pairing : Emtorsion E m → Emtorsion E m → rootsOfUnity m K
  map_add_left  : ...
  map_add_right : ...
  alternating   : ...
  nondegenerate : ...
  primitive_on_basis : ...
  rational_if_points_rational : ...
```

Then prove the Mazur obstruction from this interface now.  Later, fill the
interface using Route 1 or 1b.

## (a) Mathematical prerequisites

Only abstract finite-group pairing theory.

## (b) What Mathlib already has

* Finite abelian groups.
* `ZMod`.
* roots of unity.
* Group homomorphisms and bilinear maps.
* Enough linear algebra to formulate a basis of `E[m]` as a `ZMod m` module,
  although this may need some convenience lemmas.

## (c) Estimated new code

**200--600 lines** for the interface and the theorem

```text
full rational torsion + pairing interface => primitive rational root.
```

## (d) Main technical obstruction

This does **not** actually construct the Weil pairing.  It only isolates the
remaining axiom in its mathematically correct minimal form.

## Verdict

This is the best short-term architecture.  It gives a clean target theorem and
prevents the Mazur proof from depending on the internal construction of the
pairing.

It is not a final discharge unless the interface fields are proved.

---

# Route 2: Determinant of the mod-m Galois representation equals the cyclotomic character

## Mathematical idea

Let

```text
ρ_{E,m} : Gal(\bar Q / Q) → Aut(E[m]) ≃ GL₂(Z/mZ).
```

Prove

```text
det(ρ_{E,m}) = χ_m,
```

where `χ_m` is the mod-`m` cyclotomic character.

If `E[m]` is fully rational over `Q`, then `ρ_{E,m}` is trivial, so its
determinant is `1`.  Hence `χ_m` is trivial, so every `m`-th root of unity is
fixed by `Gal(\bar Q/Q)`, and a primitive `m`-th root lies in `Q`.

## (a) Mathematical prerequisites

* The `m`-torsion subgroup over `\bar Q`.
* A `ZMod m`-module structure on `E[m]`.
* Freeness/rank-two theorem: `E[m] ≃ (ZMod m)^2` for `char K ∤ m`.
* Galois action on torsion.
* Matrix representation of the action and determinant.
* Cyclotomic character mod `m`.
* The theorem `det ρ = χ_m`.

## (b) What Mathlib already has

Useful:

* Modular cyclotomic character is already present.
* Galois groups and field automorphisms exist.
* Elliptic-curve point groups exist.
* Linear algebra and determinants over `ZMod m` exist.

Likely missing:

* `E[m]` as a finite free `ZMod m`-module of rank two.
* Galois representation attached to an elliptic curve.
* `det ρ = χ_m`.
* The bridge between fixed roots in `\bar Q` and roots in `Q`, unless one
  formulates the theorem using values already in `Q`.

## (c) Estimated new code

If `det ρ = χ_m` is assumed as a theorem: **500--1500 lines** to package torsion,
the representation, and the conclusion.

If `det ρ = χ_m` is proved: **4k--10k lines**, because the standard proof uses
the Weil pairing.

## (d) Main technical obstruction

This route is not independent of the Weil pairing in the usual mathematics:
`det ρ = χ_m` is normally proved from Galois equivariance of the Weil pairing.
Without importing that theorem as an axiom, this route tends to collapse back
to Route 1 or 1b.

## Verdict

Excellent final packaging theorem, especially because Mathlib already has
cyclotomic character infrastructure.  But it is not the least-infrastructure way
to build the missing mathematics from scratch.

---

# Route 2b: Frobenius determinant / reduction mod p route

## Mathematical idea

Avoid global Galois representations by using good reduction.

If `E[m]` is rational over `Q`, then for every good prime `p ∤ m`, Frobenius at
`p` acts trivially on `E[m]`.  If one proves

```text
det(Frob_p | E[m]) = p mod m,
```

then `p ≡ 1 mod m` for every good `p ∤ m`.

Then choose a good prime `p` with `p not ≡ 1 mod m`, contradiction unless
`m ≤ 2`.

## (a) Mathematical prerequisites

* Integral/minimal model enough to define good reduction.
* Reduction map on torsion and injectivity away from `p`.
* Frobenius action on reduced torsion.
* Determinant of Frobenius equals `p`.
* Existence of a prime outside a finite bad set and outside `1 mod m`.

## (b) What Mathlib already has

Useful:

* Some elliptic-curve reduction files exist in Mathlib.
* Basic finite fields, Frobenius, and number-theory infrastructure exist.
* Prime-number facts exist, but the exact “prime outside bad set and congruence”
  lemma may need work.

Likely missing:

* A ready-to-use reduction theorem for torsion of an elliptic curve over `Q`.
* Frobenius determinant theorem for elliptic curves.
* The finite bad-prime bookkeeping.

## (c) Estimated new code

**5k--12k lines**, depending heavily on how much reduction infrastructure is
already usable in the FLT branch.

## (d) Main technical obstruction

The identity `det(Frob_p)=p` is again essentially the determinant/cyclotomic
character theorem at Frobenius elements.  It can be proved by finite-field
elliptic-curve theory, but that is still a major development.

## Verdict

A plausible route if the project already needs reduction/Frobenius anyway, but
not the least new infrastructure for this specific axiom.

---

# Route 3: Tate pairing / local Tate duality

## Mathematical idea

Use a Tate pairing, either over finite fields or local fields, to get a
nondegenerate pairing involving `E[m]` and roots of unity.  Then specialize to
the fully rational case.

## (a) Mathematical prerequisites

Depending on variant:

* Kummer sequence.
* Galois cohomology or divisor-class pairing.
* Local fields or finite fields.
* Local Tate duality or Tate-Lichtenbaum pairing.
* Compatibility with rational torsion.

## (b) What Mathlib already has

Useful:

* Some roots-of-unity and cyclotomic infrastructure.
* Some class group and field theory infrastructure.
* Some local/p-adic infrastructure.

Likely missing:

* Galois cohomology at the required level.
* Tate pairing for elliptic curves.
* Local duality.
* Pairing nondegeneracy theorems.

## (c) Estimated new code

**8k--20k+ lines**.

## (d) Main technical obstruction

This route needs more infrastructure than the Weil pairing route.  It is a
powerful theorem, but it is not a shortcut to the Mazur obstruction.

## Verdict

Not recommended for this axiom.

---

# Route 4: Elementary coordinate/division-polynomial argument

## Mathematical idea

Try to prove directly from rationality of all `m`-torsion coordinates that
`Q` contains a primitive `m`-th root of unity, without naming the Weil pairing.

Possible subroutes:

1. Use division polynomials and discriminants.
2. Use explicit formulas for small `m`, especially `m=3,4,5`.
3. Use Hesse form for full rational 3-torsion.
4. Use duplication/addition formulas to derive contradictions case by case.

## (a) Mathematical prerequisites

For a general theorem:

* Division polynomials for all `m`.
* Their relation to torsion coordinates.
* A theorem extracting roots of unity from the full splitting/rationality of
  those coordinates.

For small cases:

* Explicit division polynomials and resultants/discriminants for each `m`.

## (b) What Mathlib already has

Useful:

* Division polynomial files exist.
* Polynomial algebra, resultants/discriminants, and rational-root tools exist.
* Weierstrass point addition formulas exist.

Likely missing:

* A general theorem connecting full rational `m`-torsion to a cyclotomic
  subfield using division polynomials.
* Case-specific computations for Mazur-relevant `m`.

## (c) Estimated new code

General theorem: hard to estimate, likely **4k--10k lines** and probably
reinvents the determinant/Weil-pairing theorem.

Finite list only: perhaps **1k--4k lines** if the Mazur proof only needs to
exclude a small finite set of `m` values.

## (d) Main technical obstruction

There is no known clean general elementary argument that avoids the Weil pairing
in substance.  For `m=3`, there are classical explicit arguments; for arbitrary
`m`, division-polynomial proofs tend to become the Weil pairing/determinant
theorem in disguise.

## Verdict

Potentially the least code for a **finite-case workaround**, but not the best
route for the theorem as stated.

If the Mazur formalization only needs to rule out full rational `m`-torsion for
specific `m > 2`, this route deserves a separate finite-case feasibility study.

---

# Route 5: Modular curves / full level structure

## Mathematical idea

A full level-`m` structure is a basis of `E[m]`.  The moduli problem with full
level structure naturally lives over `Z[1/m, ζ_m]`, because the Weil pairing of
a symplectic basis is a primitive `m`-th root of unity.

Thus a `Q`-rational full level-`m` structure should imply that `ζ_m` is defined
over `Q`.

## (a) Mathematical prerequisites

* Moduli problem for elliptic curves with full level structure.
* Modular curve or modular stack `Y(m)` / `X(m)`.
* Its field/ring of definition involving `ζ_m`.
* Descent of rational points/level structures.

## (b) What Mathlib already has

Useful:

* The FLT project has modular-forms/modularity-related infrastructure.
* Mathlib has algebraic geometry foundations.

Likely missing:

* Modular curves/stacks with full level structure at this concrete level.
* The representability/descent theorem needed here.
* A formal link back to torsion of a Weierstrass curve.

## (c) Estimated new code

**10k--30k+ lines**.

## (d) Main technical obstruction

This is a very high-level way to package the Weil pairing.  It requires a large
moduli stack/modular curve development before reaching the simple obstruction.

## Verdict

Conceptually elegant, but far too much infrastructure for the immediate Mazur
torsion axiom.

---

# Route 6: Finite flat group schemes / Cartier duality / polarization

## Mathematical idea

Use the abstract abelian-variety/group-scheme theorem:

```text
E[m]^D is the Cartier dual of E[m],
```

and the principal polarization `E ≃ E^∨` gives a perfect alternating pairing

```text
E[m] × E[m] → μ_m.
```

If `E[m]` is the constant group scheme `(Z/mZ)^2` over `Q`, then its Cartier
dual involves `μ_m`, forcing `μ_m` to be constant / rational enough to contain a
primitive `m`-th root.

## (a) Mathematical prerequisites

* Finite flat group schemes.
* Cartier duality.
* Kernel of multiplication-by-`m` on an elliptic curve as a finite flat group
  scheme.
* Principal polarization of an elliptic curve.
* The induced Weil pairing.
* Constant group schemes and diagonalizable group schemes `μ_m`.

## (b) What Mathlib already has

Useful:

* FLT imports include group-scheme/finite-flat related files.
* Mathlib has category theory and algebraic geometry foundations.
* Roots of unity are present.

Likely missing:

* A complete finite-flat group scheme duality API strong enough for this theorem.
* Elliptic curves as group schemes/abelian schemes.
* Principal polarizations of elliptic curves.
* `E[m]` as a finite flat group scheme linked to the point group API.

## (c) Estimated new code

If starting from current public Mathlib: **10k--25k+ lines**.

If the FLT group-scheme infrastructure is already close to finite flat Cartier
duality, maybe **4k--10k lines**, but this is uncertain.

## (d) Main technical obstruction

The current Weierstrass point API is pointwise/group-theoretic, while this route
needs scheme-level elliptic curves and finite flat subgroup schemes.  Bridging
those worlds is substantial.

## Verdict

Excellent long-term architecture for arithmetic geometry in Lean, but not the
least new code for this Mazur axiom.

---

# Route 7: Theta group / Heisenberg commutator route

## Mathematical idea

Construct the theta group central extension associated to the divisor `m(O)`:

```text
1 → G_m → G(L) → E[m] → 1.
```

The commutator pairing on this central extension is the Weil pairing:

```text
[P~, Q~] = e_m(P,Q) ∈ G_m.
```

If all torsion translations are rational, the commutator is rational and
nondegenerate, giving a primitive `m`-th root in `Q`.

## (a) Mathematical prerequisites

* Line bundle or divisor `m(O)`.
* Pullback of line bundles by translations.
* Theta group central extension.
* Commutator pairing.
* Nondegeneracy.

## (b) What Mathlib already has

Useful:

* Some category/algebraic-geometry infrastructure.
* Weierstrass group law.

Likely missing:

* Line bundles/divisors on elliptic curves in the required explicit form.
* Theta groups.
* The commutator pairing theorem.

## (c) Estimated new code

**3k--8k lines** if done very explicitly for Weierstrass curves;
**8k--15k+ lines** if done geometrically and reusable.

## (d) Main technical obstruction

This is another presentation of the Weil pairing.  It may avoid some explicit
Miller-function algebra, but it replaces it with line-bundle/divisor machinery.

## Verdict

Interesting but probably not easier than Route 1b.

---

# Route 8: Complex analytic uniformization

## Mathematical idea

Over `C`, write

```text
E(C) ≃ C / Λ.
```

Then

```text
E[m] ≃ (1/m Λ) / Λ ≃ (Z/mZ)^2,
```

and the analytic Weil pairing is

```text
e_m((a,b),(c,d)) = exp(2πi(ad-bc)/m).
```

A rational full level basis would force the corresponding primitive root to be
Galois/rational.

## (a) Mathematical prerequisites

* Complex elliptic functions and lattices.
* Uniformization theorem for elliptic curves over `C`.
* Comparison with algebraic torsion.
* Algebraicity of the analytic pairing value.
* Galois/rationality comparison.

## (b) What Mathlib already has

Useful:

* Complex analysis foundations.
* Some modular/elliptic-function pieces may exist, but not enough for this.

Likely missing:

* Full complex uniformization of algebraic elliptic curves.
* Weierstrass elliptic functions at the required theorem level.
* Comparison theorem between analytic and algebraic torsion.

## (c) Estimated new code

**15k--40k+ lines**.

## (d) Main technical obstruction

This imports a huge transcendental theory just to prove an algebraic obstruction.

## Verdict

Not recommended.

---

# Route 9: Explicit finite-field counting / Hasse-bound contradiction

## Mathematical idea

If `E[m]` is rational over `Q`, then for good primes `p`, the reduction
`E(F_p)` contains a copy of `(Z/mZ)^2`, so

```text
m^2 ∣ #E(F_p).
```

Maybe combine this with Hasse bounds and chosen small primes to force `m ≤ 2`.

## (a) Mathematical prerequisites

* Reduction injectivity of prime-to-`p` torsion.
* Hasse bound.
* Prime selection avoiding bad primes and bounding congruences.

## (b) What Mathlib already has

Useful:

* Some finite-field and elliptic-curve infrastructure.
* Basic number theory.

Likely missing:

* Hasse bound for elliptic curves over finite fields, if not already available.
* Strong enough reduction of torsion.
* A uniform prime-selection argument.

## (c) Estimated new code

For a finite list of `m`, perhaps **2k--6k lines**.

For all `m`, probably not competitive with the determinant route.

## (d) Main technical obstruction

The statement `m^2 ∣ #E(F_p)` for all good `p` is weaker than `p ≡ 1 mod m`.
It may not give a clean contradiction uniformly without much more analytic or
arithmetic input.  The determinant theorem is the sharper and standard version.

## Verdict

Could be useful for finite ad hoc exclusions, but unlikely to prove the general
theorem elegantly.

---

# Route 10: A narrowly scoped imported theorem / axiom replacement

## Mathematical idea

Instead of formalizing Weil pairing immediately, add the exact theorem needed as
a named assumption or theorem stub:

```lean
axiom primitive_root_of_full_rational_m_torsion_Q :
  FullRationalMTorsion E m → ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Then prove `m ≤ 2` from this theorem.  This makes the deepest axiom precise and
isolated.

A slightly better variant is to assume a generic pairing interface rather than
the final conclusion, as in Route 1c.

## (a) Mathematical prerequisites

None beyond trusting the theorem.

## (b) What Mathlib already has

Enough to state the conclusion with roots of unity and rational numbers, once
`FullRationalMTorsion` is defined.

## (c) Estimated new code

**50--300 lines**.

## (d) Main technical obstruction

It does not reduce the trusted base unless later replaced.

## Verdict

Best project-management move if the goal is to keep the Mazur formalization
moving while preserving a clean future target.

---

# Comparison table

| route | independent of Weil pairing? | new infrastructure | estimated code | recommendation |
|---|---:|---:|---:|---|
| 1. Full divisors | yes, constructs it | very high | 5k--12k | best long-term canonical route |
| 1b. Explicit Miller pairing | yes, constructs it | medium-high | 2k--5k | best real route for least infrastructure |
| 1c. Abstract pairing interface | no, isolates it | low | 200--600 | best immediate architecture |
| 2. det rho = cyclotomic | usually no | medium/high | 500--1500 if assumed; 4k--10k if proved | good packaging, not first construction |
| 2b. Frobenius determinant | essentially no | high | 5k--12k | useful only if reduction theory is already needed |
| 3. Tate pairing | yes but heavier | very high | 8k--20k+ | not recommended |
| 4. elementary/division polynomials | maybe for finite cases | low/medium for finite cases, high generally | 1k--4k finite; 4k--10k general | possible workaround, not general |
| 5. modular curves/full level | no, packages pairing | very high | 10k--30k+ | not for this axiom |
| 6. group schemes/Cartier duality | yes, abstractly | very high | 10k--25k+ | long-term AG route |
| 7. theta group | yes, but same core | high | 3k--8k | probably harder than Miller |
| 8. complex uniformization | yes | enormous | 15k--40k+ | not recommended |
| 9. finite-field counting | partially | medium/high | 2k--6k finite; high general | ad hoc only |
| 10. scoped theorem/axiom | no | tiny | 50--300 | best temporary axiom isolation |

# Least-infrastructure recommendation

## For a real proof

Use **Route 1b: explicit Miller-function Weil pairing**, but implement it in
layers so that the Mazur proof only depends on a small theorem.

Suggested target theorem:

```lean
theorem exists_primitive_root_of_full_rational_m_torsion
    {m : ℕ} [NeZero m] (hm : 0 < m)
    (E : /* elliptic curve over Q */)
    (hfull : FullRationalMTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Implementation layers:

1. Define `E[m]` as a finite subgroup of the existing point group.
2. Prove/assume for the first pass that full `m`-torsion gives two points
   `P,Q` forming a basis of `E[m]`.
3. Define a minimal `WeilPairing` structure with values in `rootsOfUnity m K`.
4. Prove the abstract theorem:
   a nondegenerate alternating pairing on a rank-two `ZMod m` torsion module
   gives a primitive root.
5. Implement the pairing by Miller functions for Weierstrass curves.
6. Prove rationality over `Q` when `P,Q` and the curve coefficients are rational.
7. Prove `Rat` has no primitive roots except orders `1` and `2`.

The reason this is least infrastructure is that it uses existing Weierstrass
point/function-field machinery and avoids building full schemes, divisors,
Tate duality, modular curves, or abelian varieties.

## For immediate project hygiene

First add Route 1c as an interface and rewrite the Mazur proof to depend on:

```text
FullRationalMTorsion E m → ∃ ζ : Q, IsPrimitiveRoot ζ m.
```

Then the remaining axiom is a single, named theorem whose planned proof is
Route 1b.

## Do not start with det rho

Although `det ρ = χ` looks shorter on paper, proving it without already having
the Weil pairing is not shorter.  The determinant theorem is an excellent
corollary/export once the pairing exists, not the best first construction.

## Do not start with Tate pairing

Tate pairing requires more cohomology/local-field infrastructure than the
Weil pairing route and gives a more complicated path to the same conclusion.

## Elementary route caveat

If the practical Mazur proof only needs finitely many `m`, a finite-case
division-polynomial project may be shorter than a general Weil pairing.  But it
will not prove the clean theorem

```text
full rational E[m] ⇒ μ_m ⊂ Q
```

for all `m`, and it may produce many brittle computations.

# Recommended Round 2 tasks

1. Inventory the exact current definition of elliptic-curve points used in the
   Mazur files.
2. Define the statement `FullRationalMTorsion E m`.
3. Prove the rational-root-of-unity lemma for `Q`.
4. Add an abstract pairing-interface theorem:
   `FullRationalMTorsion + WeilPairingInterface ⇒ primitive root in Q`.
5. Decide whether to implement Miller pairing or a finite-case workaround.

My recommendation is:

```text
Round 2: build the abstract interface and final Q-root lemma.
Round 3: start the explicit Miller-pairing implementation.
```
