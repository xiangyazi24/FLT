# Q1233 (dm2): Codex task specification — prove `#E(ℝ)[m] ≤ 2m`

This is a self-contained task specification for Codex Pro.  It assumes no prior chat context.

## Goal

In the `xiangyazi24/FLT` Lean 4 repository, replace the custom axiom

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

axiom real_mTorsion_card_le
    (m : N) (hm : 0 < m) (E : WeierstrassCurve Q) [E.IsElliptic] :
    Set.ncard {P : (E/R).Point | (m : N) * P = 0} <= 2 * m
```

with a theorem/proof of the same statement.  Preserve the public name and signature unless the existing file uses a definitional spelling such as `ℕ` for `N`, `ℚ` for `Q`, `ℝ` for `R`, or `m • P` instead of `(m : N) * P`.  In that case, keep the exact spelling already used by the repository.

The finished theorem should have this shape:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

-- use the namespace already present in the target file

theorem real_mTorsion_card_le
    (m : N) (hm : 0 < m) (E : WeierstrassCurve Q) [E.IsElliptic] :
    Set.ncard {P : (E/R).Point | (m : N) * P = 0} <= 2 * m := by
  -- proof, no sorry, no custom axiom
  sorry
```

The final committed code must contain no `sorry` in this theorem or in any new helper lemmas added for this task.  The displayed `sorry` above is only a placeholder in the task specification.

## Mathematical statement

Let `E/ℚ` be an elliptic curve.  Base-change it to `ℝ`, and write

```text
G = E(ℝ).
```

The target set is the real `m`-torsion subgroup:

```text
G[m] = { P ∈ G | mP = 0 }.
```

The theorem to prove is:

```text
#G[m] ≤ 2m,     for every m > 0.
```

## Mathematical argument to formalize

The real locus of a nonsingular real elliptic curve is a compact abelian one-dimensional Lie group.  Its connected-component structure is classical:

```text
E(ℝ) ≅ S¹
```

or

```text
E(ℝ) ≅ S¹ × ℤ/2ℤ.
```

Equivalently, the identity component is a circle and the component group has order at most `2`:

```text
0 → E(ℝ)⁰ → E(ℝ) → π₀(E(ℝ)) → 0,
#π₀(E(ℝ)) ≤ 2,
E(ℝ)⁰ ≅ S¹.
```

For the circle, multiplication by `m` has exactly `m` kernel points:

```text
(S¹)[m] ≅ ℤ/mℤ,
#(S¹)[m] = m.
```

Therefore the exact sequence on components gives

```text
#E(ℝ)[m]
  ≤ #(E(ℝ)⁰[m]) * #π₀(E(ℝ))
  ≤ m * 2
  = 2m.
```

If using the split classification directly:

```text
#(S¹)[m] = m,
#((S¹ × ℤ/2ℤ)[m]) = m * #(ℤ/2ℤ)[m] ≤ 2m.
```

This is the intended proof.  Do not settle for the weaker algebraic bound `#E[m](ℝ) ≤ m²`; the target bound is linear in `m`.

## Repository instructions

1. Start by locating the existing declaration:

```bash
grep -R "real_mTorsion_card_le" -n FLT FermatsLastTheorem scratch || true
```

2. Inspect nearby imports, namespace, notation aliases, and any existing helper axioms/theorems:

```bash
grep -R "mTorsion\|Torsion\|RealTorsion\|AddCircle\|UnitAddCircle" -n FLT FermatsLastTheorem scratch .lake/packages/mathlib/Mathlib | head -200
```

3. Replace the axiom with a theorem.  Add helper lemmas only where they naturally belong.  Prefer local/private helper lemmas in the same file unless a reusable result clearly belongs in a new helper file.

4. Do not change downstream theorem statements.  If the proof requires changing imports, keep the import graph acyclic and minimal.

## Mathlib APIs and search targets

Codex should inspect the installed Mathlib in this repository; exact theorem names may differ from memory.  The following API families are expected to be relevant.

### Circle groups

Search for additive and unit-circle APIs:

```bash
grep -R "def AddCircle\|structure AddCircle\|namespace AddCircle\|UnitAddCircle\|unitCircle" -n .lake/packages/mathlib/Mathlib | head -200
```

Likely useful concepts:

```lean
import Mathlib

#check AddCircle
#check UnitAddCircle
#check ZMod
```

Expected lemma to prove or locate:

```lean
import Mathlib

noncomputable section

open scoped Classical

-- Desired helper, name flexible:
theorem addCircle_mTorsion_ncard
    (m : ℕ) (hm : 0 < m) :
    Set.ncard {x : AddCircle | m • x = 0} = m := by
  -- prove via `ZMod m ≃+ {x : AddCircle | m • x = 0}`
  sorry
```

Implementation hints:

* `AddCircle` is `ℝ / ℤ`-style additive circle.  The `m`-torsion points are represented by `k / m` for `k : ZMod m`.
* If `UnitAddCircle` or the complex unit circle has better root-of-unity support, it is also acceptable to prove the circle torsion cardinality there and transfer it across an existing equivalence with `AddCircle`.
* A root-of-unity route should show the kernel of `z ↦ z^m` on the unit circle has cardinal `m`.

### Finite cyclic groups and cardinality

Search:

```bash
grep -R "card_zmod\|Fintype.card.*ZMod\|ZMod.*card\|Set.ncard" -n .lake/packages/mathlib/Mathlib | head -200
```

Useful concepts:

```lean
import Mathlib

#check ZMod
#check Fintype.card
#check Set.ncard
#check Set.Finite
```

Prefer proving finite set cardinal statements using `Fintype` on subtypes when convenient, then convert to `Set.ncard`.

### Real elliptic curve topology and components

Search for existing topology/component facts on real Weierstrass curves and elliptic-curve point groups:

```bash
grep -R "WeierstrassCurve.*Real\|Real.*WeierstrassCurve\|connectedComponent\|ConnectedComponent\|PathConnected\|IsPreconnected\|IsConnected\|component" -n FLT FermatsLastTheorem .lake/packages/mathlib/Mathlib | head -300
```

The ideal helper theorem has one of the following forms, depending on available APIs:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

-- Strong form, if available/provable:
theorem real_points_addEquiv_circle_or_circle_prod_zmodTwo
    (E : WeierstrassCurve Q) [E.IsElliptic] :
    (Nonempty ((E/R).Point ≃+ AddCircle)) ∨
      (Nonempty ((E/R).Point ≃+ AddCircle × ZMod 2)) := by
  sorry
```

A weaker and often easier-to-use form is enough:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

-- Schematic: use the repository's actual type for the component quotient.
theorem real_points_identity_component_circle_and_component_bound
    (E : WeierstrassCurve Q) [E.IsElliptic] :
    -- identity component is additively equivalent to `AddCircle`
    -- and the component quotient has cardinal at most 2
    True := by
  sorry
```

The final proof only needs:

1. the identity component contributes at most `m` points to `m`-torsion;
2. the component group contributes at most a factor of `2`.

It is acceptable to prove a generic lemma saying that if an additive commutative group `G` has a subgroup `G0` whose `m`-torsion has cardinal at most `m`, and the quotient/component image has cardinal at most `2`, then `#G[m] ≤ 2m`.

### Division polynomials, IVT, and polynomial root counting

These APIs are not expected to prove the circle-torsion lemma directly, but they may be useful if Mathlib lacks a ready-made theorem on real elliptic-curve components and Codex needs to prove the component classification from the real Weierstrass equation.

Search:

```bash
grep -R "DivisionPolynomial\|division polynomial\|WeierstrassCurve.*Ψ\|WeierstrassCurve.*ψ\|Polynomial.*roots\|card_roots\|IntermediateValue\|intermediate_value" -n .lake/packages/mathlib/Mathlib FLT FermatsLastTheorem | head -300
```

Potentially useful APIs:

```lean
import Mathlib

#check Polynomial
#check Polynomial.roots
#check Polynomial.natDegree
#check Polynomial.card_roots
```

Expected use if component facts are missing:

* Put the real Weierstrass equation into completed-square form:

```text
(2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆.
```

* Analyze the real cubic on the right.  A real cubic has either one or three real roots counted without multiplicity when the elliptic curve is nonsingular.
* The real locus has either one component or two components, according to whether that cubic has one real root or three real roots.
* Use IVT to identify intervals where the cubic is nonnegative and polynomial root counting to bound the number of sign changes/root intervals.
* Combine this with the standard group-topology fact that the identity component is a circle.

Do not use division-polynomial root counting alone as the main proof: it gives the wrong order of magnitude (`O(m²)`) unless combined with the real component/circle argument.

## Suggested proof architecture

### Step 1: Isolate a generic group-cardinality lemma

Prove a reusable finite-cardinality lemma for additive groups with an identity component and component quotient.

Desired schematic statement:

```lean
import Mathlib

noncomputable section

open scoped Classical

namespace RealTorsionCardinality

/-- Schematic only.  Replace `ComponentQuotient` and hypotheses with actual Mathlib/repo APIs. -/
theorem torsion_card_le_of_circle_identity_component_and_two_components
    {G G0 C : Type*} [AddCommGroup G] [AddCommGroup G0] [AddCommGroup C]
    (m : ℕ) (hm : 0 < m)
    -- `G0` embeds as the identity component of `G`
    -- component map `G →+ C`, kernel = image of `G0`
    -- `#G0[m] ≤ m`
    -- `#C ≤ 2`
    : True := by
  trivial

end RealTorsionCardinality
```

Replace the schematic placeholders with actual definitions.  The proof should be a fiber-counting argument:

```text
map G[m] to the component group C;
there are at most 2 component fibers;
each fiber is a coset of G0[m], hence has at most m elements;
therefore #G[m] ≤ 2m.
```

### Step 2: Prove the circle `m`-torsion count

Target helper:

```lean
import Mathlib

noncomputable section

open scoped Classical

namespace RealTorsionCardinality

theorem addCircle_mTorsion_ncard
    (m : ℕ) (hm : 0 < m) :
    Set.ncard {x : AddCircle | m • x = 0} = m := by
  -- Suggested route:
  -- 1. define an additive monoid/group hom `ZMod m →+ AddCircle` sending `k` to `k/m mod 1`;
  -- 2. prove its range is exactly `{x | m • x = 0}`;
  -- 3. prove injectivity using representatives modulo `m`;
  -- 4. transfer `Fintype.card (ZMod m) = m` to `Set.ncard`.
  sorry

end RealTorsionCardinality
```

A `UnitAddCircle` or complex-roots-of-unity proof is equally acceptable if it compiles cleanly and is shorter.

### Step 3: Connect real elliptic curves to the circle/component lemma

Prefer an existing Mathlib/repo theorem that directly classifies `E(ℝ)` or bounds its components.  If one exists, use it.

If not, add a helper theorem proving enough of the real-locus structure.  The helper may live in `RealTorsionBound.lean` if it is only used there, or in a new imported file if the proof is large.

The result needed by the final theorem can be any one of these equivalent forms:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

-- Option A: direct split classification.
theorem real_points_split_circle_or_circle_two
    (E : WeierstrassCurve Q) [E.IsElliptic] :
    (Nonempty ((E/R).Point ≃+ AddCircle)) ∨
      (Nonempty ((E/R).Point ≃+ AddCircle × ZMod 2)) := by
  sorry

-- Option B: direct cardinal theorem for real torsion.
theorem real_points_mTorsion_card_le_from_components
    (m : N) (hm : 0 < m) (E : WeierstrassCurve Q) [E.IsElliptic] :
    Set.ncard {P : (E/R).Point | (m : N) * P = 0} <= 2 * m := by
  sorry
```

Option B is fine as an internal helper, but the public declaration must still be named `real_mTorsion_card_le`.

### Step 4: Replace the target axiom

Final theorem should be in the file where the axiom currently lives:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

-- preserve existing namespace

theorem real_mTorsion_card_le
    (m : N) (hm : 0 < m) (E : WeierstrassCurve Q) [E.IsElliptic] :
    Set.ncard {P : (E/R).Point | (m : N) * P = 0} <= 2 * m := by
  -- call the component/circle proof developed above
  exact real_points_mTorsion_card_le_from_components m hm E
```

Adjust the final line to the actual helper theorem and implicit arguments.

## Important constraints

Do not introduce any new custom axiom.  In particular, these are not acceptable:

```lean
import Mathlib

axiom real_points_split_circle_or_circle_two : True
axiom real_mTorsion_card_le : True
```

Do not hide the result behind `constant`, `opaque`, `unsafe`, `by native_decide` on noncomputable propositions, or a theorem imported from a new file that itself uses an axiom for the same mathematical content.

Existing project axioms unrelated to this theorem may remain untouched, but the proof of `real_mTorsion_card_le` must not depend on a newly introduced axiom or on the old `real_mTorsion_card_le` axiom under another name.

## Acceptance criteria

The task is complete only when all of the following hold.

1. `real_mTorsion_card_le` is a theorem/proved declaration, not an axiom.
2. There is no `sorry`, `admit`, or `by_cases h : False`-style fake proof in any code added or modified for this task.
3. No new custom axiom, constant, or opaque proof artifact is introduced.
4. The target file compiles:

```bash
lake env lean path/to/the/file/containing/real_mTorsion_card_le.lean
```

5. The relevant module or whole project builds cleanly enough to validate the change:

```bash
lake build
```

If `lake build` is too large for the environment, at minimum run the target module and every new helper file with `lake env lean`, then document exactly what was run.

6. This check finds no remaining axiom declaration for the target name:

```bash
grep -R "axiom real_mTorsion_card_le" -n FLT FermatsLastTheorem scratch || true
```

7. This check finds no newly introduced sorry/admit in modified Lean files:

```bash
git diff --name-only | grep '\.lean$' | xargs -r grep -n "sorry\|admit"
```

## Notes for Codex

* The mathematical heart is the real Lie-group classification of elliptic-curve real points, not division-polynomial root counting.
* `#E(ℝ)[m] ≤ 2m` follows immediately from `E(ℝ) ≅ S¹` or `S¹ × ℤ/2`; use this if Mathlib already exposes the classification.
* If Mathlib has only lower-level topology, prove the minimum component/fiber-counting statement needed for torsion rather than formalizing an unnecessarily broad classification theorem.
* Keep theorem names small and local unless they are genuinely reusable.
* Preserve existing notation aliases (`N`, `Q`, `R`, `/` base-change notation, `(E/R).Point`) exactly as found in the repository.
