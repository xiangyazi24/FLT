# Q1222 (dm1): Codex dispatch spec — prove `real_mTorsion_card_le`

## Mission

Work in the local repo checkout:

```bash
cd ~/repos/flt-ai
```

Create exactly one new Lean file:

```text
FLT/Assumptions/MazurProof/RealTorsionProof.lean
```

Do not edit existing files. Do not add axioms, `constant`s, `opaque` declarations, `unsafe` declarations, `sorry`, `admit`, or `by native_decide` hacks. The new file must compile with `lake env lean` and must import the existing torsion-definition file.

## Required import header

Start the new file with this import. Add extra Mathlib imports only if needed by the proof.

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Group.AddCircle
```

Use the same namespace conventions already used in `FLT/Assumptions/MazurProof/TorsionDefs.lean`. If that file is namespace-free, keep this file namespace-free too.

If the local checkout does not contain `FLT/Assumptions/MazurProof/TorsionDefs.lean`, stop: do **not** create a shim or replacement. The import path above is part of the task contract.

## Target theorem

The mathematical target is:

> For an elliptic curve `E : WeierstrassCurve ℚ`, the real `m`-torsion has cardinal at most `2 * m`.

The Lean statement must use additive scalar multiplication, not multiplication:

```lean
(m : ℕ) • P = 0
```

not

```lean
m * P = 0
```

The theorem must include a positivity hypothesis on `m`. Without `0 < m`, the statement is false at `m = 0`, because the `0`-torsion condition is all of `E(ℝ)`.

Preferred theorem shape, unless `TorsionDefs.lean` already defines an exact target name/type that should be reused:

```lean
noncomputable section

open scoped Classical
open WeierstrassCurve

/-- Real elliptic-curve `m`-torsion has at most `2 * m` points. -/
theorem real_mTorsion_card_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (m : ℕ) (hm : 0 < m) :
    Nat.card {P : (E⁄ℝ).Point // (m : ℕ) • P = 0} ≤ 2 * m := by
  -- proof here
```

If `TorsionDefs.lean` already defines an abbreviation such as `real_mTorsion E m`, use that abbreviation in the theorem statement if doing so matches the project’s expected public API. For example:

```lean
-- Use only if this is the existing local API.
theorem real_mTorsion_card_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (m : ℕ) (hm : 0 < m) :
    Nat.card (real_mTorsion E m) ≤ 2 * m := by
  -- proof here
```

Before writing the proof, run local probes to discover the exact names exported by `TorsionDefs.lean`:

```lean
import FLT.Assumptions.MazurProof.TorsionDefs

#check WeierstrassCurve
#check UnitAddCircle
#check AddCircle.card_torsion_le_of_isSMulRegular
#check AddCircle.finite_torsion
#check ZMod.toAddCircle
#check ZMod.toAddCircle_injective
-- Also try these; keep whichever names exist locally.
#check real_mTorsion
#check real_mTorsion_card_le
```

If `real_mTorsion_card_le` is already declared in `TorsionDefs.lean` as an axiom or theorem with `sorry`, do not create a duplicate declaration with the same name. Instead, prove the same statement in the new file under the temporary name `real_mTorsion_card_le_proved`, with a comment explaining that the existing declaration should be replaced in a follow-up patch. The preferred outcome is still a public theorem named `real_mTorsion_card_le` if no conflicting declaration exists.

## Mathematical proof plan

Prove either of the following. Option A is preferred, but Option B is acceptable and usually easier.

### Option A: construct an explicit injection

Construct an injection

```lean
{P : (E⁄ℝ).Point // (m : ℕ) • P = 0} ↪ Fin 2 × ZMod m
```

and finish by cardinality:

```lean
have hcard : Nat.card (Fin 2 × ZMod m) = 2 * m := by
  -- use `Nat.card_prod`, `Nat.card_fin`, and the local `ZMod` cardinal theorem
  -- likely `ZMod.card` or `Nat.card_zmod`, depending on the local Mathlib version
  ...
exact (Nat.card_le_card_of_injective f f.injective).trans_eq hcard
```

The injection is conceptually:

```text
P ↦ (real connected component of P, circle m-torsion coordinate inside that component)
```

The component coordinate lands in `Fin 2` because `E(ℝ)` has at most two connected components. The circle coordinate lands in `ZMod m` because each connected component is a torsor for the identity component, and the identity component is a circle whose `m`-torsion is `ZMod m`.

### Option B: prove the cardinal bound directly

Partition the torsion subtype by connected component:

```text
T_i = {P : E(ℝ)[m] | componentIndex P = i},  i : Fin 2
```

For each `i : Fin 2`:

* If `T_i` is empty, `Nat.card T_i = 0 ≤ m`.
* If `T_i` is nonempty, choose `P₀ : T_i`. The map

```text
P ↦ P - P₀
```

injects `T_i` into the `m`-torsion of the identity component, because:

```lean
m • (P - P₀) = m • P - m • P₀ = 0 - 0 = 0
```

and because two points in the same connected component differ by an element of the identity component.

Use the additive-circle theorem to show the identity-component `m`-torsion has at most `m` elements. Then sum over the two component indices:

```text
Nat.card E(ℝ)[m]
  = Σ i : Fin 2, Nat.card T_i
  ≤ Σ i : Fin 2, m
  = 2 * m
```

This direct proof is accepted even if it never packages the result as a single injection into `Fin 2 × ZMod m`.

## Existing Mathlib facts to use

Use Mathlib’s additive circle API. The relevant imported files are:

```lean
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Group.AddCircle
```

Important names to try first:

```lean
#check UnitAddCircle
#check AddCircle.card_torsion_le_of_isSMulRegular
#check AddCircle.finite_torsion
#check ZMod.toAddCircle
#check ZMod.toAddCircle_injective
#check ZMod.toAddCircle_inj
```

`Mathlib.Topology.Instances.AddCircle.Real` defines `UnitAddCircle` as `AddCircle (1 : ℝ)` and provides the map `ZMod.toAddCircle : ZMod N →+ UnitAddCircle` with injectivity lemmas for positive `N`. Use these rather than defining a new circle model.

A useful local lemma to prove early is:

```lean
private lemma unitAddCircle_mtorsion_card_le (m : ℕ) (hm : 0 < m) :
    Nat.card {x : UnitAddCircle // (m : ℕ) • x = 0} ≤ m := by
  -- Route 1: use `AddCircle.card_torsion_le_of_isSMulRegular` and convert `encard` to `Nat.card`.
  -- Route 2: construct an injection into `ZMod m` using `ZMod.toAddCircle_injective`.
  -- Prefer the route that is shortest in the local Mathlib version.
  ...
```

For Route 1, the key regularity fact over `ℝ` is that natural-number scalar multiplication by positive `m` is injective on `ℝ`:

```lean
have hreg : IsSMulRegular ℝ m := by
  -- likely available as `.of_right_eq_zero_of_smul`, or derivable from `nsmul_eq_zero` over `ℝ`
  ...
have henc : ({x : AddCircle (1 : ℝ) | (m : ℕ) • x = 0} : Set (AddCircle (1 : ℝ))).encard ≤ m := by
  exact AddCircle.card_torsion_le_of_isSMulRegular (p := (1 : ℝ)) m hm.ne' hreg
```

Then convert the set version to the subtype version. Use local theorem search for the exact conversion lemmas:

```lean
#check Set.Finite.to_subtype
#check Nat.card_eq_fintype_card
#check ENat.card_eq_coe_natCard
#check Set.encard_eq_coe_toFinset_card
```

## Real elliptic-curve component API to find or derive

Search the imported FLT/Mathlib files for existing real-elliptic component facts before proving anything from scratch:

```bash
grep -R "connectedComponent\|ConnectedComponent\|componentIndex\|UnitAddCircle\|AddCircle\|real.*component\|Real.*component" \
  FLT Mathlib .lake/packages/mathlib/Mathlib 2>/dev/null | head -200
```

The proof needs the following conceptual API. Use existing names if present; otherwise prove local private lemmas from existing Mathlib facts.

```lean
-- Schematic only: do not paste these exact names unless they exist or you define them locally.
componentIndex : (E⁄ℝ).Point → Fin 2
same_component_iff_sub_mem_identity_component :
  componentIndex P = componentIndex Q ↔ P - Q ∈ identityComponent E
identityComponent_addEquiv_unitAddCircle :
  identityComponent E ≃+ UnitAddCircle
```

The exact representation of the identity component may differ. It may be a subgroup, an additive subgroup, a connected component subtype, or a bundled topological subgroup. Use the representation already present in `TorsionDefs.lean` or nearby files.

Do **not** assume the whole group `E(ℝ)` is finite. It is not. Only the `m`-torsion is finite for `m > 0`.

## Implementation details and lemmas

### Torsion subtype

It is often helpful to define a local abbreviation if one is not already available:

```lean
private abbrev RealPoint (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ] :=
  (E⁄ℝ).Point

private abbrev RealMTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (m : ℕ) :=
  {P : RealPoint E // (m : ℕ) • P = 0}
```

Keep these `private` if the project already has public names.

### Difference of two torsion points

Use additive-group simp lemmas. A local lemma like this should be easy:

```lean
private lemma nsmul_sub_eq_zero_of_mem_mtorsion
    {G : Type*} [AddCommGroup G] {m : ℕ}
    {P Q : G} (hP : (m : ℕ) • P = 0) (hQ : (m : ℕ) • Q = 0) :
    (m : ℕ) • (P - Q) = 0 := by
  rw [nsmul_sub, hP, hQ, sub_self]
```

### Fiber injection into identity-component torsion

For a fixed component `i` and chosen base point `P₀` in that fiber, define:

```text
P ↦ P - P₀
```

The codomain should be the identity-component `m`-torsion subtype. Prove:

* it lands in the identity component because `P` and `P₀` are in the same component;
* it is `m`-torsion by `nsmul_sub_eq_zero_of_mem_mtorsion`;
* it is injective by subtract-cancellation/add-cancellation in an additive group.

This avoids having to define canonical circle coordinates on every component.

### Identity-component circle torsion

Transport identity-component torsion across the additive equivalence/homeomorphism to `UnitAddCircle`, then use `unitAddCircle_mtorsion_card_le`.

If the identity-component equivalence is only a homeomorphism, confirm it also preserves addition. The proof needs an additive equivalence or at least an injective additive map preserving `m • x = 0`.

## Expected file shape

The final file should look roughly like this; the middle lemmas will depend on the actual local API.

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Group.AddCircle

noncomputable section

open scoped Classical
open WeierstrassCurve

-- Use the namespace from `TorsionDefs.lean`, if any.

private lemma nsmul_sub_eq_zero_of_mem_mtorsion
    {G : Type*} [AddCommGroup G] {m : ℕ}
    {P Q : G} (hP : (m : ℕ) • P = 0) (hQ : (m : ℕ) • Q = 0) :
    (m : ℕ) • (P - Q) = 0 := by
  rw [nsmul_sub, hP, hQ, sub_self]

private lemma unitAddCircle_mtorsion_card_le (m : ℕ) (hm : 0 < m) :
    Nat.card {x : UnitAddCircle // (m : ℕ) • x = 0} ≤ m := by
  -- Fill using `AddCircle.card_torsion_le_of_isSMulRegular` or `ZMod.toAddCircle_injective`.
  ...

/-- Real elliptic-curve `m`-torsion has at most `2 * m` points. -/
theorem real_mTorsion_card_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (m : ℕ) (hm : 0 < m) :
    Nat.card {P : (E⁄ℝ).Point // (m : ℕ) • P = 0} ≤ 2 * m := by
  classical
  -- Either construct an injection into `Fin 2 × ZMod m`,
  -- or partition by the two connected components and bound each fiber by `m`.
  ...
```

Replace the `...` with actual proofs. The committed file must contain no `...` placeholders.

## Acceptance checks

Run all of these from `~/repos/flt-ai`:

```bash
lake env lean FLT/Assumptions/MazurProof/RealTorsionProof.lean
```

Check the new file contains no placeholders or new axioms:

```bash
! grep -nE 'sorry|admit|axiom|constant|opaque|unsafe|\.\.\.' FLT/Assumptions/MazurProof/RealTorsionProof.lean
```

Check the theorem’s axioms. Create a temporary file outside the repo, for example `/tmp/check_real_torsion.lean`:

```lean
import FLT.Assumptions.MazurProof.RealTorsionProof
#print axioms real_mTorsion_card_le
```

Then run:

```bash
lake env lean /tmp/check_real_torsion.lean
```

The only allowed axioms in the `#print axioms` output are:

```text
propext
Classical.choice
Quot.sound
```

No additional axioms are accepted.

## Non-goals

* Do not prove a statement over an arbitrary field.
* Do not use division polynomials for this task.
* Do not weaken the target to `Set.Finite`; the target is the explicit cardinal bound `≤ 2 * m` over `ℝ`.
* Do not introduce assumptions like “`E(ℝ)` has two components” as axioms. Use existing Mathlib/FLT theorems or prove local lemmas from existing theorems.
* Do not create or edit any file other than `FLT/Assumptions/MazurProof/RealTorsionProof.lean`.
