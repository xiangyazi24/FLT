# Q1318 (dm4): minimal axiom for real odd torsion over `ℝ`

## Executive answer

For the Mazur-torsion obstruction, the **minimal axiom** is the direct cardinal bound on real `p`-torsion.  You do **not** need to axiomatize the full real Lie-group/classification theorem

```text
E(ℝ) ≃ UnitAddCircle × ZMod k,  k ∈ {1, 2}.
```

That structure theorem is much stronger than the downstream proof needs.  If the only target is

```lean
{P : (E⁄ℝ).Point | p • P = 0}.Finite
Nat.card {P : (E⁄ℝ).Point // p • P = 0} ≤ 2 * p
```

then axiomatize exactly that.  This is the narrowest theorem boundary and is also the best dependency boundary for Lean.

The full `AddCircle × ZMod k` route is mathematically natural, but it imports a large real-topology/uniformization theorem that Mathlib does not currently provide for elliptic curves.

## Recommended axiom boundary

Use a direct axiom returning both finiteness and the cardinal inequality.  Do **not** state only a bare `Nat.card ≤ 2 * p` unless you separately know finiteness; `Nat.card` is less robust as a standalone finiteness witness.  A conjunction is the most convenient downstream interface.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsion

/-- The real `p`-torsion set of an elliptic curve. -/
def realPTorsionSet (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) :
    Set (E⁄ℝ).Point :=
  {P | p • P = 0}

/-- The real `p`-torsion subtype. -/
abbrev RealPTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) : Type :=
  {P : (E⁄ℝ).Point // p • P = 0}

/--
Minimal real-topology input for the Mazur odd-torsion obstruction.

Mathematically this follows from the classification
`E(ℝ) ≃ ℝ/ℤ` or `E(ℝ) ≃ ℝ/ℤ × ℤ/2ℤ`, but the classification is deliberately
not part of the Lean dependency surface here.
-/
axiom real_odd_torsion_finite_card_le_two_mul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    (realPTorsionSet E p).Finite ∧
      Nat.card (RealPTorsion E p) ≤ 2 * p

/-- Finiteness projection from the minimal axiom. -/
theorem real_odd_torsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    (realPTorsionSet E p).Finite :=
  (real_odd_torsion_finite_card_le_two_mul
    (E := E) (p := p) hp hpgt).1

/-- Cardinal bound projection from the minimal axiom. -/
theorem real_odd_torsion_card_le_two_mul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Nat.card (RealPTorsion E p) ≤ 2 * p :=
  (real_odd_torsion_finite_card_le_two_mul
    (E := E) (p := p) hp hpgt).2

end FLT.RealTorsion
```

This is the theorem you actually need.  It is also easy to swap later for a proved theorem if a real-elliptic-curve topology file is added.

## Even smaller, if you like `encard`

Mathlib's `AddCircle.card_torsion_le_of_isSMulRegular` is phrased with `encard`:

```lean
#check AddCircle.card_torsion_le_of_isSMulRegular
-- AddCircle.card_torsion_le_of_isSMulRegular
--   (n : ℕ) (h0 : n ≠ 0) (hn : IsSMulRegular 𝕜 n) :
--   {x : AddCircle p | n • x = 0}.encard ≤ n
```

So an even more cardinal-theoretic axiom is possible:

```lean
axiom real_odd_torsion_encard_le_two_mul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    (realPTorsionSet E p).encard ≤ (2 * p : ℕ)
```

This is logically compact: an `encard` bound by a finite natural number contains finiteness information.  But in practice, the conjunction

```lean
(realPTorsionSet E p).Finite ∧ Nat.card (RealPTorsion E p) ≤ 2 * p
```

is usually easier to consume in downstream elementary cardinal arguments.

## Why not axiomatize `E(ℝ) ≃ UnitAddCircle × ZMod k`?

You can, but it is not minimal.

A possible strong axiom would be:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Data.ZMod.Basic

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsion

/-- Strong global structure axiom for real elliptic-curve points.

This is far stronger than what the Mazur obstruction needs. -/
axiom real_points_addEquiv_addCircle_zmod_one_or_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      Nonempty ((E⁄ℝ).Point ≃+ UnitAddCircle × ZMod k)

end FLT.RealTorsion
```

From this, one can prove the direct torsion bound by transferring `p`-torsion across the additive equivalence and using the `AddCircle` torsion bound.  But that proof is extra work, and the axiom is much stronger than necessary.

There is also a middle option:

```lean
/-- Middle-strength axiom: only real `p`-torsion injects into the model torsion. -/
axiom real_odd_torsion_injects_into_circle_times_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Nonempty (RealPTorsion E p ↪
      {x : UnitAddCircle × ZMod 2 // p • x = 0})
```

But this is still not as clean as the direct bound, and it forces you to maintain an auxiliary product-torsion proof.

## What Mathlib has for `AddCircle`

At the FLT pinned Mathlib revision, the relevant API is narrow but useful.

`Mathlib/Topology/Instances/AddCircle/Defs.lean` defines

```lean
abbrev AddCircle [AddCommGroup 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p
```

and gives the torsion cardinal bound

```lean
theorem AddCircle.card_torsion_le_of_isSMulRegular
    (n : ℕ) (h0 : n ≠ 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard ≤ n
```

For `ℝ`, the regularity hypothesis is easy:

```lean
example (p : ℕ) (hp0 : p ≠ 0) :
    {x : UnitAddCircle | p • x = 0}.encard ≤ p := by
  exact AddCircle.card_torsion_le_of_isSMulRegular
    (p := (1 : ℝ)) p hp0
    (.of_right_eq_zero_of_smul fun x ↦ by simp [hp0])
```

`Mathlib/Topology/Instances/AddCircle/Real.lean` defines

```lean
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)

abbrev UnitAddTorus (d : Type*) :=
  d → UnitAddCircle
```

and provides, among other things,

```lean
instance AddCircle.pathConnectedSpace : PathConnectedSpace (AddCircle p)
instance AddCircle.compactSpace : CompactSpace (AddCircle p)

noncomputable def ZMod.toAddCircle : ZMod N →+ UnitAddCircle
lemma ZMod.toAddCircle_injective : Function.Injective (ZMod.toAddCircle : ZMod N → _)
```

This is enough for explicit circle torsion arguments **after** you already have a map/equivalence from `E(ℝ)` to the circle model.  It does not provide that map/equivalence.

## What Mathlib does not have

Mathlib has a general Lie-group class:

```lean
import Mathlib.Geometry.Manifold.Algebra.LieGroup

#check LieGroup
#check LieAddGroup
```

But this is only the differential-geometric typeclass infrastructure.  It is not a classification theorem for compact one-dimensional Lie groups.

Concretely, I would not expect to find any of the following already available:

```lean
-- Not currently available as a theorem/API boundary.
ERealIdentityComponent E ≃+ UnitAddCircle

-- Not currently available.
(E⁄ℝ).Point ≃+ UnitAddCircle

-- Not currently available.
(E⁄ℝ).Point ≃+ UnitAddCircle × ZMod 2

-- Not currently available.
compact_connected_one_dimensional_lie_group_equiv_circle
```

The `AddCircle` file itself still lists these as TODO-level infrastructure:

```text
TODO
* Link with periodicity
* Lie group structure
* Exponential equivalence to `Circle`
```

So even `UnitAddCircle` is not presently the endpoint of a full compact-Lie-group classification pipeline in Mathlib.

Likewise, I do not see a usable real algebraic-group API that would take a nonsingular real cubic, build its real Lie group of points, prove compactness/component structure, and identify it with `S¹ × finite`.  Mathlib has algebraic geometry and it has manifold/Lie-group infrastructure, but the bridge

```text
real algebraic curve → real Lie group → compact one-dimensional Lie group classification
```

is not there.

## Practical recommendation

For your FLT/Mazur formalization, use this as the axiom:

```lean
axiom real_odd_torsion_finite_card_le_two_mul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    (realPTorsionSet E p).Finite ∧
      Nat.card (RealPTorsion E p) ≤ 2 * p
```

Name it as a real-topology theorem, not as a group-classification theorem.  A good final name is:

```lean
real_odd_torsion_finite_card_le_two_mul
```

or, if you only expose the cardinal projection:

```lean
real_odd_torsion_card_le_two_mul
```

If later someone proves the real structure theorem, this axiom can be discharged without changing any downstream Mazur proof code.

## Mathematical note

The true odd-primary statement is slightly stronger than `≤ 2 * p`: for odd `p`, the `ZMod 2` component contributes no `p`-torsion, so the optimal real bound is `≤ p`.  The weaker `≤ 2 * p` is still enough to rule out a rational subgroup `(ZMod p)^2`, since `p^2 > 2p` for `p > 2`.
