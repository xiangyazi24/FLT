# Q1180 (dm1): concrete proof sketch for `real_mTorsion_card_le`

## Repo state checked

I read:

```text
FLT/EllipticCurve/Torsion.lean
```

It already has the two key ingredients needed by the B-line wrapper:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and

```lean
noncomputable def WeierstrassCurve.Points.map
    {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point :=
  WeierstrassCurve.Affine.Point.map f
```

I tried to read:

```text
FLT/Assumptions/MazurProof/RealTorsionBound.lean
```

on both `scratch` and `main`; the file was not found. I also searched for `RealTorsionBound`, `real_mTorsion_card_le`, and `MazurProof`, with no matching file visible to the connector.

## Bottom line

The division-polynomial route does not give the desired bound. The degree of the division polynomial gives a bound of order `m^2`, while the target is `2*m`. To improve the real-root count to `O(m)`, one must prove that multiplication by `m` on the real oval has degree `m`, or equivalently that the identity component of `E(ℝ)` is a circle group. That is the same real topology in another form.

The shortest useful Lean theorem boundary is therefore an injection

```text
E(ℝ)[m] ↪ Fin 2 × ZMod m.
```

Mathematically, the first coordinate is the connected component of the point, and the second coordinate is the circle `m`-torsion coordinate inside that component. Once this injection exists, the cardinal bound is immediate.

## Absolute minimum infrastructure

To construct the injection honestly, build one of these packages:

```text
A. Direct package:
   E(ℝ)[m] ↪ Fin 2 × ZMod m.

B. Structural package:
   component group has size ≤ 2,
   identity component has ≤ m points killed by m,
   each m-torsion component fiber is a torsor under identity-component m-torsion.

C. Analytic/topological package:
   E(ℝ)^0 ≃+ UnitAddCircle,
   and component group has size ≤ 2.
```

Package A is the smallest public API. Package B is the cleanest implementation target. Package C is the standard mathematical source. A full Weierstrass `℘` parametrization is not necessary if you can prove the identity-component torsion bound by compact connected one-dimensional abelian Lie group theory or by a direct covering-degree theorem for `[m]` on the real oval.

## Concrete Lean 4 proof sketch

This is the wrapper I would put in the missing `RealTorsionBound.lean` file. The only hard theorem is `realMTorsion_componentCircle_code`.

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT.RealTorsionBound

/-- Real points of a rational Weierstrass curve. -/
abbrev RealPoints (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  (E⁄ℝ).Point

/-- Real points killed by `m`. -/
abbrev RealMTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Type :=
  Submodule.torsionBy ℤ (RealPoints E) m

/-- Set version of the same object. -/
def realMTorsionSet (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) :
    Set (RealPoints E) :=
  {P | m • P = 0}

/--
Hard Route 4B input.

Construct this from:
* the component map `E(ℝ) → π₀(E(ℝ))`, with at most two values;
* the theorem `#E(ℝ)^0[m] ≤ m`;
* the fact that a nonempty fiber of `E(ℝ)[m]` over a component injects into
  `E(ℝ)^0[m]` by subtracting a chosen base point in that fiber.
-/
theorem realMTorsion_componentCircle_code
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m) :
    ∃ code : RealMTorsion E m → Fin 2 × ZMod m, Function.Injective code := by
  -- This is the real-topological work.
  -- It replaces the full Weierstrass parametrization by the minimal finite
  -- torsion coding needed for the B-line.
  sorry

/-- Cardinal bound for real `m`-torsion. -/
theorem real_mTorsion_card_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m) :
    Nat.card (RealMTorsion E m) ≤ 2 * m := by
  classical
  rcases realMTorsion_componentCircle_code (E := E) (m := m) hm with ⟨code, hcode⟩
  calc
    Nat.card (RealMTorsion E m)
        ≤ Nat.card (Fin 2 × ZMod m) :=
          Nat.card_le_card_of_injective code hcode
    _ = 2 * m := by
          haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
          -- If `simp` does not close at the pinned Mathlib revision, replace
          -- this with the local lemma `Nat.card (ZMod m) = m`.
          simp [Nat.card_prod]

/-- Set-`ncard` wrapper. The subtype of this set is `RealMTorsion E m`. -/
theorem real_mTorsion_set_ncard_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m) :
    (realMTorsionSet E m).ncard ≤ 2 * m := by
  classical
  -- Usual finishing pattern:
  --   change Nat.card {P : RealPoints E // P ∈ realMTorsionSet E m} ≤ 2 * m
  --   simpa [realMTorsionSet, RealMTorsion] using real_mTorsion_card_le (E := E) hm
  -- The exact `Set.ncard` subtype rewrite lemma may vary, so keep
  -- `real_mTorsion_card_le` as the primary API if possible.
  sorry

end FLT.RealTorsionBound
```

## Structural proof target for the hard input

If you want to avoid making `realMTorsion_componentCircle_code` a black box, prove these three lemmas instead:

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT.RealTorsionBound

abbrev RealPoints (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  (E⁄ℝ).Point

/-- Production version: the connected component of `0` in `E(ℝ)`. -/
-- def RealIdentityComponent ...

/-- Production version: the component quotient `π₀(E(ℝ))`. -/
-- def RealComponentGroup ...

/-- Hard topology from the real cubic: at most two real components. -/
theorem real_componentGroup_card_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    True := by
  -- Replace `True` by `Nat.card (RealComponentGroup E) ≤ 2`.
  trivial

/-- Hard group topology: the identity component has circle-like m-torsion. -/
theorem real_identityComponent_mTorsion_card_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m) :
    True := by
  -- Replace `True` by
  --   Nat.card (Submodule.torsionBy ℤ (RealIdentityComponent E) m) ≤ m.
  -- Prove this from `RealIdentityComponent E ≃+ UnitAddCircle`, or directly
  -- from `[m]` being an m-fold covering of the identity oval.
  trivial

/-- Group-theory step: component fibers are torsors under identity-component torsion. -/
theorem real_mTorsion_card_le_components
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m) :
    True := by
  -- Replace `True` by the inequality:
  --   #E(ℝ)[m] ≤ #π₀(E(ℝ)) * #E(ℝ)^0[m].
  -- For points P,Q in the same component fiber, P - Q lies in E(ℝ)^0[m].
  trivial

end FLT.RealTorsionBound
```

This structural split is the best implementation plan. It avoids complex uniformization but still contains the real topology that the theorem genuinely needs.

## Why the `℘` parametrization is not the minimum

Silverman's lattice argument proves the theorem cleanly on paper, but formalizing it would require:

```text
period lattice Λ,
Weierstrass ℘ and ℘',
the differential equation for ℘,
complex uniformization `ℂ/Λ ≃ E(ℂ)`,
classification of real points in the complex torus,
transport of the group law.
```

That is much larger than the B-line needs. For this project, the minimum is the finite real torsion coding theorem, not full analytic uniformization.

## Final recommendation

Create the missing file with the public theorem:

```lean
real_mTorsion_card_le
  (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 0 < m) :
  Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) ≤ 2*m
```

Prove it from the single hard input:

```lean
realMTorsion_componentCircle_code
  : E(ℝ)[m] ↪ Fin 2 × ZMod m.
```

Then separately build that hard input from component count plus identity-component circle torsion. Do not try to get the `2m` bound directly from `deg ψ_m`; the needed sharper real root count is equivalent in difficulty to the real oval/circle theorem.
