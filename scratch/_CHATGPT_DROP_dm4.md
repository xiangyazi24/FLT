# Q1196 (dm4): proving `#E(ℝ)[m] ≤ 2m` via Weierstrass parametrization / compact group structure

## Executive answer

I do **not** think the Weierstrass-`℘` route is shorter in Lean unless the `℘`-uniformization theorem itself is admitted as a large axiom.

The group-structure route is conceptually right:

```text
E(ℝ) is a compact 1-dimensional abelian Lie group
⇒ E(ℝ) ≃ S¹ or S¹ × Z/2Z
⇒ #E(ℝ)[m] ≤ 2m.
```

But Mathlib does not currently give a ready theorem of the form

```lean
compact_one_dimensional_abelian_lie_group_equiv_circle_times_finite
```

nor a theorem of the form

```lean
compact_connected_one_manifold_homeomorphic_circle
```

that can be imported and applied to real elliptic curves.  The local analytic API exists — in particular the implicit function theorem — but the global classification/topological-group bridge is not available as a ready-made theorem.

So the recommended FLT architecture remains:

```lean
real_mTorsion_finite
real_mTorsion_card_le
```

as the public Route 4B axioms, with `real_mTorsion_card_le` stated directly as the real torsion bound.  A future proof can use either Weierstrass uniformization or real Lie-group topology internally, but `Axioms.lean` should not depend on the internal route.

## Weierstrass `℘` route: what it would require

The analytic parametrization theorem is not just the formula

```text
t ↦ (℘(t), ℘'(t)).
```

To use it for the real torsion bound, one needs a package like:

```text
1. Define a lattice Λ ⊂ ℂ attached to E.
2. Define ℘_Λ and ℘'_Λ with convergence/meromorphicity.
3. Prove the differential equation:
     (℘')² = 4℘³ - g₂℘ - g₃.
4. Prove the addition formula, so the parametrization is a group homomorphism.
5. Prove the induced map ℂ/Λ → E(ℂ) is a group isomorphism.
6. Identify the real locus inside ℂ/Λ.
7. Classify the real locus as one or two circles.
8. Count the `m`-torsion points in those real circles.
```

This is essentially the full complex-analytic theory of elliptic curves.  If Mathlib had all of this, it would be excellent, but it is not a small shortcut.

A minimal admitted theorem could look like this:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/--
Uniformization/topological classification package for real elliptic curves.
This is the theorem one would prove using the Weierstrass `℘`-function or real
Lie-group topology.
-/
axiom realPoints_circle_or_two_circles
    (E : WeierstrassCurve ℝ) [E.IsElliptic] :
    True
    -- intended shape:
    -- Nonempty (E(ℝ) ≃+ AddCircle 1) ∨
    -- Nonempty (E(ℝ) ≃+ AddCircle 1 × ZMod 2)

end RealTorsionBound

end FLT
```

But once the theorem is this high-level, it is cleaner to state the exact theorem needed by the FLT reduction:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/--
Public Route 4B theorem: real `m`-torsion on an elliptic curve has at most `2m`
points.  This is the precise statement needed downstream.
-/
axiom real_mTorsion_card_le
    (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
    Nat.card (E.nTorsion m) ≤ 2 * m

end RealTorsionBound

end FLT
```

That is the better public API.

## Can we avoid `℘` and use compact abelian group structure?

Mathematically, yes.  Formally, not cheaply.

The proof outline is:

```text
1. The real affine curve y² = f(x) is a smooth 1-manifold away from infinity.
2. The point at infinity has a smooth chart using a local parameter such as `u = -x/y`.
3. The projective real cubic is compact.
4. The chord-tangent group law is continuous, indeed smooth.
5. Therefore E(ℝ) is a compact 1-dimensional abelian Lie group.
6. A compact connected 1-dimensional Lie group is S¹.
7. A compact 1-dimensional abelian Lie group has finitely many components, and for a real elliptic curve the component group has order at most 2.
8. Therefore E(ℝ) is either S¹ or S¹ × Z/2Z.
9. Hence `#E(ℝ)[m] ≤ 2m`.
```

This avoids `℘`, but it does **not** avoid serious topology.  In Lean, steps 1 and 4 are local calculus/algebra; steps 2, 3, 6, and 7 are the hard global topology/classification pieces.

## Exact Mathlib API names that do exist

Mathlib does have an implicit function theorem API.  The important names are in:

```lean
import Mathlib.Analysis.Calculus.Implicit
```

The exact names visible in the current Mathlib source include:

```lean
import Mathlib.Analysis.Calculus.Implicit

-- Main structure for the general implicit function theorem:
#check ImplicitFunctionData

-- The implicit function attached to the data:
#check ImplicitFunctionData.implicitFunction

-- The associated open partial homeomorphism:
#check ImplicitFunctionData.toOpenPartialHomeomorph

-- The differentiability theorem for the implicit function:
#check ImplicitFunctionData.hasStrictFDerivAt_implicitFunction

-- Eventual equations for the implicit function:
#check ImplicitFunctionData.leftFun_implicitFunction
#check ImplicitFunctionData.rightFun_implicitFunction
#check ImplicitFunctionData.prodFun_implicitFunction

-- Complemented-kernel version:
#check HasStrictFDerivAt.implicitFunctionDataOfComplemented
#check HasStrictFDerivAt.implicitFunctionOfComplemented
#check HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented

-- Finite-dimensional codomain version:
#check HasStrictFDerivAt.implicitToOpenPartialHomeomorph
#check HasStrictFDerivAt.implicitFunction

-- The file documentation also points to this version for a Cⁿ equation
-- `f : E × F → G` with invertible partial derivative in the second variable:
#check ContDiffAt.implicitFunction
```

So for local smoothness of a real affine Weierstrass curve, Mathlib has the right **local** tool.

For example, away from points where `∂F/∂y ≠ 0`, with

```text
F(x,y) = y² - f(x),
```

one can locally solve for `y` as a smooth function of `x`.  Away from points where `∂F/∂x ≠ 0`, one can locally solve for `x` as a smooth function of `y`.  At a nonsingular point, one of these partials is nonzero.

The schematic Lean target would be:

```lean
import Mathlib
import Mathlib.Analysis.Calculus.Implicit

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/-- Schematic local chart theorem for an affine smooth plane curve. -/
theorem local_chart_of_regular_level_set_schematic
    {F : ℝ × ℝ → ℝ} {P : ℝ × ℝ}
    (hF_smooth : ContDiffAt ℝ ⊤ F P)
    (hregular : fderiv ℝ F P ≠ 0) :
    True := by
  -- Intended proof uses `ContDiffAt.implicitFunction` or the stricter
  -- `HasStrictFDerivAt.implicitFunction` API after selecting a nonzero partial.
  trivial

end RealTorsionBound

end FLT
```

This is only the beginning; it does not classify the global real point group.

## Mathlib API names that I do **not** find as ready theorem statements

I do **not** know of ready Mathlib declarations with these contents:

```lean
-- not found / not available as a ready theorem:
#check compact_connected_one_manifold_homeomorphic_circle

-- not found / not available as a ready theorem:
#check compact_one_manifold_finite_disjoint_union_circles

-- not found / not available as a ready theorem:
#check compact_abelian_lie_group_equiv_torus_times_finite

-- not found / not available as a ready theorem:
#check compact_connected_one_dimensional_lie_group_equiv_circle

-- not found / not available as a ready theorem:
#check real_elliptic_curve_points_equiv_circle_or_circle_prod_zmod_two
```

These names are illustrative non-existing names: they express exactly the theorems one would want.  The point is that the global classification layer is missing as a ready API.

Mathlib has manifold infrastructure, but that is different from having the classification theorem already formalized.  The available infrastructure includes concepts such as:

```lean
import Mathlib

#check ChartedSpace
#check ModelWithCorners
#check SmoothManifoldWithCorners
#check ContMDiff
```

These are building blocks, not the final classification of compact one-manifolds or compact abelian Lie groups.

## Counting torsion once the group is known

If one had a group equivalence

```text
E(ℝ) ≃+ S¹
```

or

```text
E(ℝ) ≃+ S¹ × Z/2Z,
```

then the torsion bound is easy.  The proof becomes pure group/cardinality theory.

The relevant public theorem should not expose the topological proof.  It should be:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/-- Direct real-torsion bound, independent of proof method. -/
axiom real_mTorsion_card_le
    (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
    Nat.card (E.nTorsion m) ≤ 2 * m

end RealTorsionBound

end FLT
```

Internally, a future proof might use either:

```text
A. Weierstrass uniformization and real period classification;
B. real compact Lie group / one-manifold classification;
C. an elementary real cubic oval parametrization plus covering-degree argument.
```

But the downstream FLT code should see only `real_mTorsion_card_le`.

## Why the compact group route is still heavy

The compact group theorem you want is mathematically standard, but it is not a simple consequence of a generic compact abelian group structure theorem.

A compact abelian group need not be a torus times a finite group.  General compact abelian groups can be much wilder.  You need **compact abelian Lie group**, or at least compact abelian group plus a finite-dimensional smooth manifold structure.

So the route is really:

```text
E(ℝ) is a compact abelian Lie group of dimension 1
⇒ identity component is a 1-dimensional compact connected abelian Lie group
⇒ identity component is S¹
⇒ component group has size 1 or 2 for a real elliptic curve
⇒ #m-torsion ≤ 2m.
```

The phrase “structure theorem for compact abelian groups” is too broad and false in this naive form.  The correct theorem is for compact abelian **Lie** groups.

## The most Lean-friendly real-topology axiom

The best axiom is not “`E(ℝ)` is `S¹` or `S¹ × Z/2`”.  That exposes too much irrelevant structure.

Use exactly what the proof needs:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/--
Hard real-topological input for Route 4B.

Mathematically, this follows from the classification of the real points of an
elliptic curve as one or two circles, or from Weierstrass uniformization.
-/
axiom real_mTorsion_card_le
    (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
    Nat.card (E.nTorsion m) ≤ 2 * m

/-- Finiteness is a separate axiom only if the downstream cardinal API needs it. -/
axiom real_mTorsion_finite
    (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
    Finite (E.nTorsion m)

end RealTorsionBound

end FLT
```

Then keep the existing Route 4B theorem:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/--
Route 4B target theorem.  The proof is cardinality comparison once the real
`m`-torsion bound is available.
-/
theorem fullRationalTorsion_order_le_two_route4B
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  -- Existing proof in `RealTorsionBound.lean` should remain the implementation.
  -- It uses `real_mTorsion_finite` and `real_mTorsion_card_le`.
  sorry

end RealTorsionBound

end FLT
```

The `sorry` here is only schematic in this drop; you said the actual theorem in `RealTorsionBound.lean` is already sorry-free from the two axioms.

## Final recommendation

Do not try to build `℘` for this step.

Do not try to formalize the full compact-abelian-Lie-group classification just to prove `#E(ℝ)[m] ≤ 2m`.

For the current FLT architecture, keep the direct Route 4B real torsion bound as the hard interface:

```text
real_mTorsion_finite
real_mTorsion_card_le
```

This is the most honest and smallest public axiom footprint.  Later, if someone wants to remove those axioms, the likely internal proof can use the IFT API listed above for local charts, plus a substantial new global theorem classifying real elliptic curves as one or two circles.
