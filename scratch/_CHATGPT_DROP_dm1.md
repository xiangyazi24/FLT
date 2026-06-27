# Q1155 (dm1): Route 4B concrete — proving the real identity component is a circle

## Executive answer

The most elementary Lean route is **not** the proposed angle parametrization.  For a general nonsingular real Weierstrass cubic, the group-coordinate on the identity component is not an elementary trigonometric angle; it is an **Abel/elliptic integral coordinate**.  Proving that this coordinate is a group isomorphism requires the invariant differential and an addition theorem, or an equivalent compact connected one-dimensional Lie-group classification theorem.

So the key point is:

```text
IVT + IFT + compactness can plausibly prove that E(ℝ) is a compact 1-manifold
with one or two connected components.

But this is not enough to prove the torsion bound.

To prove #E(ℝ)[m] ≤ 2m, you need a group-theoretic circle statement:
  E(ℝ)^0 ≃+ ℝ/ℤ
or at least
  #(E(ℝ)^0[m]) ≤ m.
```

The shortest honest target theorem is therefore still the direct theorem:

```lean
real_mTorsion_card_le
  (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
  Nat.card (E.nTorsion m) ≤ 2 * m
```

Internally, prove it from a **minimal topological-group package**:

```text
1. E(ℝ)^0 is a compact connected 1-dimensional abelian Lie group.
2. Hence E(ℝ)^0 is additively isomorphic to AddCircle 1, i.e. ℝ/ℤ.
3. The component group E(ℝ)/E(ℝ)^0 has size ≤ 2.
```

If you do not want to build Lie groups, the honest alternative is the explicit Abel-map proof using elliptic integrals.  That is probably *more* work in Lean than a narrow `real_mTorsion_card_le` theorem.

## Repository and Mathlib API check

For the FLT repo, the relevant existing file is:

```text
FLT/EllipticCurve/Torsion.lean
```

It already provides:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and the point-map infrastructure:

```lean
noncomputable def WeierstrassCurve.Points.map
    {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point :=
  WeierstrassCurve.Affine.Point.map f
```

I did not find a dedicated real-locus file such as:

```text
FLT/EllipticCurve/Real.lean
FLT/EllipticCurve/RealTorsion.lean
```

so the real-topological theorem is not already packaged in FLT.

The project is pinned to Mathlib revision:

```text
96fd0fff3b8837985ae21dd02e712cb5df72ec05
```

At that revision, the relevant Mathlib API names are below.

## 1. Does Mathlib have IVT?

Yes.  Import:

```lean
import Mathlib.Topology.Order.IntermediateValue
```

Important names:

```lean
intermediate_value_univ
IsPreconnected.intermediate_value
intermediate_value_Icc
intermediate_value_Icc'
intermediate_value_uIcc
intermediate_value_Ioo
intermediate_value_Ioo'
isPreconnected_Icc
isConnected_Icc
```

For cubics over `ℝ`, the practical closed-interval theorem is:

```lean
intermediate_value_Icc
```

with shape:

```lean
theorem intermediate_value_Icc
    {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b
```

and the reversed endpoint version:

```lean
intermediate_value_Icc'
```

with conclusion:

```lean
Icc (f b) (f a) ⊆ f '' Icc a b
```

So IVT is available and usable for root-count/connectivity arguments for real cubics.

## 2. Does Mathlib have IFT?

Yes, but the API is Banach-space / Fréchet-derivative based.  Import:

```lean
import Mathlib.Analysis.Calculus.Implicit
```

Important names:

```lean
ImplicitFunctionData
ImplicitFunctionData.toOpenPartialHomeomorph
ImplicitFunctionData.implicitFunction
ImplicitFunctionData.hasStrictFDerivAt_implicitFunction
HasStrictFDerivAt.implicitToOpenPartialHomeomorph
HasStrictFDerivAt.implicitFunction
HasStrictFDerivAt.map_implicitFunction_eq
HasStrictFDerivAt.to_implicitFunction
```

For a nonsingular level set

```text
F(x, y) = 0,
```

with nonzero derivative in one coordinate, the finite-dimensional theorem you will probably use is:

```lean
HasStrictFDerivAt.implicitToOpenPartialHomeomorph
```

or:

```lean
HasStrictFDerivAt.implicitFunction
```

The source file also mentions the smoother version:

```lean
ContDiffAt.implicitFunction
```

for equations `f : E × F → G` with invertible partial derivative in the second variable.  Use this if you want a smooth local parametrization rather than only a topological local parametrization.

A schematic local-level-set code shape is:

```lean
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

open scoped Classical Topology

noncomputable section

namespace FLT.RealRoute4B

/-- Schematic polynomial equation for a short Weierstrass model. -/
def F (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 ^ 2 - (p.1 ^ 3 + a * p.1 + b)

/--
Target local chart statement.

At a nonsingular point where the derivative in `y` is nonzero, the real locus
`F a b = 0` is locally the graph of a function of `x`.
-/
theorem local_graph_where_dFdy_ne_zero
    (a b : ℝ) (p : ℝ × ℝ)
    (hp : F a b p = 0)
    (hy : (2 : ℝ) * p.2 ≠ 0) :
    True := by
  -- Actual proof route:
  -- 1. prove `HasStrictFDerivAt (F a b)` at `p`;
  -- 2. show the relevant derivative/partial derivative is surjective;
  -- 3. apply `HasStrictFDerivAt.implicitToOpenPartialHomeomorph` or
  --    `HasStrictFDerivAt.implicitFunction`.
  trivial

end FLT.RealRoute4B
```

This is enough for local manifold charts, but not enough for the group-isomorphism-to-circle theorem.

## 3. Does Mathlib have compactness of closed bounded sets?

Yes.  Imports:

```lean
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded
```

Important names:

```lean
CompactIccSpace
isCompact_Icc
isCompact_uIcc
isCompact_closedBall
IsCompact.isBounded
isCompact_of_isClosed_isBounded
isCompact_iff_isClosed_bounded
```

The Heine--Borel style theorem is:

```lean
isCompact_of_isClosed_isBounded
```

with shape:

```lean
theorem isCompact_of_isClosed_isBounded
    [ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) :
    IsCompact s
```

and the iff version:

```lean
isCompact_iff_isClosed_bounded
```

with shape:

```lean
theorem isCompact_iff_isClosed_bounded [T2Space α] [ProperSpace α] :
    IsCompact s ↔ IsClosed s ∧ IsBounded s
```

Closed intervals are handled by:

```lean
isCompact_Icc
```

and `CompactIccSpace`.

So, yes: Mathlib has the compactness/closed-bounded tools needed to prove compactness of bounded pieces, and closedness of zero loci can be obtained from continuity plus `isClosed_singleton` / `IsClosed.preimage` style lemmas.

## 4. Why IVT + IFT + compactness are not enough

They can plausibly prove this topological statement:

```text
E(ℝ) is a compact 1-dimensional smooth manifold with one or two components,
and each component is homeomorphic to a circle.
```

But the desired torsion bound is a **group** statement, not just a space statement.

A homeomorphism

```text
E(ℝ)^0 ≃ₜ S¹
```

only says the identity component is topologically a circle.  It does not say that multiplication-by-`m` has exactly `m` kernel points.  For that, you need a topological group isomorphism

```text
E(ℝ)^0 ≃+ AddCircle 1
```

or a theorem that the multiplication-by-`m` map on `E(ℝ)^0` is a degree-`m` covering map.

That requires at least one of the following extra inputs:

```text
A. classification of compact connected 1-dimensional abelian Lie groups;
B. explicit Abel/elliptic integral coordinate, proving the group law becomes addition modulo periods;
C. a direct covering-degree theorem for [m] on the real oval.
```

The proposed angle parametrization hides exactly this missing step.  For a circle defined by `x² + y² = 1`, the angle is elementary.  For a nonsingular cubic, the group parameter is not elementary angle; it is an elliptic integral.

## 5. The most elementary honest proof of `E(ℝ)^0 ≃+ ℝ/ℤ`

The least magical route is the Abel-map route.

For a real elliptic curve, let `ω` be the invariant differential.  On the identity component, define:

```text
u(P) = ∫_O^P ω
```

where the integral is taken along the real identity component.  The total period is:

```text
Ω = ∫ around E(ℝ)^0 ω > 0.
```

Then the map

```text
P ↦ u(P) mod Ωℤ
```

is a continuous group isomorphism:

```text
E(ℝ)^0 ≃+ ℝ / Ωℤ.
```

After rescaling by `Ω`, this is:

```text
E(ℝ)^0 ≃+ AddCircle 1.
```

But this is not a small proof.  It needs:

```text
1. invariant differential on a Weierstrass curve;
2. line/path integrals of that differential along real arcs;
3. proof that the integral coordinate is locally a chart;
4. proof that the integral coordinate respects the group law;
5. proof that the period lattice is rank one;
6. proof that the identity component is exactly one period cycle.
```

This is analytically honest, but it is not a quick Lean formalization.

The alternative is a general theorem from Lie groups:

```text
Every compact connected 1-dimensional abelian Lie group is isomorphic to AddCircle 1.
```

I do not see this as an existing ready-to-use Mathlib theorem for the pinned FLT revision.  Mathlib has `AddCircle` and covering-map infrastructure, but not a ready theorem classifying real elliptic-curve identity components as `AddCircle 1`.

## 6. Useful `AddCircle` API already in Mathlib

Imports:

```lean
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
```

Important names:

```lean
AddCircle
UnitAddCircle
UnitAddTorus
AddCircle.compactSpace
AddCircle.pathConnectedSpace
ZMod.toAddCircle
ZMod.toAddCircle_injective
ZMod.toAddCircle_inj
ZMod.toAddCircle_eq_zero
AddCircle.isCoveringMap_coe
AddCircle.isLocalHomeomorph_coe
AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero
```

The file `Mathlib.Topology.Instances.AddCircle.Real` gives:

```lean
abbrev UnitAddCircle := AddCircle (1 : ℝ)
```

and an injective map:

```lean
ZMod.toAddCircle : ZMod N →+ UnitAddCircle
```

with theorem:

```lean
ZMod.toAddCircle_injective : Function.Injective (ZMod.toAddCircle : ZMod N → _)
```

This is useful for the model calculation:

```text
#(UnitAddCircle[m]) = m.
```

Mathlib also has covering-map facts for `n • ·` on `AddCircle`, for example:

```lean
AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero
```

for nonzero `n`.

So once you can identify `E(ℝ)^0` with `UnitAddCircle` as a group, the torsion calculation is manageable.

## 7. Suggested public theorem boundary

Do **not** make the final FLT proof depend on elliptic integrals, ovals, IVT, IFT, and component arguments directly.  Hide all real analysis behind one theorem:

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

open scoped Classical Topology
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT.RealRoute4B

/--
Hard real theorem for Route 4B.

Recommended public API: do not expose the proof that the identity component is a
circle.  State exactly the torsion bound needed by the FLT argument.
-/
theorem real_mTorsion_card_le
    (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
    Nat.card (E.nTorsion m) ≤ 2 * m := by
  -- Internal proof options:
  -- 1. prove E(ℝ)^0 ≃+ UnitAddCircle and component group has size ≤ 2;
  -- 2. or prove directly that multiplication-by-m has kernel size ≤ 2m.
  sorry

end FLT.RealRoute4B
```

This theorem is the correct `Route 4B` endpoint.  The final rational torsion bound should use this theorem, not the underlying topological construction.

## 8. If you insist on proving the circle statement, target these lemmas

Use a deliberately narrow statement.  Avoid first developing a full smooth manifold API for real elliptic curves unless the project really needs it elsewhere.

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

open scoped Classical Topology
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT.RealRoute4B

/-- Placeholder for the identity component of the real elliptic curve. -/
def RealIdentityComponent (E : WeierstrassCurve ℝ) [E.IsElliptic] : Type :=
  {P : (E⁄ℝ).Point // True}

/-- Placeholder group structure; in production this is the connected component of `0`. -/
instance (E : WeierstrassCurve ℝ) [E.IsElliptic] :
    AddCommGroup (RealIdentityComponent E) := by
  -- Do not literally use this dummy instance.  The production definition should
  -- be the connected component subgroup of the topological group `(E⁄ℝ).Point`.
  infer_instance

/--
The real identity component is the additive circle.

This is the hard theorem if you choose the identity-component route.
-/
theorem real_identityComponent_addEquiv_addCircle
    (E : WeierstrassCurve ℝ) [E.IsElliptic] :
    Nonempty (RealIdentityComponent E ≃+ UnitAddCircle) := by
  -- Honest proof options:
  -- A. compact connected 1-dimensional abelian Lie group classification;
  -- B. explicit Abel/elliptic integral coordinate.
  sorry

/-- The component group has size at most two. -/
theorem real_componentGroup_card_le_two
    (E : WeierstrassCurve ℝ) [E.IsElliptic] :
    True := by
  -- Production statement should be a cardinal bound for
  -- `(E⁄ℝ).Point / connectedComponent(0)` or equivalent.
  -- This follows from the cubic having one or three real roots.
  trivial

end FLT.RealRoute4B
```

The dummy `RealIdentityComponent` above is intentionally schematic.  In production, it should be an actual subgroup/subtype built from the connected component of `0` in the topological group of real points.  The reason to show this sketch is to fix the dependency boundary: the hard theorem should be an additive equivalence to `UnitAddCircle`, not merely a homeomorphism.

## 9. Group-theoretic reduction once the circle theorem exists

After proving an additive equivalence with `UnitAddCircle`, the identity-component torsion calculation should be isolated as a general theorem.

```lean
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Tactic

open scoped Classical Topology

noncomputable section

namespace FLT.RealRoute4B

/--
Target theorem: the `m`-torsion of the additive circle has exactly `m` points.

This should be proved using `ZMod.toAddCircle`, `ZMod.toAddCircle_injective`,
and surjectivity onto the kernel of `m • ·` on `UnitAddCircle`.
-/
theorem unitAddCircle_mTorsion_card (m : ℕ) :
    Nat.card (Submodule.torsionBy ℤ UnitAddCircle m) = m := by
  -- Hard but much smaller than the elliptic-curve real-locus theorem.
  -- For `m = 0`, check the convention of `Submodule.torsionBy`; for the FLT
  -- application you can state this only under `0 < m`.
  sorry

/-- Transport torsion cardinality across an additive equivalence. -/
theorem torsion_card_of_addEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (m : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A m) =
      Nat.card (Submodule.torsionBy ℤ B m) := by
  -- Build the induced equivalence on `Submodule.torsionBy`.
  -- The proof is routine: map an element `a` to `e a` and use `map_nsmul`.
  sorry

end FLT.RealRoute4B
```

Then the real elliptic theorem becomes:

```text
#E(ℝ)[m]
  ≤ #(component group) * #(E(ℝ)^0[m])
  ≤ 2 * m.
```

The first inequality is an exact-sequence/cardinality lemma for the component map.  It is ordinary group theory once the component group is defined as a quotient and has cardinal at most two.

## 10. Is there a shortcut using the division polynomial `ψ_m`?

Not a useful one.

The naive division-polynomial bound gives:

```text
#x-coordinates of nonzero m-torsion ≤ deg ψ_m ≈ m²/2,
#points ≤ 2 deg ψ_m + 1 ≈ m²,
```

which is far too weak.

To improve it to `O(m)`, you would need to prove a strong theorem such as:

```text
ψ_m has at most about m/2 real roots on a one-component real elliptic curve,
and at most about m real roots on a two-component real elliptic curve.
```

But this is essentially the same real topology/torsion theorem in polynomial language.  The reason most roots of `ψ_m` are nonreal is that the real torus has only one or two real ovals; proving that via signs/Sturm theory for every `m` is not shorter than proving the real Lie-group picture.

A Sturm-theory route would require:

```text
1. a uniform Sturm sequence for ψ_m depending on m;
2. proof that the number of real roots is O(m);
3. compatibility between roots of ψ_m and real torsion points;
4. all exceptional cases around 2-torsion and point at infinity.
```

This is likely worse than the topological group route.

So the answer to the shortcut question is:

```text
No: division polynomials alone do not give the 2m bound.
A better real-root count for ψ_m is equivalent in difficulty to the real
identity-component/circle theorem or the multiplication-by-m covering theorem.
```

## 11. Recommended Lean plan

Use this three-layer plan.

### Layer 1: real topological theorem, hidden behind one API

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

open scoped Classical Topology
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT.RealRoute4B

theorem real_mTorsion_card_le
    (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
    Nat.card (E.nTorsion m) ≤ 2 * m := by
  -- Prove from identity component ≃+ UnitAddCircle plus component group ≤ 2.
  sorry

end FLT.RealRoute4B
```

### Layer 2: base change `ℚ → ℝ`

This already follows the repo's `Points.map` design.

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT.RealRoute4B

noncomputable abbrev ratToRealAlgHom : ℚ →ₐ[ℚ] ℝ :=
  IsScalarTower.toAlgHom ℚ ℚ ℝ

noncomputable def rationalPointToReal
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Points.map E ratToRealAlgHom

/-- Target local lemma: rational-to-real map on points is injective. -/
theorem rationalPointToReal_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective (rationalPointToReal E) := by
  -- Expected proof: unfold `WeierstrassCurve.Affine.Point.map`, split cases,
  -- and use injectivity of `Rat.cast : ℚ → ℝ` on affine coordinates.
  sorry

end FLT.RealRoute4B
```

### Layer 3: cardinality wrapper

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT.RealRoute4B

/-- Use the project definition if it already exists. -/
def HasFullRationalTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

/--
Final Route 4B wrapper once `real_mTorsion_card_le` and base-change injectivity
are available.
-/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  rcases hfull with ⟨f, hf⟩

  let g : ZMod m × ZMod m →+ (E⁄ℝ).Point :=
    (rationalPointToReal E).comp f

  have hg_inj : Function.Injective g := by
    intro a b hab
    apply hf
    apply rationalPointToReal_injective E
    exact hab

  -- Package `g` as an injection into real m-torsion.
  let gt : ZMod m × ZMod m → Submodule.torsionBy ℤ (E⁄ℝ).Point m :=
    fun a => ⟨g a, by
      change m • g a = 0
      rw [← map_nsmul]
      have ha : m • a = 0 := by
        ext <;> simp
      rw [← f.map_nsmul, ha, f.map_zero, map_zero]
    ⟩

  have hgt_inj : Function.Injective gt := by
    intro a b h
    apply hg_inj
    exact Subtype.ext_iff.mp h

  have hcard_lower : m * m ≤ Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) := by
    calc
      m * m = Nat.card (ZMod m × ZMod m) := by
        -- Usually `simp [Nat.card_prod]` or a small `ZMod` cardinal lemma.
        sorry
      _ ≤ Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) :=
        Nat.card_le_card_of_injective gt hgt_inj

  have hreal : Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) ≤ 2 * m := by
    -- Use `real_mTorsion_card_le` stated directly for `(E⁄ℝ).Point`, or
    -- transport from `(E.map (algebraMap ℚ ℝ)).nTorsion m`.
    sorry

  have hsq : m * m ≤ 2 * m := le_trans hcard_lower hreal
  omega

end FLT.RealRoute4B
```

The only genuinely large theorem in this whole plan is:

```lean
real_mTorsion_card_le
```

Everything else is routine by comparison.

## Final recommendation

For a 0-sorry development, do not try to prove the `2m` bound by counting real roots of `ψ_m`.  That path only hides the same topology inside a hard real-root-count theorem.

The most honest Lean path is:

```text
1. Prove local manifold/compactness/component facts using IVT, IFT, and compactness APIs.
2. Add one group-theoretic/topological input:
      E(ℝ)^0 ≃+ UnitAddCircle
   or directly:
      #(E(ℝ)^0[m]) ≤ m.
3. Prove component group size ≤ 2 from the real cubic root count.
4. Package all of this as:
      real_mTorsion_card_le : Nat.card (E.nTorsion m) ≤ 2*m.
5. Use the existing base-change map and cardinality argument to prove the rational theorem.
```

If the goal is the **shortest** proof of `real_mTorsion_card_le`, target the direct torsion bound as the public theorem and prove it privately from either compact connected 1-dimensional Lie-group classification or the Abel integral.  IVT + IFT + compactness alone are not enough to produce the group isomorphism `E(ℝ)^0 ≃+ ℝ/ℤ`.
