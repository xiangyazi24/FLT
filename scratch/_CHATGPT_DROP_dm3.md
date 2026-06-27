# Q1270 (dm3): Formalizing the real-topology obstruction to full rational `p`-torsion

## Executive answer

For the target theorem

```text
(Z / pZ)^2 ↪ E(ℚ)  impossible for odd prime p,
```

the base-change part is easy and already has Mathlib/FLT API. The real-topology part is the hard missing theorem.

The clean answers are:

1. **Yes.** The embedding `E(ℚ) → E(ℝ)` should be built from `WeierstrassCurve.Affine.Point.map` / `Point.baseChange`. FLT already has a wrapper `WeierstrassCurve.Points.map`.
2. `AddCircle` / `UnitAddCircle` has useful torsion-cardinality API, but Mathlib does **not** currently provide the bridge
   ```text
   E(ℝ)^0 ≃+ UnitAddCircle
   ```
   or the classification
   ```text
   E(ℝ) ≃ R/Z      or      E(ℝ) ≃ R/Z × Z/2Z.
   ```
   That bridge is essentially real elliptic-curve uniformization / compact one-dimensional Lie group theory.
3. The division-polynomial shortcut does **not** give the needed bound by degree alone. Mathlib has division polynomial definitions and degree computations, but not the theorem that their real roots are exactly controlled by real `p`-torsion. A raw degree bound gives only the tautological `≤ p^2` bound, not `≤ 2p` or `≤ p`.

So, if the goal is a small Lean dependency surface, the best real-topology replacement for Weil pairing is a **single explicit theorem/axiom**:

```lean
real_p_torsion_card_le_two_mul
```

or stronger:

```lean
real_odd_p_torsion_card_le
```

Do **not** try to formalize `E(ℝ)^0 ≃ UnitAddCircle` unless you are willing to add a large real uniformization/topological-group module.

## Checked files / APIs

The FLT repo on branch `scratch` pins Mathlib at

```text
96fd0fff3b8837985ae21dd02e712cb5df72ec05
```

from `lake-manifest.json`.

At that pinned Mathlib revision:

### Point base change exists

`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, around the “Maps and base changes” section, has:

```lean
noncomputable def map : (W'⁄F).Point →+ (W'⁄K).Point

lemma map_zero : map f (0 : (W'⁄F).Point) = 0
lemma map_some ...
lemma map_id (P : (W'⁄F).Point) : map (Algebra.ofId F F) P = P
lemma map_map (P : (W'⁄F).Point) : map g (map f P) = map (g.comp f) P
lemma map_injective : Function.Injective <| map (W' := W') f

noncomputable abbrev baseChange [Algebra F K] [IsScalarTower R F K] :
    (W'⁄F).Point →+ (W'⁄K).Point :=
  map <| Algebra.ofId F K
```

The key theorem is `WeierstrassCurve.Affine.Point.map_injective`: because `f : F →ₐ[S] K` is an algebra hom between fields, Mathlib proves injectivity of the induced point map.

### FLT already wraps the point map

`FLT/EllipticCurve/Torsion.lean` defines:

```lean
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point :=
  WeierstrassCurve.Affine.Point.map f
```

and also has `WeierstrassCurve.Points.map_id` and `WeierstrassCurve.Points.map_comp`.

### AddCircle has torsion bounds

`Mathlib/Topology/Instances/AddCircle/Defs.lean` has:

```lean
abbrev AddCircle [AddCommGroup 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p
```

and the useful torsion-cardinality theorem:

```lean
theorem AddCircle.card_torsion_le_of_isSMulRegular
    (n : ℕ) (h0 : n ≠ 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard ≤ n
```

plus finiteness:

```lean
theorem AddCircle.finite_torsion {n : ℕ} (hn : 0 < n) :
    { u : AddCircle p | n • u = 0 }.Finite
```

`Mathlib/Topology/Instances/AddCircle/Real.lean` defines:

```lean
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)
```

and gives an explicit injection:

```lean
noncomputable def ZMod.toAddCircle : ZMod N →+ UnitAddCircle
lemma ZMod.toAddCircle_injective : Function.Injective (toAddCircle : ZMod N → _)
```

This is enough to reason about `p`-torsion **after** one has an equivalence between real elliptic-curve components and `UnitAddCircle`. It does not provide that equivalence.

### Division polynomials exist, but not the needed real-root theorem

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines:

```lean
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ
```

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` computes the expected degrees, including:

```lean
WeierstrassCurve.natDegree_preΨ_le
WeierstrassCurve.coeff_preΨ
WeierstrassCurve.natDegree_preΨ
WeierstrassCurve.leadingCoeff_preΨ
WeierstrassCurve.natDegree_ΨSq_le
WeierstrassCurve.natDegree_ΨSq
WeierstrassCurve.natDegree_Φ
```

A repository search for division-polynomial/torsion connections only points back to `Basic.lean` and `Degree.lean`; I did not find a theorem of the form “`x` is the x-coordinate of a nonzero `n`-torsion point iff `preΨ n` vanishes at `x`,” nor any theorem counting real roots of division polynomials.

## (1) Constructing `E(ℚ) → E(ℝ)`

Use the base-change map attached to the algebra map `ℚ →ₐ[ℚ] ℝ`.

With the FLT wrapper, the intended definition is:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsionSketch

/-- Base change of rational points to real points. -/
noncomputable def EQ_to_ER
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Points.map E (Algebra.ofId ℚ ℝ)

/-- The base-change map is injective.  The proof should reduce to
`WeierstrassCurve.Affine.Point.map_injective`. -/
theorem EQ_to_ER_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective (EQ_to_ER E) := by
  -- This is the intended proof shape.  Depending on implicit arguments,
  -- Lean may need `(W' := E)` or the affine form of `E` made explicit.
  simpa [EQ_to_ER, WeierstrassCurve.Points.map]
    using (WeierstrassCurve.Affine.Point.map_injective
      (W' := E) (f := Algebra.ofId ℚ ℝ))

end FLT.RealTorsionSketch
```

If the explicit `(W' := E)` does not elaborate because the local notation chooses the affine curve differently, use Mathlib’s raw map directly and let the target type infer the curve:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsionSketch

noncomputable def EQ_to_ER_raw
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Affine.Point.baseChange ℚ ℝ

end FLT.RealTorsionSketch
```

The important point: this map is algebraic base change; no topology is needed.

## (2) What is needed for `E^0(ℝ) ≃ UnitAddCircle`?

The relevant Mathlib objects are:

```lean
import Mathlib.Topology.Instances.AddCircle.Real
```

Then:

```lean
UnitAddCircle      -- definitionally `AddCircle (1 : ℝ)`
UnitAddTorus d     -- `d → UnitAddCircle`
ZMod.toAddCircle   -- explicit `ZMod N →+ UnitAddCircle`
AddCircle.card_torsion_le_of_isSMulRegular
AddCircle.finite_torsion
```

For the group-theoretic part, the theorem you would want from `AddCircle` is only a cardinal bound:

```lean
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section

namespace FLT.RealTorsionSketch

/-- This is the kind of fact already available for additive circles:
`n`-torsion in `ℝ / ℤ` has cardinal at most `n`.

The exact proof term may need minor adjustment, but the underlying theorem is
`AddCircle.card_torsion_le_of_isSMulRegular`.
-/
example (n : ℕ) (hn : n ≠ 0) :
    {x : UnitAddCircle | n • x = 0}.encard ≤ n := by
  exact AddCircle.card_torsion_le_of_isSMulRegular
    (p := (1 : ℝ)) n hn
    (.of_right_eq_zero_of_smul fun x ↦ by simp [hn])

end FLT.RealTorsionSketch
```

But this only talks about `UnitAddCircle`. The missing theorem is the bridge:

```lean
-- Not in Mathlib / FLT currently.
-- Schematic only.
noncomputable def realEllipticIdentityComponentEquivAddCircle
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ERealIdentityComponent E ≃+ UnitAddCircle :=
  sorry
```

or a component-level classification:

```lean
-- Schematic only.
axiom real_points_group_classification
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Nonempty ((E⁄ℝ).Point ≃+ UnitAddCircle) ∨
    Nonempty ((E⁄ℝ).Point ≃+ UnitAddCircle × ZMod 2)
```

That is not a small API task. It requires proving that the real locus of a nonsingular cubic is a compact one-dimensional Lie group with one or two connected components, and identifying the identity component with the additive circle. Analytically, this is real elliptic-curve uniformization; topologically, it is compact connected one-dimensional Lie-group classification.

## Shorter theorem boundary for the FLT use case

For the FLT obstruction, do not formalize the identity component. State the exact cardinal bound you need.

The strongest useful theorem is:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsionSketch

/-- Strong real odd-torsion bound: the real `p`-torsion is cyclic of order at most `p`.
This is true because `E(ℝ) ≃ ℝ/ℤ` or `ℝ/ℤ × ℤ/2ℤ`, and odd torsion ignores the `ZMod 2` component.
-/
axiom real_odd_p_torsion_card_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point p) ≤ p

end FLT.RealTorsionSketch
```

An even weaker theorem is enough for contradiction:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsionSketch

/-- Weak real odd-torsion bound sufficient to rule out `(ZMod p)^2` for `2 < p`. -/
axiom real_p_torsion_card_le_two_mul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point p) ≤ 2 * p

end FLT.RealTorsionSketch
```

With either axiom/theorem, the final contradiction is ordinary group/cardinality bookkeeping.

Schematic proof:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Topology.Instances.AddCircle.Real
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsionSketch

noncomputable def EQ_to_ER
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Points.map E (Algebra.ofId ℚ ℝ)

axiom EQ_to_ER_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective (EQ_to_ER E)

axiom real_p_torsion_card_le_two_mul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point p) ≤ 2 * p

/-- Schematic: compose an injected `Fp²` in `E(ℚ)` with base change to `E(ℝ)`,
observe its image lies in real `p`-torsion, and contradict the real cardinal bound. -/
theorem no_Fp2_in_EQ_from_real_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    ¬ ∃ f : ZMod p × ZMod p →+ (E⁄ℚ).Point, Function.Injective f := by
  rintro ⟨f, hf⟩

  -- Build an additive monoid hom into the real p-torsion subgroup.
  let g : ZMod p × ZMod p →+ Submodule.torsionBy ℤ (E⁄ℝ).Point p :=
  { toFun := fun x =>
      ⟨EQ_to_ER E (f x), by
        -- `p • x = 0` in `ZMod p × ZMod p`, so `p • f x = 0`, and maps preserve `nsmul`.
        -- This is routine `simp`/`ext` arithmetic in `ZMod` plus `map_nsmul`.
        sorry⟩
    map_zero' := by
      ext
      simp [EQ_to_ER]
    map_add' := by
      intro x y
      ext
      simp [EQ_to_ER] }

  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply hf
    apply EQ_to_ER_injective E
    exact congrArg Subtype.val hxy

  have hcard_domain : Nat.card (ZMod p × ZMod p) = p * p := by
    -- `simp` should know the cardinality of `ZMod p` and products.
    simp

  have hcard_inj : Nat.card (ZMod p × ZMod p) ≤
      Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point p) := by
    exact Nat.card_le_card_of_injective g hg_inj

  have hreal := real_p_torsion_card_le_two_mul E p hp hpgt

  -- From `p*p ≤ 2*p` and `0 < p`, get `p ≤ 2`, contradicting `2 < p`.
  have hp_pos : 0 < p := hp.pos
  have hp_le_two : p ≤ 2 := by
    nlinarith [hcard_domain, hcard_inj, hreal, hp_pos]
  omega

end FLT.RealTorsionSketch
```

I would not keep `EQ_to_ER_injective` as an axiom; it is just a wrapper around `Point.map_injective`. I wrote it as an axiom in this schematic block only to keep the main cardinal proof focused.

## (3) Why division polynomials do not give a short `≤ 2p` proof

For odd `p`, the relevant univariate division polynomial has degree

```text
(p^2 - 1) / 2.
```

A nonzero real `p`-torsion point and its negative have the same `x`-coordinate, so a naive real-root count gives at best

```text
#E(ℝ)[p] ≤ 1 + 2 * degree(ψ_p)
           = 1 + 2 * ((p^2 - 1) / 2)
           = p^2.
```

That is exactly the size of full geometric `p`-torsion, so it does **not** contradict an injection of `(Z / pZ)^2`.

To get the true real bound

```text
#E(ℝ)[p] = p       for odd p,
```

you need more than degree. You need to know the real-root distribution of the division polynomial, or equivalently that the real group is a circle up to a harmless `Z/2` component. Proving that root distribution by Sturm theory or interlacing of division polynomials would be a substantial real-analysis/computational-polynomial project, not a short shortcut.

So the division-polynomial path currently has two missing pieces:

```lean
-- Schematic, not currently in Mathlib.
theorem prePsi_vanishes_iff_x_coord_of_nonzero_n_torsion : Prop := by
  sorry

-- Schematic, much harder: the real roots of `preΨ p` are only `(p-1)/2` many.
theorem real_roots_prePsi_odd_prime_card : Prop := by
  sorry
```

Mathlib’s current `DivisionPolynomial.Basic` and `DivisionPolynomial.Degree` are useful starts, but they do not yet provide those torsion/root-count theorems.

## Recommended architecture

If you want the **smallest formal module** for this route, use this theorem boundary:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.RealTorsionSketch

/-- Algebraic, should be proved immediately from Mathlib `Point.map_injective`. -/
theorem rational_points_embed_real_points
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective
      (WeierstrassCurve.Points.map E (Algebra.ofId ℚ ℝ) :
        (E⁄ℚ).Point →+ (E⁄ℝ).Point) := by
  simpa [WeierstrassCurve.Points.map]
    using (WeierstrassCurve.Affine.Point.map_injective
      (W' := E) (f := Algebra.ofId ℚ ℝ))

/-- The single real-topology input.  This is the only hard theorem in the real route. -/
axiom real_odd_torsion_card_le_two_mul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point p) ≤ 2 * p

end FLT.RealTorsionSketch
```

Then the proof of “no `(ZMod p)^2` injects into `E(ℚ)`” is finite cardinal arithmetic.

If the project is trying to minimize axioms, the Weil-pairing route is still much cleaner: one Weil-pairing corollary directly rules out full rational `p`-torsion over `ℚ`. The real-topology route is attractive only if `real_odd_torsion_card_le_two_mul` is actually proved; otherwise it is just a different hard axiom.
