# Q2872 (dm-codex1): Kubert C12 square residual split

Target local file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.RationalPointsN12`

I could not see the local in-progress `KubertBridgeN12.lean` through the canonical GitHub branch, so this answer is keyed to the prompt-provided checked state and to the current Mathlib APIs named in the prompt: `WeierstrassCurve.Affine.Point`, `WeierstrassCurve.Projective.Point`, and `(E⁄ℚ).Point`.

## Executive recommendation

Do **not** leave the residual as the old square-discriminant axiom. Split it as follows:

1. Keep the already-checked group extraction:
   - from `ZMod 2 × ZMod 12` injection, get `∃ P : (E⁄ℚ).Point, addOrderOf P = 12`;
   - from the same injection, get `∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g`.
2. Leave only the cyclic-12 Kubert/Tate-normal-form model theorem as a residual. It should return not merely equations, but also a point-group additive equivalence from `(E⁄ℚ).Point` to the projective point group of the concrete short model.
3. Prove the full-two transport `C` in Lean by composing:

```text
ZMod 2 × ZMod 2 --g--> (E⁄ℚ).Point
                --Kubert add-equivalence--> Projective.Point (shortW A B)
                --Projective.Point.toAffineAddEquiv--> Affine.Point (shortW A B)
```

This uses existing Mathlib APIs and avoids inventing projection syntax such as `(shortW A B).Point`.

The key point is: Mathlib has `WeierstrassCurve.VariableChange` as an action on curves, but I do **not** see a ready-made point-level `AddEquiv` for an arbitrary variable change. Therefore, if the Kubert residual only returns raw coordinate-change data, the transport of the full-two subgroup is still a residual. If the Kubert residual returns the additive equivalence below, then `C` is fully checked and tiny.

## Pasteable Lean design

Place this below the existing definitions of `shortW`, `A12`, `B12`, `Delta12`, and the checked theorem

```lean
square_discriminant_of_full_two_torsion_on_shortW
```

or adapt the import list to the imports already present in `KubertBridgeN12.lean`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve

namespace MazurProof.RationalPointsN12

/--
The remaining cyclic-12 Kubert/Tate-normal-form output needed for the N=12 bridge.

This deliberately includes a point-group additive equivalence.  That is the honest interface
at which the later full-two transport becomes a checked Lean composition instead of another
geometric residual.

The target point type is written with the actual Mathlib namespace:
`WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (shortW A B))`.
Do not replace this by `(shortW A B).Point`.
-/
structure KubertC12ShortWModel (E : WeierstrassCurve ℚ) where
  t : ℚ
  hDelta : Delta12 t ≠ 0
  hB : B12 t ≠ 0
  pointAddEquiv :
    (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (shortW (A12 t) (B12 t)))

/--
Smallest recommended replacement residual for the old `kubert_C12_square` axiom.

Mathematically this is exactly the cyclic-12 Kubert/Tate-normal-form theorem, strengthened
only by exposing the induced additive equivalence on rational point groups.  It no longer
mentions full rational 2-torsion and no longer asserts the square-discriminant conclusion.
-/
axiom kubertC12ShortWModel_of_order12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12ShortWModel E

/--
Checked part C: transport a full-two subgroup through the Kubert additive equivalence and
then through Mathlib's projective-to-affine additive equivalence.

The target type is the one required by the checked theorem
`square_discriminant_of_full_two_torsion_on_shortW`.
-/
noncomputable def fullTwoAffineOfProjectiveAddEquiv
    {E : WeierstrassCurve ℚ} {A B : ℚ}
    (φ : (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (shortW A B)))
    (g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point) :
    (ZMod 2 × ZMod 2) →+
      WeierstrassCurve.Affine.Point (shortW A B) :=
  ((WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (WeierstrassCurve.toProjective (shortW A B))).toAddMonoidHom).comp
    (φ.toAddMonoidHom.comp g)

/--
The transported full-two map is injective because it is a composition of injective maps.
-/
theorem fullTwoAffineOfProjectiveAddEquiv_injective
    {E : WeierstrassCurve ℚ} {A B : ℚ}
    (φ : (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (shortW A B)))
    (g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point)
    (hg : Function.Injective g) :
    Function.Injective
      (fullTwoAffineOfProjectiveAddEquiv (E := E) (A := A) (B := B) φ g) := by
  intro u v huv
  apply hg
  apply φ.injective
  exact
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (WeierstrassCurve.toProjective (shortW A B))).injective huv

/--
Assembly theorem after the checked group-extraction layer.

This is the theorem that actually replaces the old square-discriminant axiom internally:
it uses only
* extracted order-12 point,
* extracted full-two injection,
* the smaller cyclic-12 Kubert model residual,
* the checked affine full-two square-discriminant theorem.
-/
theorem kubert_C12_square_of_extracted_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hP12 : ∃ P : (E⁄ℚ).Point, addOrderOf P = 12)
    (hFull2 : ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point,
      Function.Injective g) :
    ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  rcases hP12 with ⟨P, hP⟩
  rcases hFull2 with ⟨g, hg⟩
  let M := kubertC12ShortWModel_of_order12 E P hP
  let gAff :
      (ZMod 2 × ZMod 2) →+
        WeierstrassCurve.Affine.Point (shortW (A12 M.t) (B12 M.t)) :=
    fullTwoAffineOfProjectiveAddEquiv
      (E := E) (A := A12 M.t) (B := B12 M.t) M.pointAddEquiv g
  have hgAff : Function.Injective gAff := by
    simpa [gAff] using
      fullTwoAffineOfProjectiveAddEquiv_injective
        (E := E) (A := A12 M.t) (B := B12 M.t) M.pointAddEquiv g hg
  rcases square_discriminant_of_full_two_torsion_on_shortW
      (A := A12 M.t) (B := B12 M.t) M.hB gAff hgAff with ⟨s, hs⟩
  exact ⟨M.t, s, M.hDelta, hs⟩

end MazurProof.RationalPointsN12
```

If the line

```lean
exact
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (WeierstrassCurve.toProjective (shortW A B))).injective huv
```

fails to elaborate because Lean does not unfold the `AddMonoidHom.comp` coercions aggressively enough, replace the proof body by this more explicit variant:

```lean
theorem fullTwoAffineOfProjectiveAddEquiv_injective
    {E : WeierstrassCurve ℚ} {A B : ℚ}
    (φ : (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (shortW A B)))
    (g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point)
    (hg : Function.Injective g) :
    Function.Injective
      (fullTwoAffineOfProjectiveAddEquiv (E := E) (A := A) (B := B) φ g) := by
  intro u v huv
  change
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (WeierstrassCurve.toProjective (shortW A B))) (φ (g u)) =
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (WeierstrassCurve.toProjective (shortW A B))) (φ (g v)) at huv
  exact hg <| φ.injective <|
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (WeierstrassCurve.toProjective (shortW A B))).injective huv
```

## Wrapper for the old hypothesis shape

Your local file already has checked extraction theorems from

```lean
hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f
```

to both `hP12` and `hFull2`. Since their names were not given in the prompt, keep the old theorem name as a thin wrapper like this, replacing the two placeholder names by the checked local declarations.

```lean
theorem kubert_C12_square_from_residuals
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  exact kubert_C12_square_of_extracted_torsion E
    (/* existing checked theorem: order-12 point extracted from hE */)
    (/* existing checked theorem: full-two injection extracted from hE */)
```

A realistic filled version will look like this:

```lean
theorem kubert_C12_square_from_residuals
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  exact kubert_C12_square_of_extracted_torsion E
    (exists_order12_point_of_zmod2_zmod12_injective E hE)
    (exists_full_two_injection_of_zmod2_zmod12_injective E hE)
```

where the two identifiers in the final two lines should be replaced by the actual checked theorem names in your file.

## Why this is the smallest honest residual

The old residual was:

```lean
axiom kubert_C12_square
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
  ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t
```

That axiom bundled four distinct tasks: group extraction, cyclic-12 Kubert parametrization, transport of full 2-torsion, and the short-Weierstrass square-discriminant algebra.

After your checked work, the only part that should remain residual is:

```lean
axiom kubertC12ShortWModel_of_order12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12ShortWModel E
```

This residual says only: an elliptic curve over `ℚ` with a rational point of order `12` is additively equivalent, on rational points, to the cyclic-12 Kubert short model

```lean
shortW (A12 t) (B12 t)
```

with `Delta12 t ≠ 0` and `B12 t ≠ 0`.

Everything involving the extracted `ZMod 2 × ZMod 2` subgroup and the square condition

```lean
s ^ 2 = A12 t ^ 2 - 4 * B12 t
```

is then checked by composition plus your existing theorem

```lean
square_discriminant_of_full_two_torsion_on_shortW
```

## If you insist on a raw coordinate-isomorphism residual instead

A residual of the form “there exists a `VariableChange ℚ` taking `E` to the Kubert short model” is mathematically natural, but it is not currently the most useful Lean interface. Mathlib's `VariableChange` file gives the action on curves and invariant quantities, while the checked point-group bridge you need would still have to be built.

So either:

1. prove a new Mathlib/local theorem turning a `VariableChange` equality into

```lean
(E⁄ℚ).Point ≃+
  WeierstrassCurve.Projective.Point
    (WeierstrassCurve.toProjective (shortW A B))
```

or

2. keep that additive equivalence as part of the Kubert residual, as recommended above.

Option 2 is the smallest clean reduction of the present axiom because it removes the full-two and square-discriminant content without forcing a premature formalization of all variable-change point maps.
