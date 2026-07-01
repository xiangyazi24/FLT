# Q2874 dm-codex2: Kubert N12 torsion transport API skeleton

Namespace: `MazurProof.RationalPointsN12`.

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`.

I could not fetch `KubertBridgeN12.lean` or the named local WIP declarations from `xiangyazi24/FLT@scratch`; the skeleton below is therefore self-contained and uses the type names from the prompt.

## 1. Best residual type

For the downstream Kubert C proof, the most convenient normal-form residual is **not** a curve-isomorphism object. The minimal checkable residual is an additive homomorphism on point groups plus injectivity:

```lean
∃ t : ℚ,
  B12 t ≠ 0 ∧
  ∃ φ : (E⁄ℚ).Point →+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)),
    Function.Injective φ
```

This is exactly what the final step needs: if `f22` is an injected full-two subgroup on `(E⁄ℚ).Point`, then `φ.comp f22` is an injected full-two subgroup on the short normal form.

If the normal-form theorem naturally proves an equivalence, use an `AddEquiv`; but immediately wrap it into the same residual shape:

```lean
-- If `e : (E⁄ℚ).Point ≃+ WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t))`
let φ : (E⁄ℚ).Point →+
    WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)) :=
  e.toAddMonoidHom
have hφ : Function.Injective φ := by
  intro P Q hPQ
  exact e.injective hPQ
```

Why this is better than exposing a variable-change object downstream:

* it avoids depending on the exact Mathlib curve-isomorphism API in the Kubert obstruction file;
* it is enough for `square_discriminant_of_full_two_torsion_on_shortW`;
* it lets the hard normal-form proof live in a separate file with whatever curve-map API is most convenient.

Recommended residual declaration:

```lean
open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsN12

/-- Minimal residual output of the Kubert normal-form reduction. -/
structure KubertNormalFormTransport (E : WeierstrassCurve ℚ) where
  t : ℚ
  hB : B12 t ≠ 0
  φ : (E⁄ℚ).Point →+
    WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t))
  φ_injective : Function.Injective φ

/-- Residual theorem shape if the normal form is available under a C12 injection. -/
def KubertC12NormalFormResidual : Prop :=
  ∀ {E : WeierstrassCurve ℚ}
    (f12 : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point),
    Function.Injective f12 →
      ∃ nt : KubertNormalFormTransport E, True

end MazurProof.RationalPointsN12
```

The terminal `True` is optional; it is useful if the residual later needs to return side conditions without changing call sites.

## 2. Pure composition lemma

This is the exact generic lemma I would put near the top of `KubertBridgeN12.lean`.

```lean
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsN12

/-- Transport an injected full-two subgroup through any injective additive hom. -/
theorem compose_full_two_torsion_injection_through_addMonoidHom
    {P Q : Type*} [AddMonoid P] [AddMonoid Q]
    (f : ZMod 2 × ZMod 2 →+ P)
    (hf : Function.Injective f)
    (φ : P →+ Q)
    (hφ : Function.Injective φ) :
    Function.Injective (φ.comp f) := by
  intro x y hxy
  apply hf
  apply hφ
  simpa using hxy

end MazurProof.RationalPointsN12
```

If Lean unfolds the composition differently, replace the final line by:

```lean
  simpa [AddMonoidHom.comp_apply] using hxy
```

This theorem avoids any curve-specific API. The point groups only need their existing additive monoid/group instances.

## 3. If the input is C12 torsion, extract full-two torsion separately

For the final bridge, prefer to pass an already-extracted

```lean
f22 : ZMod 2 × ZMod 2 →+ (E⁄ℚ).Point
hf22 : Function.Injective f22
```

to the normal-form square-discriminant step.

If you do want to extract it from

```lean
f12 : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point
hf12 : Function.Injective f12
```

put that in a separate group-only lemma. The required inclusion sends the second `ZMod 2` generator to `6 : ZMod 12`.

```lean
namespace MazurProof.RationalPointsN12

abbrev FullTwoDomain : Type := ZMod 2 × ZMod 2
abbrev C12Domain : Type := ZMod 2 × ZMod 12

-- Preferred if `ZMod.lift` is available in the pinned Mathlib.
-- Check exact signature with:
--   #check ZMod.lift
--   #check ZMod.lift_apply
--
-- def zmod2_to_zmod12_six : ZMod 2 →+ ZMod 12 :=
--   ZMod.lift (2 : ℕ) (6 : ZMod 12) (by norm_num)

/-- Inclusion of the full-two subgroup into `ZMod 2 × ZMod 12`.
    Fill `zmod2_to_zmod12_six` using the local `ZMod.lift` API. -/
def fullTwoIntoC12
    (ι : ZMod 2 →+ ZMod 12) :
    FullTwoDomain →+ C12Domain where
  toFun x := (x.1, ι x.2)
  map_zero' := by
    ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp [map_add]

theorem fullTwoIntoC12_injective
    (ι : ZMod 2 →+ ZMod 12)
    (hι0 : ι 0 = 0)
    (hι1 : ι 1 = (6 : ZMod 12)) :
    Function.Injective (fullTwoIntoC12 ι) := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg Prod.fst hxy
  · -- Since the domain is `ZMod 2`, it is enough to split into two cases.
    -- This version is deliberately robust to local `ZMod` extensionality names.
    have hsecond : ι x.2 = ι y.2 := congrArg Prod.snd hxy
    fin_cases x.2 <;> fin_cases y.2 <;> simp [hι0, hι1] at hsecond ⊢

/-- Full-two injection obtained from C12 injection. -/
def fullTwoInjection_of_C12
    {P : Type*} [AddMonoid P]
    (ι : ZMod 2 →+ ZMod 12)
    (f12 : C12Domain →+ P) :
    FullTwoDomain →+ P :=
  f12.comp (fullTwoIntoC12 ι)

theorem fullTwoInjection_of_C12_injective
    {P : Type*} [AddMonoid P]
    (ι : ZMod 2 →+ ZMod 12)
    (hι0 : ι 0 = 0)
    (hι1 : ι 1 = (6 : ZMod 12))
    (f12 : C12Domain →+ P)
    (hf12 : Function.Injective f12) :
    Function.Injective (fullTwoInjection_of_C12 ι f12) := by
  exact hf12.comp (fullTwoIntoC12_injective ι hι0 hι1)

end MazurProof.RationalPointsN12
```

If `ZMod.lift` is missing or awkward, define `ι` by `fin_cases` locally and prove its hom law by four cases. Keep that case split out of the Kubert square step.

Likely discovery commands:

```lean
#check ZMod.lift
#check ZMod.castHom
#check ZMod.val
#check ZMod.natCast_zmod_val
```

`ZMod.castHom` is **not** the right map from `ZMod 2` to `ZMod 12`: a ring hom `ZMod n →+* ZMod m` exists in the divisibility direction `m ∣ n`, so it will not produce the subgroup map sending `1 ↦ 6`.

## 4. Kubert square-discriminant bridge skeleton

Use this when the full-two injection on `E` has already been extracted.

```lean
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsN12

/--
Core transport step.  The theorem target should be exactly the target of

  #check square_discriminant_of_full_two_torsion_on_shortW

with `A := A12 t`, `B := B12 t`.
-/
theorem kubert_C12_square_from_normal_form_residual
    {E : WeierstrassCurve ℚ} {t : ℚ}
    (hB : B12 t ≠ 0)
    (f22 : ZMod 2 × ZMod 2 →+ (E⁄ℚ).Point)
    (hf22 : Function.Injective f22)
    (φ : (E⁄ℚ).Point →+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)))
    (hφ : Function.Injective φ) :
    -- Paste the exact conclusion printed by:
    --   #check square_discriminant_of_full_two_torsion_on_shortW
    -- Expected shape, depending on the local theorem:
    --   IsSquare (short_discriminant (A12 t) (B12 t))
    -- or
    --   ∃ u : ℚ, u ^ 2 = -(4 * (A12 t)^3 + 27 * (B12 t)^2)
    by
      exact square_discriminant_of_full_two_torsion_on_shortW
        (hB := hB)
        (φ.comp f22)
        (compose_full_two_torsion_injection_through_addMonoidHom
          f22 hf22 φ hφ) := by
  let g : ZMod 2 × ZMod 2 →+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)) :=
    φ.comp f22
  have hg : Function.Injective g :=
    compose_full_two_torsion_injection_through_addMonoidHom
      f22 hf22 φ hφ
  exact square_discriminant_of_full_two_torsion_on_shortW
    (hB := hB) g hg

end MazurProof.RationalPointsN12
```

The unusual theorem header above shows the key point: because I cannot see the local return type of `square_discriminant_of_full_two_torsion_on_shortW`, fill the theorem conclusion from `#check` and keep the proof body exactly as shown. In a real file it should look like this after filling the target:

```lean
theorem kubert_C12_square_from_normal_form_residual
    {E : WeierstrassCurve ℚ} {t : ℚ}
    (hB : B12 t ≠ 0)
    (f22 : ZMod 2 × ZMod 2 →+ (E⁄ℚ).Point)
    (hf22 : Function.Injective f22)
    (φ : (E⁄ℚ).Point →+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)))
    (hφ : Function.Injective φ) :
    <the exact square-discriminant conclusion at `A12 t`, `B12 t`> := by
  let g : ZMod 2 × ZMod 2 →+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)) :=
    φ.comp f22
  have hg : Function.Injective g := by
    exact compose_full_two_torsion_injection_through_addMonoidHom
      f22 hf22 φ hφ
  exact square_discriminant_of_full_two_torsion_on_shortW
    (hB := hB) g hg
```

If the checked theorem has explicit `A`/`B` parameters, use:

```lean
  exact square_discriminant_of_full_two_torsion_on_shortW
    (A := A12 t) (B := B12 t) (hB := hB) g hg
```

If it has explicit `t`, use:

```lean
  exact square_discriminant_of_full_two_torsion_on_shortW
    (t := t) (hB := hB) g hg
```

## 5. Bridge using the residual structure

This version consumes the recommended residual package.

```lean
namespace MazurProof.RationalPointsN12

/-- Normal-form residual plus full-two torsion gives the short-form square discriminant. -/
theorem kubert_C12_square_from_transport_package
    {E : WeierstrassCurve ℚ}
    (nt : KubertNormalFormTransport E)
    (f22 : ZMod 2 × ZMod 2 →+ (E⁄ℚ).Point)
    (hf22 : Function.Injective f22) :
    -- Fill with an existential using the exact local square-discriminant conclusion:
    -- ∃ t : ℚ, <square-discriminant conclusion for `A12 t`, `B12 t`>
    ∃ t : ℚ, True := by
  refine ⟨nt.t, ?_⟩
  -- Replace `True` by:
  -- exact kubert_C12_square_from_normal_form_residual
  --   (E := E) (t := nt.t) nt.hB f22 hf22 nt.φ nt.φ_injective
  trivial

end MazurProof.RationalPointsN12
```

In the actual file, do not leave `True`; use the exact result proposition from the checked theorem. The construction of `g` and `hg` is independent of that proposition.

## 6. If the normal-form theorem gives an `AddEquiv`

Use this tiny adapter and then call the same theorem.

```lean
namespace MazurProof.RationalPointsN12

theorem kubert_C12_square_from_normal_form_addEquiv
    {E : WeierstrassCurve ℚ} {t : ℚ}
    (hB : B12 t ≠ 0)
    (f22 : ZMod 2 × ZMod 2 →+ (E⁄ℚ).Point)
    (hf22 : Function.Injective f22)
    (e : (E⁄ℚ).Point ≃+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t))) :
    -- Same exact target as `kubert_C12_square_from_normal_form_residual`.
    <the exact square-discriminant conclusion at `A12 t`, `B12 t`> := by
  let φ : (E⁄ℚ).Point →+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)) :=
    e.toAddMonoidHom
  have hφ : Function.Injective φ := by
    intro P Q hPQ
    exact e.injective hPQ
  exact kubert_C12_square_from_normal_form_residual
    (E := E) (t := t) hB f22 hf22 φ hφ

end MazurProof.RationalPointsN12
```

If Lean does not simplify coercions from `φ` to `e`, use:

```lean
  have hφ : Function.Injective φ := by
    intro P Q hPQ
    exact e.injective (by simpa [φ] using hPQ)
```

## 7. Mathlib curve-isomorphism / variable-change API discovery

The current downstream bridge should not depend on these names, but the normal-form producer may use them.

Start with these `#check`s inside the repo, after the imports already used in Weierstrass files:

```lean
open scoped WeierstrassCurve.Affine

#check WeierstrassCurve
#check WeierstrassCurve.Affine.Point
#check WeierstrassCurve.Affine.Point.baseChange
#check WeierstrassCurve.Affine.Point.map_injective
#check WeierstrassCurve.Points.map
#check WeierstrassCurve.Points.map
#check Algebra.ofId
```

Then search Mathlib locally:

```bash
rg "structure .*Variable|def .*Variable|VariableChange" .lake/packages/mathlib/Mathlib -n
rg "Affine.Point.*map|def .*baseChange|map_injective" .lake/packages/mathlib/Mathlib -n
rg "WeierstrassCurve.*AddEquiv|Affine.Point.*AddEquiv|toAddMonoidHom" .lake/packages/mathlib/Mathlib -n
rg "namespace WeierstrassCurve" .lake/packages/mathlib/Mathlib/AlgebraicGeometry -n
```

Likely imports to try, depending on the repo’s pinned Mathlib layout:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
```

If those are too broad, use the imports already present in files where these appeared:

```lean
WeierstrassCurve.Affine.Point.baseChange ℚ ℝ
WeierstrassCurve.Affine.Point.map_injective (W' := E) (f := Algebra.ofId ℚ ℝ)
WeierstrassCurve.Points.map E (Algebra.ofId ℚ ℝ)
```

The robust workflow is:

1. In the producer file, turn the curve variable change into either
   `AddEquiv` or `AddMonoidHom + Function.Injective` on point groups.
2. Export only that residual hom/injectivity pair to `KubertBridgeN12.lean`.
3. In `KubertBridgeN12.lean`, compose via `φ.comp f22` and apply `square_discriminant_of_full_two_torsion_on_shortW`.

## 8. Syntax pitfalls

* Do not write `(shortW A B).Point`. Use
  `WeierstrassCurve.Affine.Point (shortW A B)`.
* For the source curve, use the existing local spelling `(E⁄ℚ).Point` if that already has the group instance expected by the injection theorem.
* `AddMonoidHom.comp` order is `φ.comp f`, meaning `x ↦ φ (f x)`.
* If `Function.Injective (φ.comp f)` does not close by `hφ.comp hf`, use the explicit proof in Section 2.
* Keep the full-two extraction from `ZMod 2 × ZMod 12` separate from normal-form transport; it is group-only and should not import Weierstrass geometry.
