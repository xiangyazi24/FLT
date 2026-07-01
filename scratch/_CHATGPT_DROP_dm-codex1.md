# Q2852 (dm-codex1): small `ZMod 2 × ZMod 12` group lemmas

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsN12

/-!
`(E⁄ℚ).Point` is an additive group, so the compiling order function is
`addOrderOf`, not bare `orderOf`.  If a downstream statement wants
multiplicative `orderOf`, use `orderOf (Multiplicative.ofAdd P)`; see the
wrapper below.
-/

private def zmod12ToZmod2xZmod12 : ZMod 12 →+ (ZMod 2 × ZMod 12) where
  toFun x := (0, x)
  map_zero' := by
    ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp

private theorem zmod12ToZmod2xZmod12_injective :
    Function.Injective zmod12ToZmod2xZmod12 := by
  intro x y h
  exact congrArg Prod.snd h

private theorem addOrderOf_zmod2x12_zero_one :
    addOrderOf ((0, 1) : ZMod 2 × ZMod 12) = 12 := by
  have h := addOrderOf_injective
    zmod12ToZmod2xZmod12 zmod12ToZmod2xZmod12_injective (1 : ZMod 12)
  simpa [zmod12ToZmod2xZmod12, ZMod.addOrderOf_one] using h

/-- Additive-order version: this is the natural statement for elliptic-curve points. -/
theorem point_addOrder12_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ P : (E⁄ℚ).Point, addOrderOf P = 12 := by
  refine ⟨f ((0, 1) : ZMod 2 × ZMod 12), ?_⟩
  have h := addOrderOf_injective f hf ((0, 1) : ZMod 2 × ZMod 12)
  simpa [addOrderOf_zmod2x12_zero_one] using h

/-- Multiplicative-order wrapper, if a downstream API is written using `orderOf`. -/
theorem point_order12_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ P : (E⁄ℚ).Point, orderOf (Multiplicative.ofAdd P) = 12 := by
  rcases point_addOrder12_of_zmod2_zmod12_injection E f hf with ⟨P, hP⟩
  exact ⟨P, by simpa using hP⟩

/-- The additive hom `ZMod 2 → ZMod 12` sending `1` to `6`. -/
private def zmod2ToZmod12_six : ZMod 2 →+ ZMod 12 where
  toFun x := (6 : ZMod 12) * ((x.val : ℕ) : ZMod 12)
  map_zero' := by
    simp
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> native_decide

private theorem zmod2ToZmod12_six_injective :
    Function.Injective zmod2ToZmod12_six := by
  intro x y h
  fin_cases x <;> fin_cases y
  · rfl
  · exfalso
    have hv := congrArg ZMod.val h
    norm_num [zmod2ToZmod12_six, ZMod.val_natCast] at hv
  · exfalso
    have hv := congrArg ZMod.val h
    norm_num [zmod2ToZmod12_six, ZMod.val_natCast] at hv
  · rfl

/-- The inclusion `(a,b) ↦ (a,6b)` of `ZMod 2 × ZMod 2` into
`ZMod 2 × ZMod 12`. -/
private def zmod2x2ToZmod2x12 :
    (ZMod 2 × ZMod 2) →+ (ZMod 2 × ZMod 12) where
  toFun x := (x.1, zmod2ToZmod12_six x.2)
  map_zero' := by
    ext <;> simp [zmod2ToZmod12_six]
  map_add' := by
    intro x y
    ext
    · simp
    · exact map_add zmod2ToZmod12_six x.2 y.2

private theorem zmod2x2ToZmod2x12_injective :
    Function.Injective zmod2x2ToZmod2x12 := by
  intro x y h
  apply Prod.ext
  · exact congrArg Prod.fst h
  · exact zmod2ToZmod12_six_injective (congrArg Prod.snd h)

theorem full_two_torsion_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g := by
  refine ⟨f.comp zmod2x2ToZmod2x12, ?_⟩
  intro x y hxy
  apply zmod2x2ToZmod2x12_injective
  apply hf
  exact hxy

end MazurProof.RationalPointsN12
```

API notes:

```lean
#check addOrderOf_injective     -- to-additive version of `orderOf_injective`
#check ZMod.addOrderOf_one      -- `addOrderOf (1 : ZMod n) = n`
#check AddMonoidHom.comp
#check orderOf_ofAdd_eq_addOrderOf
```

The literal target `∃ P, orderOf P = 12` is ill-typed for an additive point group; use `addOrderOf P = 12`, or `orderOf (Multiplicative.ofAdd P) = 12`.
