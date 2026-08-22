import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Same-site relative differentials for schemes over an affine base

A morphism from a scheme to an affine spectrum induces a map from the
constant base ring to the structure presheaf on the scheme's small Zariski
site.  This file packages that map and the universal property of the
objectwise relative Kähler differential presheaf.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The base-ring map on the small Zariski site induced by a morphism to an
affine spectrum. -/
noncomputable def constBaseMap (K : CommRingCat.{u}) {X : Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec K) :
    (Functor.const X.Opensᵒᵖ).obj K ⟶ X.presheaf where
  app U :=
    (ΓSpecIso K).inv ≫
      p.appLE (⊤ : (AlgebraicGeometry.Spec K).Opens) U.unop (by simp)
  naturality := by
    intro U V i
    simp only [Functor.const_obj_map, Category.assoc]
    rw [p.appLE_map]
    exact Category.id_comp _

@[simp]
theorem constBaseMap_app (K : CommRingCat.{u}) {X : Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec K) (U : X.Opensᵒᵖ) :
    (constBaseMap K p).app U =
      (ΓSpecIso K).inv ≫
        p.appLE (⊤ : (AlgebraicGeometry.Spec K).Opens) U.unop (by simp) :=
  rfl

end AlgebraicGeometry.Scheme

namespace PresheafOfModules.DifferentialsConstruction

universe u vD uD

variable {D : Type uD} [Category.{vD} D]
variable {S R : Dᵒᵖ ⥤ CommRingCat.{u}}

/-- Morphisms from the relative differential presheaf are equivalent to
compatible relative derivations. -/
noncomputable def homEquiv (φ : S ⟶ R)
    (M : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)) :
    (relativeDifferentials' φ ⟶ M) ≃ M.Derivation' φ where
  toFun f := (derivation' φ).postcomp f
  invFun d := (isUniversal' φ).desc d
  left_inv f := by
    apply (isUniversal' φ).postcomp_injective
    exact (isUniversal' φ).fac ((derivation' φ).postcomp f)
  right_inv d := (isUniversal' φ).fac d

end PresheafOfModules.DifferentialsConstruction

namespace PresheafOfModules.Derivation'

open CategoryTheory.Limits

universe u vD uD

variable {D : Type uD} [Category.{vD} D]
variable {S R : Dᵒᵖ ⥤ CommRingCat.{u}}
variable {φ : S ⟶ R}

@[simp]
theorem postcomp_comp
    {M N P : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)}
    (d : M.Derivation' φ) (f : M ⟶ N) (g : N ⟶ P) :
    (d.postcomp f).postcomp g = d.postcomp (f ≫ g) := by
  rfl

/-- The product derivation records a compatible family of relative
derivations in one product-valued derivation. -/
noncomputable def pi {ι : Type u}
    (M : ι → PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))
    (d : ∀ i, (M i).Derivation' φ) :
    (∏ᶜ M).Derivation' φ :=
  (DifferentialsConstruction.derivation' φ).postcomp
    (Limits.Pi.lift fun i =>
      (DifferentialsConstruction.isUniversal' φ).desc (d i))

@[simp]
theorem pi_postcomp_π {ι : Type u}
    (M : ι → PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))
    (d : ∀ i, (M i).Derivation' φ) (i : ι) :
    (pi M d).postcomp (Limits.Pi.π M i) = d i := by
  unfold pi
  rw [postcomp_comp, Limits.Pi.lift_π]
  exact (DifferentialsConstruction.isUniversal' φ).fac (d i)

/-- A relative derivation satisfying two parallel module equations lifts to
the corresponding equalizer-valued derivation. -/
noncomputable def equalizerLift
    {M N : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)}
    (d : M.Derivation' φ) (f g : M ⟶ N)
    (h : d.postcomp f = d.postcomp g) :
    (equalizer f g).Derivation' φ :=
  (DifferentialsConstruction.derivation' φ).postcomp
    (equalizer.lift
      ((DifferentialsConstruction.isUniversal' φ).desc d)
      (by
        apply (DifferentialsConstruction.isUniversal' φ).postcomp_injective
        rw [← postcomp_comp, ← postcomp_comp]
        rw [(DifferentialsConstruction.isUniversal' φ).fac d]
        exact h))

@[simp]
theorem equalizerLift_postcomp_ι
    {M N : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)}
    (d : M.Derivation' φ) (f g : M ⟶ N)
    (h : d.postcomp f = d.postcomp g) :
    (equalizerLift d f g h).postcomp (equalizer.ι f g) = d := by
  unfold equalizerLift
  rw [postcomp_comp, equalizer.lift_ι]
  exact (DifferentialsConstruction.isUniversal' φ).fac d

end PresheafOfModules.Derivation'
