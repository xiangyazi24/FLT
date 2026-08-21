import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
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
