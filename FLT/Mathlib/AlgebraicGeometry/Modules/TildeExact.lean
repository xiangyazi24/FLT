import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Topology.Sheaves.Abelian

/-!
# Exactness of affine module sheafification

For a commutative ring `R`, the affine tilde functor sends an `R`-module to
the corresponding module sheaf on `Spec R`.  This file proves that tilde
preserves exact short complexes.

The proof checks exactness on stalks after forgetting the module structure.
The stalk of `M̃` at a prime is the localization of `M` at that prime, and the
stalk map induced by a linear map is the canonical map between the localized
modules.  Exactness therefore follows from exactness of module localization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open TopCat

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-- The underlying morphism of abelian-group presheaves associated to a tilde
morphism.  Naming this map separates the colimit defining a stalk from the
module-sheaf bookkeeping in `SheafOfModules.toSheaf`. -/
noncomputable def tildePresheafMap {M N : ModuleCat R} (f : M ⟶ N) :
    (tilde M).presheaf ⟶ (tilde N).presheaf where
  app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' ((tilde.map f).val.app U) (by simp)
  naturality X Y g := by
    ext y
    exact PresheafOfModules.naturality_apply (tilde.map f).val g y

/-- Forgetting a tilde morphism to abelian-group presheaves gives
`tildePresheafMap`.  This is the comparison used when exactness is reflected
through the faithful forgetful functor from module sheaves. -/
theorem forget_toSheaf_tilde_map {M N : ModuleCat R} (f : M ⟶ N) :
    (TopCat.Sheaf.forget AddCommGrpCat (Spec R)).map
        ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map (tilde.map f)) =
      tildePresheafMap R f := by
  rfl

/-- The map on a stalk induced by `tilde.map f` is the canonical localization
of `f` at the corresponding prime ideal.

The proof first verifies scalar compatibility on germs.  An arbitrary stalk
element is then written with one denominator.  Multiplication by that
denominator is invertible in the target stalk, so equality reduces to the
naturality square on the germ of a global numerator. -/
theorem tilde_stalkMap_eq_localization {M N : ModuleCat R}
    (f : M ⟶ N) (x : Spec R) :
    (fun z ↦
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (tildePresheafMap R f)) z) =
      fun z ↦ IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk M x).hom (tilde.toStalk N x).hom f.hom z := by
  funext z
  let actual : (tilde M).presheaf.stalk x → (tilde N).presheaf.stalk x :=
    fun w ↦
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (tildePresheafMap R f)) w
  let z' : (tilde M).presheaf.stalk x := z
  change actual z' = IsLocalizedModule.map x.asIdeal.primeCompl
    (tilde.toStalk M x).hom (tilde.toStalk N x).hom f.hom z'
  have actual_smul (r : R) (w : (tilde M).presheaf.stalk x) :
      actual (r • w) = r • actual w := by
    obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ w
    have hSource :
        (tilde M).presheaf.germ U x hxU (r • t) =
          r • (tilde M).presheaf.germ U x hxU t := by
      change _ = StructureSheaf.toStalk R x r •
        TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU t
      rw [← StructureSheaf.algebraMap_germ_apply U x hxU]
      refine .trans ?_ (PresheafOfModules.germ_smul ..)
      congr 1
    change actual (r • (tilde M).presheaf.germ U x hxU t) =
      r • actual ((tilde M).presheaf.germ U x hxU t)
    rw [← hSource]
    dsimp only [actual]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    have hApp :
        (tildePresheafMap R f).app (.op U)
            (r • (show Γ(tilde M, U) from t)) =
          r • (show Γ(tilde N, U) from
            (tildePresheafMap R f).app (.op U) t) := by
      rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_Spec_def]
      exact ((tilde.map f).val.app (.op U)).hom.map_smul _ t
    rw [hApp]
    change
      TopCat.Presheaf.germ (moduleStructurePresheaf R N).presheaf U x hxU
          (r • (show Γ(tilde N, U) from (tilde.map f).val.app (.op U) t)) =
        r • TopCat.Presheaf.germ (moduleStructurePresheaf R N).presheaf U x hxU
          ((tilde.map f).val.app (.op U) t)
    change _ = StructureSheaf.toStalk R x r •
      TopCat.Presheaf.germ (moduleStructurePresheaf R N).presheaf U x hxU
        ((tilde.map f).val.app (.op U) t)
    rw [← StructureSheaf.algebraMap_germ_apply U x hxU]
    refine .trans ?_ (PresheafOfModules.germ_smul ..)
    congr 1
  obtain ⟨⟨m, s⟩, hs⟩ :=
    IsLocalizedModule.surj x.asIdeal.primeCompl (tilde.toStalk M x).hom z'
  apply IsLocalizedModule.smul_injective (tilde.toStalk N x).hom s
  change (s : R) • actual z' = (s : R) •
    IsLocalizedModule.map x.asIdeal.primeCompl
      (tilde.toStalk M x).hom (tilde.toStalk N x).hom f.hom z'
  have hsR : (s : R) • z' = tilde.toStalk M x m := by
    exact hs
  rw [← actual_smul (s : R) z', hsR]
  rw [← LinearMap.map_smul, hsR, IsLocalizedModule.map_apply]
  change actual (tilde.toStalk M x m) = tilde.toStalk N x (f m)
  change actual
      ((tilde M).presheaf.germ ⊤ x trivial
        (StructureSheaf.toOpenₗ R M ⊤ m)) =
    (tilde N).presheaf.germ ⊤ x trivial
      (StructureSheaf.toOpenₗ R N ⊤ (f m))
  dsimp only [actual]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  congr 1
  change StructureSheaf.comapₗ f.hom ⊤ ⊤ (fun _ h ↦ h)
      (StructureSheaf.toOpenₗ R M ⊤ m) =
    StructureSheaf.toOpenₗ R N ⊤ (f m)
  rw [StructureSheaf.toOpenₗ_eq_const, StructureSheaf.toOpenₗ_eq_const,
    StructureSheaf.comapₗ_const]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The nested forgetful and stalk functors require deeper instance synthesis
-- than the default budget, independently of the mathematical proof terms.
/-- After forgetting the scalar action, affine tilde sends an exact module
complex to an exact complex of abelian-group sheaves.  Keeping this stronger
form separate is useful for local-to-global arguments, where stalk exactness
is transported across an open immersion. -/
theorem tilde_map_toSheaf_exact (S : ShortComplex (ModuleCat R))
    (hS : S.Exact) :
    let F := SheafOfModules.toSheaf (Spec R).ringCatSheaf
    letI : F.Additive := inferInstance
    (@CategoryTheory.ShortComplex.map _ _ _ _ _ _
      (S.map (tilde.functor R)) F
      (CategoryTheory.Functor.preservesZeroMorphisms_of_additive F)).Exact := by
  dsimp only
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro x
  rw [ShortComplex.ab_exact_iff_function_exact]
  have hFunction : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  have hLocalized :=
    IsLocalizedModule.map_exact x.asIdeal.primeCompl
      (tilde.toStalk S.X₁ x).hom (tilde.toStalk S.X₂ x).hom
      (tilde.toStalk S.X₃ x).hom S.f.hom S.g.hom hFunction
  convert hLocalized using 1 <;> try rfl
  all_goals
    rename_i h₁ h₂
    cases h₁
    cases h₂
    apply heq_of_eq
  · change
      (fun z ↦ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (tildePresheafMap R S.f)) z) =
      fun z ↦ IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk S.X₁ x).hom (tilde.toStalk S.X₂ x).hom S.f.hom z
    exact tilde_stalkMap_eq_localization R S.f x
  · change
      (fun z ↦ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (tildePresheafMap R S.g)) z) =
      fun z ↦ IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk S.X₂ x).hom (tilde.toStalk S.X₃ x).hom S.g.hom z
    exact tilde_stalkMap_eq_localization R S.g x

set_option synthInstance.maxHeartbeats 100000 in
-- Reflecting through the faithful scalar-forgetful functor is categorical;
-- the larger budget is needed only to synthesize the nested functor data.
/-- Affine module sheafification preserves exactness.  Equivalently, the tilde
functor from `R`-modules to module sheaves on `Spec R` is exact on every short
complex. -/
theorem tilde_map_exact (S : ShortComplex (ModuleCat R)) (hS : S.Exact) :
    (S.map (tilde.functor R)).Exact := by
  let F := SheafOfModules.toSheaf (Spec R).ringCatSheaf
  letI : F.Additive := inferInstance
  letI : F.PreservesZeroMorphisms :=
    CategoryTheory.Functor.preservesZeroMorphisms_of_additive F
  exact F.reflects_exact_of_faithful _ (tilde_map_toSheaf_exact R S hS)

end AlgebraicGeometry
