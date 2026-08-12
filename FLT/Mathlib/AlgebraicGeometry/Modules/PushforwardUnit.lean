import FLT.Mathlib.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The structure module and direct image

This file packages the canonical morphism from the structure module of a
scheme to the direct image of the structure module along a scheme morphism.
For a closed immersion this morphism is an epimorphism.  For open immersions,
the remaining lemmas identify its adjunction transpose with the canonical
restriction isomorphism and record its compatibility with iterated
restriction.

These statements are deliberately phrased in the category of module sheaves.
They let geometric resolutions use categorical kernels and cokernels without
re-expanding the underlying morphisms of sheaves of rings at every step.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme} (f : X ⟶ Y)

/-- The ringed-space map, regarded as a morphism from the ambient structure
module to the direct image of the source structure module. -/
def unitToPushforwardUnit :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp]
theorem unitToPushforwardUnit_app_apply (U : Y.Opens) (a : Γ(Y, U)) :
    Hom.app (unitToPushforwardUnit f) U a = f.app U a :=
  rfl

/-- A closed immersion makes the ambient structure module surject locally
onto the direct image of the source structure module.  Affine opens form a
basis, and the defining section map of a closed immersion is surjective on
each such open. -/
theorem unitToPushforwardUnit_epi [IsClosedImmersion f] :
    Epi (unitToPushforwardUnit f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hlocal : TopCat.Presheaf.IsLocallySurjective
      (F.map (unitToPushforwardUnit f)).hom := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t y hy
    obtain ⟨V, ⟨W, hW, rfl⟩, hyV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    refine ⟨W, hVU, ?_, hyV⟩
    obtain ⟨s, hs⟩ := f.app_surjective W hW (t |_ W)
    exact ⟨s, hs⟩
  letI : CategoryTheory.Sheaf.IsLocallySurjective
      (F.map (unitToPushforwardUnit f)) := hlocal
  letI : Epi (F.map (unitToPushforwardUnit f)) :=
    CategoryTheory.Sheaf.epi_of_isLocallySurjective _
  constructor
  intro Z g h hgh
  apply F.map_injective
  apply (cancel_epi (F.map (unitToPushforwardUnit f))).mp
  simpa only [← F.map_comp] using congrArg F.map hgh

/-! ## The structure map under vertical-open base change

Consider a cartesian square whose vertical maps are open immersions.  The
Beck--Chevalley isomorphism from `PullbackUnit` identifies restriction of a
horizontal direct image with the direct image of the opposite restriction.
For structure modules this identification carries the restricted canonical
map to the canonical map along the upper horizontal arrow.  This naturality
statement is what lets a global closed immersion be tested on affine charts.
-/

set_option backward.isDefEq.respectTransparency false in
/-- The canonical structure-module map is stable under Beck--Chevalley base
change through a cartesian square with open vertical arrows.  Sectionwise,
the ring maps around the square carry the multiplicative generator `1`
compatibly; the pullback equality only transports it between equal opens. -/
theorem unitToPushforwardUnit_verticalOpenBaseChange
    {P U X Y : Scheme} (f' : P ⟶ U) (iX : P ⟶ X)
    (iU : U ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion iX] [IsOpenImmersion iU]
    (H : IsPullback f' iX iU f) :
    (restrictUnitIso iU).inv ≫
        (restrictFunctor iU).map (unitToPushforwardUnit f) ≫
        (verticalOpenBaseChangeIso f' iX iU f H
          (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        (pushforward f').map (restrictUnitIso iX).hom =
      unitToPushforwardUnit f' := by
  apply hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro r
  simp only [Hom.comp_app, CategoryTheory.comp_apply,
    restrictUnitIso_inv_app_apply, restrictFunctor_map_app,
    unitToPushforwardUnit_app_apply,
    verticalOpenBaseChangeIso_hom_app_apply,
    pushforward_map_app]
  let e : Γ(X, f ⁻¹ᵁ iU ''ᵁ W) ≅ Γ(P, f' ⁻¹ᵁ W) :=
    X.presheaf.mapIso
        (eqToIso
          (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op ≪≫
      iX.appIso _
  have hcoeff :
      (iU.appIso W).inv ≫ f.app _ = f'.app W ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op,
      Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_comp_appLE, H.w, e]
  have hmaps :
      (iU.appIso W).inv ≫ f.app _ ≫
          X.presheaf.map
            (eqToHom
              (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
                H W)).op ≫
          (iX.appIso (f' ⁻¹ᵁ W)).hom =
        f'.app W := by
    calc
      _ = ((iU.appIso W).inv ≫ f.app _) ≫ e.hom := by
        simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
          eqToIso.hom, eqToHom_op, Category.assoc]
      _ = (f'.app W ≫ e.inv) ≫ e.hom :=
        congrArg (fun q => q ≫ e.hom) hcoeff
      _ = f'.app W := by simp
  exact ConcreteCategory.congr_hom hmaps r

set_option backward.isDefEq.respectTransparency false in
/-- The structure-sheaf comparison for an open immersion factors its section
map through restriction to the image and the canonical open-set isomorphism.
This small identity is the sectionwise core of the iterated-unit calculation
below. -/
theorem presheafMap_imagePreimage_comp_appIso_hom
    {V X : Scheme} (k : V ⟶ X) [IsOpenImmersion k] (U : X.Opens) :
    X.presheaf.map (homOfLE (k.image_preimage_le U)).op ≫
        (k.appIso (k ⁻¹ᵁ U)).hom =
      k.app U := by
  rw [← cancel_mono (k.appIso (k ⁻¹ᵁ U)).inv]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (k.app_appIso_inv U).symm

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward comparison associated to a reflexive equality is the
identity on every coefficient module. -/
theorem pushforwardCongr_refl_hom_app
    {X Y : Scheme} (f : X ⟶ Y) (M : X.Modules) :
    (pushforwardCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply hom_ext
  intro U
  rw [pushforwardCongr_hom_app_app, Hom.id_app]
  change M.presheaf.map _ = 𝟙 _
  rw [← M.presheaf.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Successively restricting the ambient structure module through two open
immersions agrees with restricting it along their named composite.  The
proof evaluates the two maps on the universal section `1`; linearity then
reduces the statement to functoriality of the structure-sheaf map. -/
theorem unitToPushforwardUnit_comp_restrictUnit
    {V X Y : Scheme} (k : V ⟶ X) (f : X ⟶ Y) (h : V ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion f] [IsOpenImmersion h]
    (hk : k ≫ f = h) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (pushforward f).map
          ((restrictAdjunction k).unit.app
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (pushforward k).map (restrictUnitIso k).hom) ≫
        (pushforwardComp k f).hom.app
          (SheafOfModules.unit V.ringCatSheaf) ≫
        (pushforwardCongr hk).hom.app
          (SheafOfModules.unit V.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
  subst h
  rw [pushforwardCongr_refl_hom_app, Category.comp_id]
  apply ((pushforward (k ≫ f)).obj
    (SheafOfModules.unit V.ringCatSheaf)).unitHomEquiv.injective
  ext U
  change
    (((pushforward f).map
          ((restrictAdjunction k).unit.app
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (pushforward k).map (restrictUnitIso k).hom) ≫
        (pushforwardComp k f).hom.app
          (SheafOfModules.unit V.ringCatSheaf)).val.app U)
      ((((pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv
            (SheafOfModules.unitToPushforwardObjUnit
              f.toRingCatSheafHom)).val U) =
      ((((pushforward (k ≫ f)).obj
          (SheafOfModules.unit V.ringCatSheaf)).unitHomEquiv
            (SheafOfModules.unitToPushforwardObjUnit
              (k ≫ f).toRingCatSheafHom)).val U)
  have hf :
      ((((pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv
            (SheafOfModules.unitToPushforwardObjUnit
              f.toRingCatSheafHom)).val U) = f.app U.unop 1 := by
    exact SheafOfModules.unitHomEquiv_apply_coe _ _ U
  have hkf :
      ((((pushforward (k ≫ f)).obj
          (SheafOfModules.unit V.ringCatSheaf)).unitHomEquiv
            (SheafOfModules.unitToPushforwardObjUnit
              (k ≫ f).toRingCatSheafHom)).val U) =
        (k ≫ f).app U.unop 1 := by
    exact SheafOfModules.unitHomEquiv_apply_coe _ _ U
  rw [hf, hkf]
  change
    Hom.app
      ((pushforward f).map
          ((restrictAdjunction k).unit.app
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (pushforward k).map (restrictUnitIso k).hom) ≫
        (pushforwardComp k f).hom.app
          (SheafOfModules.unit V.ringCatSheaf)) U.unop
        (f.app U.unop 1) =
      (k ≫ f).app U.unop 1
  rw [Hom.comp_app]
  simp only [pushforwardComp_hom_app_app, pushforward_map_app,
    Functor.map_comp, Hom.comp_app, restrictAdjunction_unit_app_app,
    CategoryTheory.comp_apply]
  change (k.appIso (k ⁻¹ᵁ f ⁻¹ᵁ U.unop)).hom
      (X.presheaf.map
        (homOfLE (k.image_preimage_le (f ⁻¹ᵁ U.unop))).op
        (f.app U.unop 1)) =
    (k ≫ f).app U.unop 1
  rw [← ConcreteCategory.comp_apply,
    presheafMap_imagePreimage_comp_appIso_hom]
  exact (congrArg (fun q ↦ q 1)
    (Scheme.Hom.comp_app k f U.unop)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The preceding iterated-unit identity is invariant under arbitrary chosen
unit trivializations on the intermediate and smallest opens.  Naturality of
extension by zero cancels those choices before applying the canonical
calculation. -/
theorem unitToPushforwardUnit_comp_pushforwardRestriction
    {V X Y : Scheme} (k : V ⟶ X) (f : X ⟶ Y) (h : V ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion f] [IsOpenImmersion h]
    (hk : k ≫ f = h) (F : X.Modules) (G : V.Modules)
    (eF : F ≅ SheafOfModules.unit X.ringCatSheaf)
    (eG : G ≅ SheafOfModules.unit V.ringCatSheaf) :
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (pushforward f).map eF.inv) ≫
      pushforwardRestrictionHomOfHom
        (f := f) (k := k) (h := h) hk F G
          (unitRestrictionHom k F G eF eG) =
    SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
      (pushforward h).map eG.inv := by
  have hlocal :
      (restrictFunctor k).map eF.inv ≫
          unitRestrictionHom k F G eF eG =
        (restrictUnitIso k).hom ≫ eG.inv := by
    unfold unitRestrictionHom
    rw [← Category.assoc, ← (restrictFunctor k).map_comp]
    simp
  have hnaturality :=
    pushforwardRestrictionHomOfHom_naturality
      (f := f) (k := k) (h := h) hk
      (restrictUnitIso k).hom
      (unitRestrictionHom k F G eF eG)
      eF.inv eG.inv hlocal
  have hunit :
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
          pushforwardRestrictionHomOfHom
            (f := f) (k := k) (h := h) hk
            (SheafOfModules.unit X.ringCatSheaf)
            (SheafOfModules.unit V.ringCatSheaf)
            (restrictUnitIso k).hom =
        SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
    simpa only [pushforwardRestrictionHomOfHom] using
      unitToPushforwardUnit_comp_restrictUnit k f h hk
  rw [Category.assoc, hnaturality]
  rw [← Category.assoc, hunit]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the canonical structure-module map back across an open
immersion and applying the adjunction counit recovers the standard
structure-sheaf trivialization on the open.  This is the local triangle
identity in the concrete coordinates used by `restrictUnitIso`. -/
theorem restrict_unitToPushforwardUnit_comp_counit
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).map
        (SheafOfModules.unitToPushforwardObjUnit
          f.toRingCatSheafHom) ≫
      (restrictAdjunction f).counit.app
        (SheafOfModules.unit X.ringCatSheaf) =
      (restrictUnitIso f).hom := by
  apply hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  simp only [Hom.comp_app, restrictFunctor_map_app,
    restrictAdjunction_counit_app_app, CategoryTheory.comp_apply]
  change X.presheaf.map
      (eqToHom (f.preimage_image_eq U).symm).op
        (f.app (f ''ᵁ U) x) =
    (f.appIso U).hom x
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom]

end AlgebraicGeometry.Scheme.Modules
