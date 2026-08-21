import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Module
import FLT.Mathlib.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Restricting affine tilde sheaves to principal opens

This file constructs the canonical restriction of an affine tilde sheaf
through its localized top sections.  The construction is independent of a
basis or a trivialization of the module.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- Top sections after restriction are the sections on the image open, with
the source-ring scalar structure transported by the affine morphism. -/
def restrictTildeTopLinearEquiv {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars f.hom).obj
        ((moduleSpecΓFunctor (R := S)).obj
          ((Scheme.Modules.restrictFunctor (Spec.map f)).obj (tilde M))) ≃ₗ[R]
      Γ(tilde M, Spec.map f ''ᵁ (⊤ : (Spec S).Opens)) where
  toFun := ((tilde M).restrictAppIso (Spec.map f) ⊤).hom
  invFun := ((tilde M).restrictAppIso (Spec.map f) ⊤).inv
  left_inv x :=
    ((tilde M).restrictAppIso (Spec.map f) ⊤).hom_inv_id_apply x
  right_inv x :=
    ((tilde M).restrictAppIso (Spec.map f) ⊤).inv_hom_id_apply x
  map_add' x y := map_add _ x y
  map_smul' a x := by
    change ((tilde M).restrictAppIso (Spec.map f) ⊤).hom (f a • x) =
      a • ((tilde M).restrictAppIso (Spec.map f) ⊤).hom x
    convert Scheme.Modules.restrictAppIso_smul_Spec
      (M := tilde M) (f := f) (U := (⊤ : (Spec S).Opens)) a x using 1
    rfl

variable {R S : CommRingCat.{u}} [Algebra R S]

/-- An affine module is recovered from top sections when it is isomorphic to
a tilde sheaf.  This packages the localizing argument used to construct
canonical affine restriction isomorphisms. -/
theorem isIso_fromTildeΓ_of_iso_tilde (L : (Spec R).Modules)
    (M : ModuleCat.{u} R) (e : L ≅ tilde M) :
    IsIso (Scheme.Modules.fromTildeΓ (R := R) L) := by
  exact (isIso_fromTildeΓ_iff_isLocalizing (R := R) L).2 <|
    isLocalizing_of_iso (R := R)
      ((modulesSpecToSheaf (R := R)).mapIso e.symm)
      (isLocalizing_tilde M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Global sections are faithful on morphisms whose source is recovered by
the affine tilde counit. -/
theorem Scheme.Modules.hom_ext_of_isIso_fromTildeΓ
    (A B : (Spec R).Modules)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) A)]
    {f g : A ⟶ B}
    (hΓ :
      (moduleSpecΓFunctor (R := R)).map f =
        (moduleSpecΓFunctor (R := R)).map g) :
    f = g := by
  apply (cancel_epi (Scheme.Modules.fromTildeΓ (R := R) A)).1
  let adj := tilde.adjunction (R := R)
  change adj.counit.app A ≫ f = adj.counit.app A ≫ g
  apply (adj.homEquiv
    ((moduleSpecΓFunctor (R := R)).obj A) B).injective
  have hcounit :
      adj.homEquiv ((moduleSpecΓFunctor (R := R)).obj A) ((𝟭 _).obj A)
          (adj.counit.app A) =
        𝟙 ((moduleSpecΓFunctor (R := R)).obj A) := by
    rw [← adj.homEquiv_symm_id A]
    exact Equiv.apply_symm_apply _ _
  simpa only [adj.homEquiv_naturality_right, hcounit,
    Category.id_comp] using hΓ

/-- The map on top sections of a morphism into a tilde sheaf, normalized by
the canonical identification of the target's top sections with its module. -/
def normalizedTildeTop {A : (Spec R).Modules} {M : ModuleCat.{u} R}
    (f : A ⟶ tilde M) :
    (moduleSpecΓFunctor (R := R)).obj A ⟶ M :=
  (moduleSpecΓFunctor (R := R)).map f ≫ (tilde.isoTop M).inv

/-- A morphism into an affine tilde sheaf is determined by its normalized top
sections whenever its source is recovered by the affine tilde counit. -/
theorem Scheme.Modules.hom_ext_of_normalizedTildeTop
    (A : (Spec R).Modules) (M : ModuleCat.{u} R)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) A)]
    {f g : A ⟶ tilde M}
    (h : normalizedTildeTop f = normalizedTildeTop g) :
    f = g := by
  apply Scheme.Modules.hom_ext_of_isIso_fromTildeΓ A (tilde M)
  apply (cancel_mono (tilde.isoTop M).inv).1
  exact h

/-- Normalized top sections carry a morphism of affine modules to its
underlying module homomorphism. -/
theorem normalizedTildeTop_comp_tildeMap
    {A : (Spec R).Modules} {M N : ModuleCat.{u} R}
    (f : A ⟶ tilde M) (g : M ⟶ N) :
    normalizedTildeTop (f ≫ tilde.map g) =
      normalizedTildeTop f ≫ g := by
  have hmap :
      (moduleSpecΓFunctor (R := R)).map (tilde.map g) ≫
          (tilde.isoTop N).inv =
        (tilde.isoTop M).inv ≫ g := by
    apply (cancel_epi (tilde.isoTop M).hom).1
    simp only [Iso.hom_inv_id_assoc]
    change tilde.toOpen M ⊤ ≫
        ((modulesSpecToSheaf (R := R)).map (tilde.map g)).1.app (.op ⊤) ≫
          (tilde.isoTop N).inv = g
    erw [tilde.toOpen_map_app_assoc]
    change g ≫ ((tilde.isoTop N).hom ≫ (tilde.isoTop N).inv) = g
    rw [Iso.hom_inv_id, Category.comp_id]
  simp only [normalizedTildeTop, Functor.map_comp, Category.assoc, hmap]
  rfl

/-- The universal map from an affine module to the top sections of its tilde
sheaf restricted along an Away localization. -/
def awayRestrictionGlobalMap (r : R) [IsLocalization.Away r S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (M : ModuleCat.{u} R) :
    M →ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((moduleSpecΓFunctor (R := S)).obj
        ((Scheme.Modules.restrictFunctor
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M))) := by
  let f : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
  letI : IsOpenImmersion (Spec.map f) := by
    dsimp only [f]
    exact IsOpenImmersion.of_isLocalization r
  let U : (Spec R).Opens := Spec.map f ''ᵁ (⊤ : (Spec S).Opens)
  exact (restrictTildeTopLinearEquiv f M).symm.toLinearMap.comp
    (tilde.toOpen M U).hom

/-- A restriction framed by source and target affine-module coordinates maps
each localized generator by applying the source coordinate, the affine ring
map, and the inverse target coordinate. -/
theorem normalizedTildeTop_restrictFrame_apply
    (r : R) [IsLocalization.Away r S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (eR : M ≅ ModuleCat.of R R) (eS : N ≅ ModuleCat.of S S)
    (m : M) :
    normalizedTildeTop
        ((Scheme.Modules.restrictFunctor
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
              (tilde.map eR.hom) ≫
          (Scheme.Modules.restrictUnitIso
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom ≫
          tilde.map eS.inv)
        ((awayRestrictionGlobalMap (R := R) (S := S) r M) m) =
      eS.inv (algebraMap R S (eR.hom m)) := by
  simp [normalizedTildeTop, awayRestrictionGlobalMap,
    restrictTildeTopLinearEquiv]
  change (tilde.isoTop N).inv
      ((tilde.map eS.inv).app ⊤
        ((Scheme.Modules.restrictUnitIso
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom.app ⊤
          ((tilde.map eR.hom).app
            (Spec.map (CommRingCat.ofHom (algebraMap R S)) ''ᵁ ⊤)
            ((tilde.toOpen M
              (Spec.map (CommRingCat.ofHom (algebraMap R S)) ''ᵁ ⊤)) m)))) = _
  conv in ((tilde.map eR.hom).app _ _) =>
    erw [Scheme.Modules.tildeMap_toOpen_apply]
  erw [Scheme.Modules.restrictUnitIso_hom_app_apply]
  conv in
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).appIso ⊤).hom _ =>
    erw [Scheme.Modules.specMap_appIso_hom_tildeSelf_toOpen_apply]
  conv in ((tilde.map eS.inv).app ⊤ _) =>
    erw [Scheme.Modules.tildeMap_toOpen_apply]
  change (tilde.isoTop N).inv
      ((tilde.toOpen N ⊤)
        (eS.inv (algebraMap R S (eR.hom m)))) = _
  change (tilde.isoTop N).inv
      ((tilde.isoTop N).hom
        (eS.inv (algebraMap R S (eR.hom m)))) = _
  exact Iso.hom_inv_id_apply (tilde.isoTop N) _

/-- The top-section map for an Away restriction has the localized-module
universal property. -/
theorem awayRestrictionGlobalMap_isLocalizedModule
    (r : R) [IsLocalization.Away r S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (M : ModuleCat.{u} R) :
    IsLocalizedModule (.powers r)
      (awayRestrictionGlobalMap (R := R) (S := S) r M) := by
  let f : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
  letI : IsOpenImmersion (Spec.map f) := by
    dsimp only [f]
    exact IsOpenImmersion.of_isLocalization r
  let U : (Spec R).Opens := Spec.map f ''ᵁ (⊤ : (Spec S).Opens)
  have hU : U = PrimeSpectrum.basicOpen r := by
    dsimp only [U, f]
    rw [Scheme.Hom.image_top_eq_opensRange]
    apply SetLike.ext'
    exact PrimeSpectrum.localization_away_comap_range S r
  letI : IsLocalizedModule (.powers r) (tilde.toOpen M U).hom := by
    rw [hU]
    infer_instance
  change IsLocalizedModule (.powers r)
    ((restrictTildeTopLinearEquiv f M).symm.toLinearMap.comp
      (tilde.toOpen M U).hom)
  exact IsLocalizedModule.of_linearEquiv (.powers r)
    (tilde.toOpen M U).hom (restrictTildeTopLinearEquiv f M).symm

/-- Top sections of the restricted tilde sheaf are canonically the scalar
extension of the original module. -/
def awayRestrictionGlobalEquivTensor (r : R) [IsLocalization.Away r S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (M : ModuleCat.{u} R) :
    (moduleSpecΓFunctor (R := S)).obj
        ((Scheme.Modules.restrictFunctor
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M)) ≃ₗ[S]
      TensorProduct R S M := by
  let G : ModuleCat.{u} S :=
    (moduleSpecΓFunctor (R := S)).obj
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M))
  let GR : ModuleCat.{u} R :=
    (ModuleCat.restrictScalars (algebraMap R S)).obj G
  letI : IsScalarTower R S GR :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI := awayRestrictionGlobalMap_isLocalizedModule
    (R := R) (S := S) r M
  exact (IsLocalizedModule.isBaseChange (.powers r) S
    (awayRestrictionGlobalMap (R := R) (S := S) r M)).equiv.symm

set_option maxHeartbeats 2000000 in
-- The affine counit and the base-change equivalence create a large dependent term.
/-- Restriction of an affine tilde sheaf along an Away localization is the
tilde sheaf of scalar extension.  Invertibility of the affine counit may be
proved independently by transporting the localizing property across an
isomorphism. -/
def tildeRestrictIsoAway (r : R) [IsLocalization.Away r S]
    (M : ModuleCat.{u} R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [IsIso (Scheme.Modules.fromTildeΓ (R := S)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M)))] :
    (Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M) ≅
      tilde (ModuleCat.of S (TensorProduct R S M)) := by
  let L : (Spec S).Modules :=
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M)
  let G : ModuleCat.{u} S := (moduleSpecΓFunctor (R := S)).obj L
  let e : G ≅ ModuleCat.of S (TensorProduct R S M) :=
    (awayRestrictionGlobalEquivTensor (R := R) (S := S) r M).toModuleIso
  exact (asIso (Scheme.Modules.fromTildeΓ (R := S) L)).symm ≪≫
    (tilde.functor S).mapIso e

set_option maxHeartbeats 2000000 in
-- Normalizing the counit on a pure tensor requires elaborating the same affine tower.
/-- The canonical Away restriction sends each original section to its pure
tensor after identifying the target's top sections with scalar extension. -/
theorem tildeRestrictIsoAway_normalizedTildeTop_apply
    (r : R) [IsLocalization.Away r S]
    (M : ModuleCat.{u} R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [IsIso (Scheme.Modules.fromTildeΓ (R := S)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M)))]
    (m : M) :
    normalizedTildeTop
        (tildeRestrictIsoAway (R := R) (S := S) r M).hom
        ((awayRestrictionGlobalMap (R := R) (S := S) r M) m) =
      (TensorProduct.tmul R (1 : S) m : TensorProduct R S M) := by
  let a : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
  let j : Spec S ⟶ Spec R := Spec.map a
  let L : (Spec S).Modules :=
    (Scheme.Modules.restrictFunctor j).obj (tilde M)
  let G : ModuleCat.{u} S :=
    (moduleSpecΓFunctor (R := S)).obj L
  let BC : ModuleCat.{u} S :=
    ModuleCat.of S (TensorProduct R S M)
  let alpha : M →ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj G :=
    awayRestrictionGlobalMap (R := R) (S := S) r M
  letI : IsScalarTower R S
      ((ModuleCat.restrictScalars (algebraMap R S)).obj G) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalizedModule (.powers r) alpha :=
    awayRestrictionGlobalMap_isLocalizedModule
      (R := R) (S := S) r M
  have hbc : IsBaseChange S alpha :=
    IsLocalizedModule.isBaseChange (.powers r) S alpha
  let eBC : G ≅ BC := hbc.equiv.symm.toModuleIso
  let counit : tilde G ⟶ L :=
    Scheme.Modules.fromTildeΓ (R := S) L
  let psi : L ≅ tilde BC :=
    tildeRestrictIsoAway (R := R) (S := S) r M
  let Utop : (Spec S).Opens := ⊤
  let F := modulesSpecToSheaf (R := S)
  have hPsiInvTop :
      tilde.toOpen BC Utop ≫
          (F.map psi.inv).1.app (.op Utop) = eBC.inv := by
    change tilde.toOpen BC Utop ≫
        (F.map ((tilde.functor S).map eBC.inv ≫ counit)).1.app (.op Utop) =
      eBC.inv
    rw [Functor.map_comp]
    change tilde.toOpen BC Utop ≫
        (F.map (tilde.map eBC.inv)).1.app (.op Utop) ≫
          (F.map counit).1.app (.op Utop) = eBC.inv
    erw [tilde.toOpen_map_app_assoc]
    dsimp only [G, counit]
    erw [Scheme.Modules.toOpen_fromTildeΓ_app (R := S) L Utop]
    change eBC.inv ≫ 𝟙 G = eBC.inv
    simp
  have hBCPure :
      eBC.inv.hom (TensorProduct.tmul R (1 : S) m) = alpha m := by
    change hbc.equiv (TensorProduct.tmul R (1 : S) m) = alpha m
    simpa only [one_smul] using hbc.equiv_tmul (1 : S) m
  have hPsiInvPure :
      ((F.map psi.inv).1.app (.op Utop))
          ((tilde.toOpen BC Utop)
            (TensorProduct.tmul R (1 : S) m)) = alpha m := by
    change (tilde.toOpen BC Utop ≫
      (F.map psi.inv).1.app (.op Utop)).hom
        (TensorProduct.tmul R (1 : S) m) = alpha m
    rw [hPsiInvTop]
    exact hBCPure
  have hPsiTop :
      ((F.map psi.hom).1.app (.op Utop)) (alpha m) =
        (tilde.toOpen BC Utop)
          (TensorProduct.tmul R (1 : S) m) := by
    let q := (F.map psi.inv).1.app (.op Utop)
    apply (ConcreteCategory.bijective_of_isIso q).1
    rw [hPsiInvPure]
    change q (((F.map psi.hom).1.app (.op Utop)) (alpha m)) = alpha m
    dsimp [q]
    simp only [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
    simp
  change (tilde.isoTop BC).inv
      (((F.map psi.hom).1.app (.op Utop)) (alpha m)) = _
  rw [hPsiTop]
  simp [Utop, tilde.isoTop]

end AlgebraicGeometry
