import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialTilde
import FLT.Mathlib.AlgebraicGeometry.Modules.TildeAway

/-!
# Canonical restriction of N25 affine differentials

The actual Kähler tilde sheaves on the four coordinate charts restrict
canonically to the actual Kähler tilde sheaves on ordered pair overlaps.
The residue frames are used only to establish affine recovery from top
sections; the resulting restriction isomorphisms are defined by localization
and formally étale base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialRestriction

open RationalPointsN25QuotientTwoCanonicalDifferentialTilde
open RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
open RationalPointsN25QuotientTwoCanonicalDifferentialCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoTwistingDescent
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingSheafGluing
open RationalPointsN25QuotientTwoTwistingTransition
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory

/-- The first geometric overlap projection is the spectrum map of the
explicit chart localization. -/
theorem coordinateOverlapToLeft_eq_specMap (i j : Fin 4) :
    coordinateOverlapToLeft i j =
      Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j)) := by
  unfold coordinateOverlapToLeft
  rw [coordinateChosenPullbackIso_inv_p₁]
  rfl

instance coordinateChartToLeftOverlapSpecIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j))) := by
  rw [← coordinateOverlapToLeft_eq_specMap]
  infer_instance

/-- The restriction to the first explicit affine overlap is recovered from
its top sections.  The residue frame supplies only this proposition-valued
affine-recovery certificate. -/
noncomputable instance coordinateKaehlerRestrictLeftSpecFromTildeΓIsIso
    (i j : Fin 4) :
    IsIso (Scheme.Modules.fromTildeΓ
      (R := .of (coordinateOverlapRing i j))
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom
          (coordinateChartToLeftOverlapRingHom i j)))).obj
            (chartCoordinateKaehlerDifferentialSheaf i))) := by
  let T := coordinateOverlapRing i j
  let g : CommRingCat.of (ChartCoordinateRing i) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (coordinateChartToLeftOverlapRingHom i j)
  have hg : coordinateOverlapToLeft i j = Spec.map g :=
    coordinateOverlapToLeft_eq_specMap i j
  let frameRaw :
      (Scheme.Modules.restrictFunctor (Spec.map g)).obj
          (chartCoordinateKaehlerDifferentialSheaf i) ≅
        coordinateOverlapTwistModule (-1) i j :=
    (Scheme.Modules.restrictFunctorCongr hg.symm).app
        (chartCoordinateKaehlerDifferentialSheaf i) ≪≫
      (Scheme.Modules.restrictFunctor
        (coordinateOverlapToLeft i j)).mapIso
          (chartCoordinateKaehlerDifferentialTildeIso i) ≪≫
      coordinateRestrictLeftIso (-1) i j
  have hTwistObj : coordinateOverlapTwistModule (-1) i j =
      tilde (ModuleCat.of T T) := rfl
  let frameSpec :
      (Scheme.Modules.restrictFunctor (Spec.map g)).obj
          (chartCoordinateKaehlerDifferentialSheaf i) ≅
        tilde (ModuleCat.of T T) :=
    frameRaw ≪≫ eqToIso hTwistObj
  exact isIso_fromTildeΓ_of_iso_tilde _ (ModuleCat.of T T) frameSpec

/-- Restriction along the first explicit spectrum map is canonically
localization of Kähler differentials followed by formally étale base change. -/
def coordinateKaehlerRestrictLeftSpecCanonicalIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j)))).obj
        (chartCoordinateKaehlerDifferentialSheaf i) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j := by
  let S := ChartCoordinateRing i
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
    (coordinateClass_mem_degreeOne j)
  letI : Algebra S T := (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  letI : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (.powers r)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap S T)))).obj
          (tilde (ModuleCat.of S Ω[S⁄k])))) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom
          (coordinateChartToLeftOverlapRingHom i j)))).obj
            (chartCoordinateKaehlerDifferentialSheaf i)))
    infer_instance
  let e : ModuleCat.of T (TensorProduct S T Ω[S⁄k]) ≅
      ModuleCat.of T Ω[T⁄k] :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S T).toModuleIso
  exact tildeRestrictIsoAway (R := .of S) (S := .of T) r
      (ModuleCat.of S Ω[S⁄k]) ≪≫
    (tilde.functor (.of T)).mapIso e

/-- The first residue frame gives an explicit presentation of restriction
along the spectrum localization. -/
def coordinateKaehlerRestrictLeftSpecResidueFrameIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j)))).obj
        (chartCoordinateKaehlerDifferentialSheaf i) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j)))).mapIso
          (chartCoordinateKaehlerDifferentialTildeIso i) ≪≫
    Scheme.Modules.restrictUnitIso
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j))) ≪≫
    (coordinateOverlapLeftKaehlerDifferentialTildeIso i j).symm

/-- The source module map whose localization generates top sections of the
first explicit overlap restriction. -/
def coordinateKaehlerLeftLocalizationGlobalMap (i j : Fin 4) :
    Ω[ChartCoordinateRing i⁄k] →ₗ[ChartCoordinateRing i]
      (ModuleCat.restrictScalars
        (coordinateChartToLeftOverlapRingHom i j)).obj
        ((moduleSpecΓFunctor (R := .of (coordinateOverlapRing i j))).obj
          ((Scheme.Modules.restrictFunctor
            (Spec.map (CommRingCat.ofHom
              (coordinateChartToLeftOverlapRingHom i j)))).obj
                (chartCoordinateKaehlerDifferentialSheaf i))) := by
  let S := ChartCoordinateRing i
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
    (coordinateClass_mem_degreeOne j)
  letI : Algebra S T := (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  exact awayRestrictionGlobalMap (R := .of S) (S := .of T) r
    (ModuleCat.of S Ω[S⁄k])

set_option maxHeartbeats 300000 in
-- The formally étale base-change equivalence carries the full chart localization tower.
/-- On localization generators, the first canonical restriction is the
functorial map on Kähler differentials. -/
theorem coordinateKaehlerRestrictLeftSpecCanonicalIso_normalizedTop_apply
    (i j : Fin 4) (omega : Ω[ChartCoordinateRing i⁄k]) :
    normalizedTildeTop
        (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom
        (coordinateKaehlerLeftLocalizationGlobalMap i j omega) =
      coordinateOverlapLeftKaehlerDifferentialMap i j omega := by
  let S := ChartCoordinateRing i
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
    (coordinateClass_mem_degreeOne j)
  letI : Algebra S T := (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  letI : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (.powers r)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap S T)))).obj
          (tilde (ModuleCat.of S Ω[S⁄k])))) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom
          (coordinateChartToLeftOverlapRingHom i j)))).obj
            (chartCoordinateKaehlerDifferentialSheaf i)))
    infer_instance
  change normalizedTildeTop
      ((tildeRestrictIsoAway (R := .of S) (S := .of T) r
          (ModuleCat.of S Ω[S⁄k])).hom ≫
        tilde.map
          (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
            k S T).toModuleIso.hom)
      ((awayRestrictionGlobalMap (R := .of S) (S := .of T) r
        (ModuleCat.of S Ω[S⁄k])) omega) = _
  rw [normalizedTildeTop_comp_tildeMap]
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S T
      (normalizedTildeTop
        (tildeRestrictIsoAway (R := .of S) (S := .of T) r
          (ModuleCat.of S Ω[S⁄k])).hom
        ((awayRestrictionGlobalMap (R := .of S) (S := .of T) r
          (ModuleCat.of S Ω[S⁄k])) omega)) = _
  rw [tildeRestrictIsoAway_normalizedTildeTop_apply]
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S T
      (1 ⊗ₜ[S] omega) = _
  simp [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul,
    coordinateOverlapLeftKaehlerDifferentialMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On localization generators, the first residue-frame restriction agrees
with the functorial map on Kähler differentials. -/
theorem coordinateKaehlerRestrictLeftSpecResidueFrameIso_normalizedTop_apply
    (i j : Fin 4) (omega : Ω[ChartCoordinateRing i⁄k]) :
    normalizedTildeTop
        (coordinateKaehlerRestrictLeftSpecResidueFrameIso i j).hom
        (coordinateKaehlerLeftLocalizationGlobalMap i j omega) =
      coordinateOverlapLeftKaehlerDifferentialMap i j omega := by
  let S := ChartCoordinateRing i
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
    (coordinateClass_mem_degreeOne j)
  letI : Algebra S T := (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  have h := normalizedTildeTop_restrictFrame_apply
    (R := .of S) (S := .of T) r
    (ModuleCat.of S Ω[S⁄k])
    (ModuleCat.of T Ω[T⁄k])
    (chartCoordinateKaehlerDifferentialEquiv i).toModuleIso
    (coordinateOverlapLeftKaehlerDifferentialEquiv i j).toModuleIso omega
  dsimp only [S, T, r] at h
  let frameAlg :
      (Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap S T)))).obj
          (chartCoordinateKaehlerDifferentialSheaf i) ≅
        coordinateOverlapKaehlerDifferentialSheaf i j :=
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap S T)))).mapIso
        (chartCoordinateKaehlerDifferentialTildeIso i) ≪≫
      Scheme.Modules.restrictUnitIso
        (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≪≫
      (coordinateOverlapLeftKaehlerDifferentialTildeIso i j).symm
  have hframe : coordinateKaehlerRestrictLeftSpecResidueFrameIso i j =
      frameAlg := rfl
  calc
    normalizedTildeTop
        (coordinateKaehlerRestrictLeftSpecResidueFrameIso i j).hom
        (coordinateKaehlerLeftLocalizationGlobalMap i j omega) =
      (coordinateOverlapLeftKaehlerDifferentialEquiv i j).toModuleIso.inv
        (algebraMap S T
          ((chartCoordinateKaehlerDifferentialEquiv i).toModuleIso.hom omega)) := by
        rw [hframe]
        dsimp only [S, T, coordinateKaehlerLeftLocalizationGlobalMap,
          chartCoordinateKaehlerDifferentialTildeIso,
          coordinateOverlapLeftKaehlerDifferentialTildeIso,
          Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
          Functor.mapIso_inv, tilde.functor_map,
          toAlgebra_algebraMap, frameAlg]
        convert h using 1
        all_goals rfl
    _ = coordinateOverlapLeftKaehlerDifferentialMap i j omega := by
      change (coordinateOverlapLeftKaehlerDifferentialEquiv i j).symm
          (coordinateChartToLeftOverlapRingHom i j
            (chartCoordinateKaehlerDifferentialEquiv i omega)) = _
      rw [← coordinateOverlapLeftKaehlerDifferentialEquiv_map]
      simp

/-- The canonical first restriction is the same isomorphism as the explicit
residue-frame presentation. -/
theorem coordinateKaehlerRestrictLeftSpecCanonicalIso_eq_residueFrameIso
    (i j : Fin 4) :
    coordinateKaehlerRestrictLeftSpecCanonicalIso i j =
      coordinateKaehlerRestrictLeftSpecResidueFrameIso i j := by
  let S := ChartCoordinateRing i
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
    (coordinateClass_mem_degreeOne j)
  letI : Algebra S T := (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  let A : (Spec (.of T)).Modules :=
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j)))).obj
          (chartCoordinateKaehlerDifferentialSheaf i)
  let G : ModuleCat T := (moduleSpecΓFunctor (R := .of T)).obj A
  let alpha : Ω[S⁄k] →ₗ[S]
      (ModuleCat.restrictScalars (algebraMap S T)).obj G :=
    coordinateKaehlerLeftLocalizationGlobalMap i j
  letI : IsScalarTower S T
      ((ModuleCat.restrictScalars (algebraMap S T)).obj G) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalizedModule (.powers r) alpha := by
    dsimp only [alpha, G, A]
    exact awayRestrictionGlobalMap_isLocalizedModule
      (R := .of S) (S := .of T) r (ModuleCat.of S Ω[S⁄k])
  have hbc : IsBaseChange T alpha :=
    IsLocalizedModule.isBaseChange (.powers r) T alpha
  apply Iso.ext
  apply Scheme.Modules.hom_ext_of_normalizedTildeTop A
    (ModuleCat.of T Ω[T⁄k])
  apply ModuleCat.hom_ext
  exact hbc.algHom_ext
    (normalizedTildeTop
      (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom).hom
    (normalizedTildeTop
      (coordinateKaehlerRestrictLeftSpecResidueFrameIso i j).hom).hom
    (fun omega => by
      change normalizedTildeTop
          (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom
          (coordinateKaehlerLeftLocalizationGlobalMap i j omega) =
        normalizedTildeTop
          (coordinateKaehlerRestrictLeftSpecResidueFrameIso i j).hom
          (coordinateKaehlerLeftLocalizationGlobalMap i j omega)
      rw [coordinateKaehlerRestrictLeftSpecCanonicalIso_normalizedTop_apply,
        coordinateKaehlerRestrictLeftSpecResidueFrameIso_normalizedTop_apply])

/-- Canonical restriction from the first named geometric chart projection. -/
def coordinateKaehlerRestrictLeftCanonicalIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).obj
        (chartCoordinateKaehlerDifferentialSheaf i) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  (Scheme.Modules.restrictFunctorCongr
      (coordinateOverlapToLeft_eq_specMap i j)).app
        (chartCoordinateKaehlerDifferentialSheaf i) ≪≫
    coordinateKaehlerRestrictLeftSpecCanonicalIso i j

/-- The second geometric overlap projection is the spectrum map of the
explicit chart localization. -/
theorem coordinateOverlapToRight_eq_specMap (i j : Fin 4) :
    coordinateOverlapToRight i j =
      Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j)) := by
  unfold coordinateOverlapToRight
  rw [coordinateChosenPullbackIso_inv_p₂]
  rfl

instance coordinateChartToRightOverlapSpecIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j))) := by
  rw [← coordinateOverlapToRight_eq_specMap]
  infer_instance

/-- The restriction to the second explicit affine overlap is recovered from
its top sections.  The residue frame supplies only this proposition-valued
affine-recovery certificate. -/
noncomputable instance coordinateKaehlerRestrictRightSpecFromTildeΓIsIso
    (i j : Fin 4) :
    IsIso (Scheme.Modules.fromTildeΓ
      (R := .of (coordinateOverlapRing i j))
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom
          (coordinateChartToRightOverlapRingHom i j)))).obj
            (chartCoordinateKaehlerDifferentialSheaf j))) := by
  let T := coordinateOverlapRing i j
  let g : CommRingCat.of (ChartCoordinateRing j) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (coordinateChartToRightOverlapRingHom i j)
  have hg : coordinateOverlapToRight i j = Spec.map g :=
    coordinateOverlapToRight_eq_specMap i j
  let frameRaw :
      (Scheme.Modules.restrictFunctor (Spec.map g)).obj
          (chartCoordinateKaehlerDifferentialSheaf j) ≅
        coordinateOverlapTwistModule (-1) i j :=
    (Scheme.Modules.restrictFunctorCongr hg.symm).app
        (chartCoordinateKaehlerDifferentialSheaf j) ≪≫
      (Scheme.Modules.restrictFunctor
        (coordinateOverlapToRight i j)).mapIso
          (chartCoordinateKaehlerDifferentialTildeIso j) ≪≫
      coordinateRestrictRightIso (-1) i j
  have hTwistObj : coordinateOverlapTwistModule (-1) i j =
      tilde (ModuleCat.of T T) := rfl
  let frameSpec :
      (Scheme.Modules.restrictFunctor (Spec.map g)).obj
          (chartCoordinateKaehlerDifferentialSheaf j) ≅
        tilde (ModuleCat.of T T) :=
    frameRaw ≪≫ eqToIso hTwistObj
  exact isIso_fromTildeΓ_of_iso_tilde _ (ModuleCat.of T T) frameSpec

/-- Restriction along the second explicit spectrum map is canonically
localization of Kähler differentials followed by formally étale base change. -/
def coordinateKaehlerRestrictRightSpecCanonicalIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j)))).obj
        (chartCoordinateKaehlerDifferentialSheaf j) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j := by
  let S := ChartCoordinateRing j
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne i)
  letI : Algebra S T := (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  letI : IsScalarTower k S T :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (.powers r)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap S T)))).obj
          (tilde (ModuleCat.of S Ω[S⁄k])))) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom
          (coordinateChartToRightOverlapRingHom i j)))).obj
            (chartCoordinateKaehlerDifferentialSheaf j)))
    infer_instance
  let e : ModuleCat.of T (TensorProduct S T Ω[S⁄k]) ≅
      ModuleCat.of T Ω[T⁄k] :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S T).toModuleIso
  exact tildeRestrictIsoAway (R := .of S) (S := .of T) r
      (ModuleCat.of S Ω[S⁄k]) ≪≫
    (tilde.functor (.of T)).mapIso e

/-- The second residue frame gives an explicit presentation of restriction
along the spectrum localization. -/
def coordinateKaehlerRestrictRightSpecResidueFrameIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j)))).obj
        (chartCoordinateKaehlerDifferentialSheaf j) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j)))).mapIso
          (chartCoordinateKaehlerDifferentialTildeIso j) ≪≫
    Scheme.Modules.restrictUnitIso
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j))) ≪≫
    (coordinateOverlapRightKaehlerDifferentialTildeIso i j).symm

/-- The source module map whose localization generates top sections of the
second explicit overlap restriction. -/
def coordinateKaehlerRightLocalizationGlobalMap (i j : Fin 4) :
    Ω[ChartCoordinateRing j⁄k] →ₗ[ChartCoordinateRing j]
      (ModuleCat.restrictScalars
        (coordinateChartToRightOverlapRingHom i j)).obj
        ((moduleSpecΓFunctor (R := .of (coordinateOverlapRing i j))).obj
          ((Scheme.Modules.restrictFunctor
            (Spec.map (CommRingCat.ofHom
              (coordinateChartToRightOverlapRingHom i j)))).obj
                (chartCoordinateKaehlerDifferentialSheaf j))) := by
  let S := ChartCoordinateRing j
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne i)
  letI : Algebra S T := (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  exact awayRestrictionGlobalMap (R := .of S) (S := .of T) r
    (ModuleCat.of S Ω[S⁄k])

set_option maxHeartbeats 300000 in
-- The right chart carries the same localization tower with the reversed denominator order.
/-- On localization generators, the second canonical restriction is the
functorial map on Kähler differentials. -/
theorem coordinateKaehlerRestrictRightSpecCanonicalIso_normalizedTop_apply
    (i j : Fin 4) (omega : Ω[ChartCoordinateRing j⁄k]) :
    normalizedTildeTop
        (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom
        (coordinateKaehlerRightLocalizationGlobalMap i j omega) =
      coordinateOverlapRightKaehlerDifferentialMap i j omega := by
  let S := ChartCoordinateRing j
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne i)
  letI : Algebra S T := (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  letI : IsScalarTower k S T :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (.powers r)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap S T)))).obj
          (tilde (ModuleCat.of S Ω[S⁄k])))) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := .of T)
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom
          (coordinateChartToRightOverlapRingHom i j)))).obj
            (chartCoordinateKaehlerDifferentialSheaf j)))
    infer_instance
  change normalizedTildeTop
      ((tildeRestrictIsoAway (R := .of S) (S := .of T) r
          (ModuleCat.of S Ω[S⁄k])).hom ≫
        tilde.map
          (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
            k S T).toModuleIso.hom)
      ((awayRestrictionGlobalMap (R := .of S) (S := .of T) r
        (ModuleCat.of S Ω[S⁄k])) omega) = _
  rw [normalizedTildeTop_comp_tildeMap]
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S T
      (normalizedTildeTop
        (tildeRestrictIsoAway (R := .of S) (S := .of T) r
          (ModuleCat.of S Ω[S⁄k])).hom
        ((awayRestrictionGlobalMap (R := .of S) (S := .of T) r
          (ModuleCat.of S Ω[S⁄k])) omega)) = _
  rw [tildeRestrictIsoAway_normalizedTildeTop_apply]
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S T
      (1 ⊗ₜ[S] omega) = _
  simp [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul,
    coordinateOverlapRightKaehlerDifferentialMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On localization generators, the second residue-frame restriction agrees
with the functorial map on Kähler differentials. -/
theorem coordinateKaehlerRestrictRightSpecResidueFrameIso_normalizedTop_apply
    (i j : Fin 4) (omega : Ω[ChartCoordinateRing j⁄k]) :
    normalizedTildeTop
        (coordinateKaehlerRestrictRightSpecResidueFrameIso i j).hom
        (coordinateKaehlerRightLocalizationGlobalMap i j omega) =
      coordinateOverlapRightKaehlerDifferentialMap i j omega := by
  let S := ChartCoordinateRing j
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne i)
  letI : Algebra S T := (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  have h := normalizedTildeTop_restrictFrame_apply
    (R := .of S) (S := .of T) r
    (ModuleCat.of S Ω[S⁄k])
    (ModuleCat.of T Ω[T⁄k])
    (chartCoordinateKaehlerDifferentialEquiv j).toModuleIso
    (coordinateOverlapRightKaehlerDifferentialEquiv i j).toModuleIso omega
  dsimp only [S, T, r] at h
  let frameAlg :
      (Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap S T)))).obj
          (chartCoordinateKaehlerDifferentialSheaf j) ≅
        coordinateOverlapKaehlerDifferentialSheaf i j :=
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap S T)))).mapIso
        (chartCoordinateKaehlerDifferentialTildeIso j) ≪≫
      Scheme.Modules.restrictUnitIso
        (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≪≫
      (coordinateOverlapRightKaehlerDifferentialTildeIso i j).symm
  have hframe : coordinateKaehlerRestrictRightSpecResidueFrameIso i j =
      frameAlg := rfl
  calc
    normalizedTildeTop
        (coordinateKaehlerRestrictRightSpecResidueFrameIso i j).hom
        (coordinateKaehlerRightLocalizationGlobalMap i j omega) =
      (coordinateOverlapRightKaehlerDifferentialEquiv i j).toModuleIso.inv
        (algebraMap S T
          ((chartCoordinateKaehlerDifferentialEquiv j).toModuleIso.hom omega)) := by
        rw [hframe]
        dsimp only [S, T, coordinateKaehlerRightLocalizationGlobalMap,
          chartCoordinateKaehlerDifferentialTildeIso,
          coordinateOverlapRightKaehlerDifferentialTildeIso,
          Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
          Functor.mapIso_inv, tilde.functor_map,
          toAlgebra_algebraMap, frameAlg]
        convert h using 1
        all_goals rfl
    _ = coordinateOverlapRightKaehlerDifferentialMap i j omega := by
      change (coordinateOverlapRightKaehlerDifferentialEquiv i j).symm
          (coordinateChartToRightOverlapRingHom i j
            (chartCoordinateKaehlerDifferentialEquiv j omega)) = _
      rw [← coordinateOverlapRightKaehlerDifferentialEquiv_map]
      simp

/-- The canonical second restriction is the same isomorphism as the explicit
residue-frame presentation. -/
theorem coordinateKaehlerRestrictRightSpecCanonicalIso_eq_residueFrameIso
    (i j : Fin 4) :
    coordinateKaehlerRestrictRightSpecCanonicalIso i j =
      coordinateKaehlerRestrictRightSpecResidueFrameIso i j := by
  let S := ChartCoordinateRing j
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne i)
  letI : Algebra S T := (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization r
  let A : (Spec (.of T)).Modules :=
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j)))).obj
          (chartCoordinateKaehlerDifferentialSheaf j)
  let G : ModuleCat T := (moduleSpecΓFunctor (R := .of T)).obj A
  let alpha : Ω[S⁄k] →ₗ[S]
      (ModuleCat.restrictScalars (algebraMap S T)).obj G :=
    coordinateKaehlerRightLocalizationGlobalMap i j
  letI : IsScalarTower S T
      ((ModuleCat.restrictScalars (algebraMap S T)).obj G) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalizedModule (.powers r) alpha := by
    dsimp only [alpha, G, A]
    exact awayRestrictionGlobalMap_isLocalizedModule
      (R := .of S) (S := .of T) r (ModuleCat.of S Ω[S⁄k])
  have hbc : IsBaseChange T alpha :=
    IsLocalizedModule.isBaseChange (.powers r) T alpha
  apply Iso.ext
  apply Scheme.Modules.hom_ext_of_normalizedTildeTop A
    (ModuleCat.of T Ω[T⁄k])
  apply ModuleCat.hom_ext
  exact hbc.algHom_ext
    (normalizedTildeTop
      (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom).hom
    (normalizedTildeTop
      (coordinateKaehlerRestrictRightSpecResidueFrameIso i j).hom).hom
    (fun omega => by
      change normalizedTildeTop
          (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom
          (coordinateKaehlerRightLocalizationGlobalMap i j omega) =
        normalizedTildeTop
          (coordinateKaehlerRestrictRightSpecResidueFrameIso i j).hom
          (coordinateKaehlerRightLocalizationGlobalMap i j omega)
      rw [coordinateKaehlerRestrictRightSpecCanonicalIso_normalizedTop_apply,
        coordinateKaehlerRestrictRightSpecResidueFrameIso_normalizedTop_apply])

/-- Canonical restriction from the second named geometric chart projection. -/
def coordinateKaehlerRestrictRightCanonicalIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).obj
        (chartCoordinateKaehlerDifferentialSheaf j) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  (Scheme.Modules.restrictFunctorCongr
      (coordinateOverlapToRight_eq_specMap i j)).app
        (chartCoordinateKaehlerDifferentialSheaf j) ≪≫
    coordinateKaehlerRestrictRightSpecCanonicalIso i j

end MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialRestriction
