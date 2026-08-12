import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGlobal
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedImmersion
import FLT.Mathlib.AlgebraicGeometry.Modules.PushforwardUnit

/-!
# Geometric target of the N25 ambient Koszul resolution

The global ambient Koszul complex was constructed by descending the four
affine chart complexes.  Its terminal map initially lands in a categorical
cokernel.  This file begins the geometric identification of that cokernel
with the direct image of the structure sheaf of the projective complete
intersection.

The first essential normalization is `O(0) = O`: the degree-zero twisting
datum has identity transition functions, so its Čech equalizer is canonically
the ambient structure module.  We prove this on the actual global equalizer,
not by introducing a second abstract line bundle.  The resulting isomorphism
then supplies the natural morphism from the terminal Koszul term to the
direct image of the curve structure module.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGeometry

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoKoszulSheafTransition
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open RationalPointsN25QuotientTwoAmbientTwistingSheafGluing
open RationalPointsN25QuotientTwoAmbientKoszulGlobal
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The degree-zero transition datum -/

/-- Exponent zero makes every coordinate-ratio transition the identity. -/
theorem ratioPowerTransition_zero (i j : Fin 4) :
    Away.ratioPowerTransition standardConePiece
      (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 0 =
        LinearEquiv.refl _ _ := by
  apply LinearEquiv.ext
  intro x
  simp [Away.ratioPowerTransition]

/-- Consequently, the tilde transition of the zero ambient twist is the
identity on every ordered pair overlap. -/
theorem ambientOverlapTwistIso_zero (i j : Fin 4) :
    (ambientOverlapTwistIso 0 i j).hom = 𝟙 _ := by
  change (tilde.functor (AmbientOverlapRingCat i j)).map
      (Away.ratioPowerTransition standardConePiece
        (coordinate_isHomogeneous i)
        (coordinate_isHomogeneous j) 0).toModuleIso.hom = 𝟙 _
  rw [ratioPowerTransition_zero]
  exact tilde.map_id

/-! ## The canonical compatible family -/

/-- The ambient structure sheaf maps to the extension of the zero local
twist on chart `i` by restriction, followed by the inverse affine tilde
comparison. -/
def ambientUnitToLocalPushforwardZero (i : Fin 4) :
    SheafOfModules.unit BinaryProjectiveThreeSpace.ringCatSheaf ⟶
      ambientLocalPushforward 0 i :=
  Scheme.Modules.unitToPushforwardUnit (ambientChartMap i) ≫
    (Scheme.Modules.pushforward (ambientChartMap i)).map
      (ambientLocalTwistUnitIso 0 i).inv

/-- The four canonical restriction maps form a morphism into the Čech
source product. -/
def ambientUnitToTwistCechSourceZero :
    SheafOfModules.unit BinaryProjectiveThreeSpace.ringCatSheaf ⟶
      twistCechSource 0 :=
  Pi.lift ambientUnitToLocalPushforwardZero

/-- The two overlap arrows agree on the canonical structure-sheaf family.
The only geometric content is that the degree-zero transition is the
identity; the rest is functoriality of restriction through the two named
factorizations of each overlap map. -/
theorem ambientUnitToTwistCechSourceZero_compatible :
    ambientUnitToTwistCechSourceZero ≫ twistCechLeft 0 =
      ambientUnitToTwistCechSourceZero ≫ twistCechRight 0 := by
  apply Pi.hom_ext
  intro p
  simp only [twistCechLeft, twistCechRight]
  unfold ambientUnitToTwistCechSourceZero
  simp only [Category.assoc, Pi.lift_π]
  rw [Pi.lift_π_assoc, Pi.lift_π_assoc]
  have hzero :
      (ambientRestrictLeftIso 0 p.1 p.2 ≪≫
          ambientOverlapTwistIso 0 p.1 p.2).hom =
        (ambientRestrictLeftIso 0 p.1 p.2).hom := by
    simp only [Iso.trans_hom, ambientOverlapTwistIso_zero,
      Category.comp_id]
  unfold pushforwardRestrictionHom
  simp only [hzero]
  have hleft :
      (ambientRestrictLeftIso 0 p.1 p.2).hom =
        Scheme.Modules.unitRestrictionHom
          (ambientOverlapToLeft p.1 p.2)
          (ambientLocalTwistModule 0 p.1)
          (ambientOverlapTwistModule 0 p.1 p.2)
          (ambientLocalTwistUnitIso 0 p.1)
          (ambientOverlapTwistUnitIso 0 p.1 p.2) := by
    rfl
  have hright :
      (ambientRestrictRightIso 0 p.1 p.2).hom =
        Scheme.Modules.unitRestrictionHom
          (ambientOverlapToRight p.1 p.2)
          (ambientLocalTwistModule 0 p.2)
          (ambientOverlapTwistModule 0 p.1 p.2)
          (ambientLocalTwistUnitIso 0 p.2)
          (ambientOverlapTwistUnitIso 0 p.1 p.2) := by
    rfl
  rw [hleft, hright]
  change
    (SheafOfModules.unitToPushforwardObjUnit
          (ambientChartMap p.1).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (ambientChartMap p.1)).map
          (ambientLocalTwistUnitIso 0 p.1).inv) ≫ _ =
      (SheafOfModules.unitToPushforwardObjUnit
          (ambientChartMap p.2).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (ambientChartMap p.2)).map
          (ambientLocalTwistUnitIso 0 p.2).inv) ≫ _
  rw [Scheme.Modules.unitToPushforwardUnit_comp_pushforwardRestriction
    (ambientOverlapToLeft p.1 p.2) (ambientChartMap p.1)
      (ambientOverlapMap p.1 p.2) rfl
      (ambientLocalTwistModule 0 p.1)
      (ambientOverlapTwistModule 0 p.1 p.2)
      (ambientLocalTwistUnitIso 0 p.1)
      (ambientOverlapTwistUnitIso 0 p.1 p.2)]
  rw [Scheme.Modules.unitToPushforwardUnit_comp_pushforwardRestriction
    (ambientOverlapToRight p.1 p.2) (ambientChartMap p.2)
      (ambientOverlapMap p.1 p.2)
      (ambientOverlapMap_eq_right p.1 p.2)
      (ambientLocalTwistModule 0 p.2)
      (ambientOverlapTwistModule 0 p.1 p.2)
      (ambientLocalTwistUnitIso 0 p.2)
      (ambientOverlapTwistUnitIso 0 p.1 p.2)]

/-- The compatible structure-sheaf family glues to the descended zero
twist. -/
def ambientUnitToGlobalTwistZero :
    SheafOfModules.unit BinaryProjectiveThreeSpace.ringCatSheaf ⟶
      globalTwistModule 0 :=
  equalizer.lift ambientUnitToTwistCechSourceZero
    ambientUnitToTwistCechSourceZero_compatible

/-! ## Local normalization and global invertibility -/

/-- On every standard coordinate chart, the glued zero-twist comparison is
the canonical restriction isomorphism after applying the local unit
trivialization.  Thus this statement records the mathematical normalization,
not merely local invertibility. -/
theorem ambientUnitToGlobalTwistZero_restrict (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
        ambientUnitToGlobalTwistZero ≫
      (globalTwistModuleLocalUnitIso 0 i).hom =
        (Scheme.Modules.restrictUnitIso (ambientChartMap i)).hom := by
  change (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
        ambientUnitToGlobalTwistZero ≫
      globalTwistModuleToLocal 0 i ≫
        (ambientLocalTwistUnitIso 0 i).hom = _
  rw [globalTwistModuleToLocal_eq]
  unfold ambientUnitToGlobalTwistZero
  simp only [← Category.assoc]
  rw [← Functor.map_comp]
  rw [equalizer.lift_ι_assoc]
  unfold ambientUnitToTwistCechSourceZero
  rw [Pi.lift_π]
  unfold ambientUnitToLocalPushforwardZero
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have htail :
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ((Scheme.Modules.pushforward (ambientChartMap i)).map
            (ambientLocalTwistUnitIso 0 i).inv) ≫
        (Scheme.Modules.restrictAdjunction
          (ambientChartMap i)).counit.app
            (ambientLocalTwistModule 0 i) ≫
        (ambientLocalTwistUnitIso 0 i).hom =
      (Scheme.Modules.restrictAdjunction
        (ambientChartMap i)).counit.app
          (SheafOfModules.unit
            (ambientCoordinateChartScheme i).ringCatSheaf) := by
    calc
      _ = (Scheme.Modules.restrictAdjunction
            (ambientChartMap i)).counit.app
              (SheafOfModules.unit
                (ambientCoordinateChartScheme i).ringCatSheaf) ≫
            (ambientLocalTwistUnitIso 0 i).inv ≫
            (ambientLocalTwistUnitIso 0 i).hom := by
          simpa only [Functor.comp_map, Functor.id_map] using
            (Scheme.Modules.restrictAdjunction
              (ambientChartMap i)).counit.naturality_assoc
                (ambientLocalTwistUnitIso 0 i).inv
                (ambientLocalTwistUnitIso 0 i).hom
      _ = _ := by simp
  rw [htail]
  exact Scheme.Modules.restrict_unitToPushforwardUnit_comp_counit
    (ambientChartMap i)

set_option synthInstance.maxHeartbeats 200000 in
-- Comparing stalks across the four-chart cover creates a large typeclass term.
/-- The descended zero twist is the ambient structure module.  The proof is
local on stalks: every projective point lies in a standard coordinate chart,
the preceding normalization makes the restricted comparison an isomorphism,
and `restrictStalkNatIso` transports that fact back to the ambient stalk. -/
theorem ambientUnitToGlobalTwistZero_isIso :
    IsIso ambientUnitToGlobalTwistZero := by
  let F := SheafOfModules.toSheaf
    BinaryProjectiveThreeSpace.ringCatSheaf
  have hStalk (x : BinaryProjectiveThreeSpace) :
      IsIso
        ((Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ambientUnitToGlobalTwistZero) := by
    let i := ambientCoordinateAffineOpenCover.idx x
    have hx := ambientCoordinateAffineOpenCover.covers x
    change x ∈ Set.range (ambientChartMap i) at hx
    obtain ⟨y, hy⟩ := hx
    haveI hRestrictedComposite : IsIso
        ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
            ambientUnitToGlobalTwistZero ≫
          (globalTwistModuleLocalUnitIso 0 i).hom) := by
      rw [ambientUnitToGlobalTwistZero_restrict]
      infer_instance
    letI hRestricted : IsIso
        ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientUnitToGlobalTwistZero) :=
      IsIso.of_isIso_comp_right
        ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientUnitToGlobalTwistZero)
        (globalTwistModuleLocalUnitIso 0 i).hom
    let G := Scheme.Modules.toPresheaf (ambientChartScheme i) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat y
    have hRestrictedStalk : IsIso
        ((Scheme.Modules.restrictFunctor (ambientChartMap i) ⋙ G).map
          ambientUnitToGlobalTwistZero) := by
      change IsIso (G.map
        ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientUnitToGlobalTwistZero))
      infer_instance
    have hAmbientStalk : IsIso
        ((Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y)).map ambientUnitToGlobalTwistZero) :=
      (CategoryTheory.NatIso.isIso_map_iff
        (Scheme.Modules.restrictStalkNatIso (ambientChartMap i) y)
          ambientUnitToGlobalTwistZero).mp hRestrictedStalk
    exact hy ▸ hAmbientStalk
  have hUnderlyingStalk (x : BinaryProjectiveThreeSpace) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (F.map ambientUnitToGlobalTwistZero).hom) := by
    change IsIso
      ((Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ambientUnitToGlobalTwistZero)
    exact hStalk x
  letI : ∀ x : BinaryProjectiveThreeSpace,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (F.map ambientUnitToGlobalTwistZero).hom) := hUnderlyingStalk
  haveI hUnderlying : IsIso (F.map ambientUnitToGlobalTwistZero) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      (F.map ambientUnitToGlobalTwistZero)
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso
    ((F.map ambientUnitToGlobalTwistZero).hom.app (.op U))
  infer_instance

/-- The preferred orientation identifies the descended degree-zero twist
with the ambient structure module. -/
def ambientGlobalTwistZeroIsoUnit :
    globalTwistModule 0 ≅
      SheafOfModules.unit BinaryProjectiveThreeSpace.ringCatSheaf := by
  letI := ambientUnitToGlobalTwistZero_isIso
  exact (asIso ambientUnitToGlobalTwistZero).symm

/-! ## The geometric terminal morphism -/

/-- The degree-zero terminal Koszul term maps to the direct image of the
curve structure module by first identifying `O(0)` with the ambient
structure module and then applying the structure morphism of the closed
immersion. -/
def ambientKoszulZeroToCurve :
    globalTwistModule 0 ⟶
      (Scheme.Modules.pushforward canonicalProjectiveCurveMap).obj
        (SheafOfModules.unit CanonicalProjectiveCurve25Two.ringCatSheaf) :=
  ambientGlobalTwistZeroIsoUnit.hom ≫
    Scheme.Modules.unitToPushforwardUnit canonicalProjectiveCurveMap

/-- The geometric terminal morphism is an epimorphism: its first factor is
an isomorphism and its second factor is locally surjective because the curve
map is a closed immersion. -/
instance ambientKoszulZeroToCurve_epi : Epi ambientKoszulZeroToCurve := by
  letI : Epi
      (Scheme.Modules.unitToPushforwardUnit
        canonicalProjectiveCurveMap) :=
    Scheme.Modules.unitToPushforwardUnit_epi
      canonicalProjectiveCurveMap
  unfold ambientKoszulZeroToCurve
  infer_instance

end MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGeometry
