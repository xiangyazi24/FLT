import FLT.Assumptions.MazurProof.N13ClosedFiberCharts
import FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility
import Mathlib.RingTheory.Localization.Algebra

/-!
# Closed fibres of the N13 chart overlaps

The reductions on the two distinguished principal opens are the
localizations of the chart reductions.  Consequently they remain
surjective, and localization carries their kernels to the extension of
the vertical ideal.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberOverlaps

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev R₂ :=
  N13GeneralizedMumfordReduction.R₂

private abbrev OrdinaryAffine :=
  N13OrdinaryCurveOverlap.AffineCurve

private abbrev SpecialAffine :=
  N13SpecialCurveOverlap.AffineCurve

private abbrev OrdinaryAffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap

private abbrev SpecialAffineOverlap :=
  N13SpecialCurveOverlap.AffineOverlap

private abbrev OrdinaryInfinity :=
  N13OrdinaryCurveOverlap.InfinityCurve

private abbrev SpecialInfinity :=
  N13SpecialCurveOverlap.CoordinateRing

private abbrev OrdinaryInfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap

private abbrev SpecialInfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap

private theorem reduce_affine_x :
    N13GeneralizedMumfordReduction.reduceCoordinate
        N13OrdinaryCurveOverlap.xClass =
      N13SpecialCurveOverlap.xClass := by
  simp [N13OrdinaryCurveOverlap.xClass,
    N13SpecialCurveOverlap.xClass,
    N13GeneralizedMumfordReduction.reducePoly]

private theorem reduce_infinity_t :
    N13IntegralInfinityReduction.reduceCoordinate
        N13IntegralInfinityChart.tClass =
      N13SpecialInfinityChart.tClass := by
  exact N13IntegralInfinityReduction.reduce_tClass

private theorem affine_powers_map :
    Submonoid.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (Submonoid.powers N13OrdinaryCurveOverlap.xClass) =
      Submonoid.powers N13SpecialCurveOverlap.xClass := by
  rw [Submonoid.map_powers, reduce_affine_x]

private theorem infinity_powers_map :
    Submonoid.map
        N13IntegralInfinityReduction.reduceCoordinate
        (Submonoid.powers N13IntegralInfinityChart.tClass) =
      Submonoid.powers N13SpecialInfinityChart.tClass := by
  rw [Submonoid.map_powers, reduce_infinity_t]

/-- The canonical localization of the affine chart reduction. -/
def affineLocalizationMap :
    OrdinaryAffineOverlap →+* SpecialAffineOverlap := by
  letI :
      IsLocalization
        (Submonoid.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (Submonoid.powers N13OrdinaryCurveOverlap.xClass))
        SpecialAffineOverlap := by
    rw [affine_powers_map]
    infer_instance
  exact
    IsLocalization.map
      SpecialAffineOverlap
      N13GeneralizedMumfordReduction.reduceCoordinate
      (Submonoid.powers
        N13OrdinaryCurveOverlap.xClass).le_comap_map

/-- The exported affine-overlap reduction is the canonical localization
of the affine chart reduction. -/
theorem affineLocalizationMap_eq :
    affineLocalizationMap =
      N13OverlapReductionCompatibility.reduceAffineOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13OrdinaryCurveOverlap.xClass)
  apply RingHom.ext
  intro z
  change
    affineLocalizationMap
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap z) =
      N13OverlapReductionCompatibility.reduceAffineOverlap
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap z)
  rw [N13OverlapReductionCompatibility.reduceAffineOverlap_algebraMap]
  change
    affineLocalizationMap
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap z) =
      algebraMap SpecialAffine SpecialAffineOverlap
        (N13GeneralizedMumfordReduction.reduceCoordinate z)
  simp [affineLocalizationMap, IsLocalization.map_eq]

private theorem affineLocalizationMap_surjective :
    Function.Surjective affineLocalizationMap := by
  letI :
      IsLocalization
        (Submonoid.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (Submonoid.powers N13OrdinaryCurveOverlap.xClass))
        SpecialAffineOverlap := by
    rw [affine_powers_map]
    infer_instance
  change Function.Surjective
    (IsLocalization.map
      SpecialAffineOverlap
      N13GeneralizedMumfordReduction.reduceCoordinate
      (Submonoid.powers
        N13OrdinaryCurveOverlap.xClass).le_comap_map)
  exact
    IsLocalization.map_surjective_of_surjective
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
      OrdinaryAffineOverlap
      SpecialAffineOverlap
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective

private theorem affineLocalizationMap_ker :
    RingHom.ker affineLocalizationMap =
      (RingHom.ker
        N13GeneralizedMumfordReduction.reduceCoordinate).map
          (algebraMap OrdinaryAffine OrdinaryAffineOverlap) := by
  letI :
      IsLocalization
        (Submonoid.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (Submonoid.powers N13OrdinaryCurveOverlap.xClass))
        SpecialAffineOverlap := by
    rw [affine_powers_map]
    infer_instance
  change
    RingHom.ker
        (IsLocalization.map
          SpecialAffineOverlap
          N13GeneralizedMumfordReduction.reduceCoordinate
          (Submonoid.powers
            N13OrdinaryCurveOverlap.xClass).le_comap_map) =
      (RingHom.ker
        N13GeneralizedMumfordReduction.reduceCoordinate).map
          (algebraMap OrdinaryAffine OrdinaryAffineOverlap)
  exact
    IsLocalization.ker_map
      SpecialAffineOverlap
      N13GeneralizedMumfordReduction.reduceCoordinate
      rfl

/-- Reduction on the affine overlap remains surjective. -/
theorem reduceAffineOverlap_surjective :
    Function.Surjective
      N13OverlapReductionCompatibility.reduceAffineOverlap := by
  rw [← affineLocalizationMap_eq]
  exact affineLocalizationMap_surjective

/-- The kernel on the affine overlap is the extension of the vertical
ideal. -/
theorem ker_reduceAffineOverlap :
    RingHom.ker
        N13OverlapReductionCompatibility.reduceAffineOverlap =
      N13ClosedFiberCharts.verticalIdeal.map
        (algebraMap R₂ OrdinaryAffineOverlap) := by
  rw [← affineLocalizationMap_eq, affineLocalizationMap_ker,
    N13GeneralizedMumfordReduction.ker_reduceCoordinate]
  simp only [N13ClosedFiberCharts.verticalIdeal, Ideal.map_span,
    Set.image_singleton,
    IsScalarTower.algebraMap_apply R₂ OrdinaryAffine
      OrdinaryAffineOverlap]

/-- The canonical localization of the infinity chart reduction. -/
def infinityLocalizationMap :
    OrdinaryInfinityOverlap →+* SpecialInfinityOverlap := by
  letI :
      IsLocalization
        (Submonoid.map
          N13IntegralInfinityReduction.reduceCoordinate
          (Submonoid.powers N13IntegralInfinityChart.tClass))
        SpecialInfinityOverlap := by
    rw [infinity_powers_map]
    infer_instance
  exact
    IsLocalization.map
      SpecialInfinityOverlap
      N13IntegralInfinityReduction.reduceCoordinate
      (Submonoid.powers
        N13IntegralInfinityChart.tClass).le_comap_map

/-- The exported infinity-overlap reduction is the canonical localization
of the infinity chart reduction. -/
theorem infinityLocalizationMap_eq :
    infinityLocalizationMap =
      N13OverlapReductionCompatibility.reduceInfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13IntegralInfinityChart.tClass)
  apply RingHom.ext
  intro z
  change
    infinityLocalizationMap
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap z) =
      N13OverlapReductionCompatibility.reduceInfinityOverlap
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap z)
  rw [N13OverlapReductionCompatibility.reduceInfinityOverlap_algebraMap]
  change
    infinityLocalizationMap
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap z) =
      algebraMap SpecialInfinity SpecialInfinityOverlap
        (N13IntegralInfinityReduction.reduceCoordinate z)
  simp [infinityLocalizationMap, IsLocalization.map_eq]

private theorem infinityLocalizationMap_surjective :
    Function.Surjective infinityLocalizationMap := by
  letI :
      IsLocalization
        (Submonoid.map
          N13IntegralInfinityReduction.reduceCoordinate
          (Submonoid.powers N13IntegralInfinityChart.tClass))
        SpecialInfinityOverlap := by
    rw [infinity_powers_map]
    infer_instance
  change Function.Surjective
    (IsLocalization.map
      SpecialInfinityOverlap
      N13IntegralInfinityReduction.reduceCoordinate
      (Submonoid.powers
        N13IntegralInfinityChart.tClass).le_comap_map)
  exact
    IsLocalization.map_surjective_of_surjective
      (Submonoid.powers N13IntegralInfinityChart.tClass)
      OrdinaryInfinityOverlap
      SpecialInfinityOverlap
      N13IntegralInfinityReduction.reduceCoordinate_surjective

private theorem infinityLocalizationMap_ker :
    RingHom.ker infinityLocalizationMap =
      (RingHom.ker
        N13IntegralInfinityReduction.reduceCoordinate).map
          (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap) := by
  letI :
      IsLocalization
        (Submonoid.map
          N13IntegralInfinityReduction.reduceCoordinate
          (Submonoid.powers N13IntegralInfinityChart.tClass))
        SpecialInfinityOverlap := by
    rw [infinity_powers_map]
    infer_instance
  change
    RingHom.ker
        (IsLocalization.map
          SpecialInfinityOverlap
          N13IntegralInfinityReduction.reduceCoordinate
          (Submonoid.powers
            N13IntegralInfinityChart.tClass).le_comap_map) =
      (RingHom.ker
        N13IntegralInfinityReduction.reduceCoordinate).map
          (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)
  exact
    IsLocalization.ker_map
      SpecialInfinityOverlap
      N13IntegralInfinityReduction.reduceCoordinate
      rfl

/-- Reduction on the infinity overlap remains surjective. -/
theorem reduceInfinityOverlap_surjective :
    Function.Surjective
      N13OverlapReductionCompatibility.reduceInfinityOverlap := by
  rw [← infinityLocalizationMap_eq]
  exact infinityLocalizationMap_surjective

/-- The kernel on the infinity overlap is the extension of the vertical
ideal. -/
theorem ker_reduceInfinityOverlap :
    RingHom.ker
        N13OverlapReductionCompatibility.reduceInfinityOverlap =
      N13ClosedFiberCharts.verticalIdeal.map
        (algebraMap R₂ OrdinaryInfinityOverlap) := by
  rw [← infinityLocalizationMap_eq, infinityLocalizationMap_ker,
    N13IntegralInfinityReduction.ker_reduceCoordinate]
  simp only [N13ClosedFiberCharts.verticalIdeal, Ideal.map_span,
    Set.image_singleton,
    IsScalarTower.algebraMap_apply R₂ OrdinaryInfinity
      OrdinaryInfinityOverlap]

/-- The affine-overlap structure morphism to the two-adic base. -/
def affineOverlapToBase :
    Spec (.of OrdinaryAffineOverlap) ⟶ Spec (.of R₂) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap R₂ OrdinaryAffineOverlap))

/-- The infinity-overlap structure morphism to the two-adic base. -/
def infinityOverlapToBase :
    Spec (.of OrdinaryInfinityOverlap) ⟶ Spec (.of R₂) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap R₂ OrdinaryInfinityOverlap))

/-- The special affine overlap is the closed fibre of the ordinary
affine overlap. -/
def affineOverlapClosedFiberIso :
    pullback
        affineOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ≅
      Spec (.of SpecialAffineOverlap) :=
  ClosedFiberAffineCore.specPullbackIsoOfReduction
    N13ClosedFiberCharts.verticalIdeal
    N13OverlapReductionCompatibility.reduceAffineOverlap
    reduceAffineOverlap_surjective
    ker_reduceAffineOverlap

/-- The special infinity overlap is the closed fibre of the ordinary
infinity overlap. -/
def infinityOverlapClosedFiberIso :
    pullback
        infinityOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ≅
      Spec (.of SpecialInfinityOverlap) :=
  ClosedFiberAffineCore.specPullbackIsoOfReduction
    N13ClosedFiberCharts.verticalIdeal
    N13OverlapReductionCompatibility.reduceInfinityOverlap
    reduceInfinityOverlap_surjective
    ker_reduceInfinityOverlap

end MazurProof.N13ClosedFiberOverlaps
