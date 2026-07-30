import FLT.Assumptions.MazurProof.N13ClosedFiberGlueOverlaps

/-!
# Compatibility of the N13 closed-fibre gluing maps

The chart and overlap closed-fibre isomorphisms commute with the two
principal-open restriction maps.  This is the local naturality needed
to identify the pullback gluing datum with the explicit special-fibre
gluing datum.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberGlueComparison

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev D :=
  N13IntegralCurveScheme.glueData

private abbrev P :=
  Scheme.Pullback.gluing
    D.openCover
    N13IntegralCurveScheme.toBase
    N13ClosedFiberCharts.closedBaseMap

private abbrev S :=
  N13SpecialFibreScheme.glueData

private abbrev R₂ :=
  N13OrdinaryCurveOverlap.R₂

private abbrev OrdinaryAffine :=
  N13OrdinaryCurveOverlap.AffineCurve

private abbrev OrdinaryAffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap

private abbrev SpecialAffine :=
  N13SpecialCurveOverlap.AffineCurve

private abbrev SpecialAffineOverlap :=
  N13SpecialCurveOverlap.AffineOverlap

private abbrev OrdinaryInfinity :=
  N13OrdinaryCurveOverlap.InfinityCurve

private abbrev OrdinaryInfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap

private abbrev SpecialInfinity :=
  N13SpecialCurveOverlap.CoordinateRing

private abbrev SpecialInfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap

/-- Rewrite the affine pullback chart using the chartwise structure map. -/
def affineChartBaseChangeTransportIso :
    pullback
        (D.ι false ≫ N13IntegralCurveScheme.toBase)
        N13ClosedFiberCharts.closedBaseMap ≅
      pullback
        (N13IntegralCurveScheme.chartToBase false)
        N13ClosedFiberCharts.closedBaseMap :=
  pullback.congrHom
    (N13IntegralCurveScheme.ι_toBase false)
    rfl

/-- Rewrite the infinity pullback chart using the chartwise structure map. -/
def infinityChartBaseChangeTransportIso :
    pullback
        (D.ι true ≫ N13IntegralCurveScheme.toBase)
        N13ClosedFiberCharts.closedBaseMap ≅
      pullback
        (N13IntegralCurveScheme.chartToBase true)
        N13ClosedFiberCharts.closedBaseMap :=
  pullback.congrHom
    (N13IntegralCurveScheme.ι_toBase true)
    rfl

/-- The affine chart of the pullback gluing is the explicit special
affine chart. -/
def affinePullbackChartIso :
    P.U false ≅ S.U false :=
  affineChartBaseChangeTransportIso ≪≫
    N13ClosedFiberCharts.affineClosedFiberIso

/-- The infinity chart of the pullback gluing is the explicit special
infinity chart. -/
def infinityPullbackChartIso :
    P.U true ≅ S.U true :=
  infinityChartBaseChangeTransportIso ≪≫
    N13ClosedFiberCharts.infinityClosedFiberIso

/-- The `false,true` overlap of the pullback gluing is the explicit
special affine overlap. -/
def affinePullbackOverlapIso :
    P.V (false, true) ≅ S.V (false, true) :=
  N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.symm ≪≫
    N13ClosedFiberOverlaps.affineOverlapClosedFiberIso ≪≫
      N13SpecialFibreScheme.affineOverlapToGlueDataIso

/-- The `true,false` overlap of the pullback gluing is the explicit
special infinity overlap. -/
def infinityPullbackOverlapIso :
    P.V (true, false) ≅ S.V (true, false) :=
  N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.symm ≪≫
    N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso ≪≫
      N13SpecialFibreScheme.infinityOverlapToGlueDataIso

/-- Base change of the affine principal-open inclusion. -/
def affineRestrictionBaseChange :
    pullback
        N13ClosedFiberOverlaps.affineOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ⟶
      pullback
        (N13IntegralCurveScheme.chartToBase false)
        N13ClosedFiberCharts.closedBaseMap :=
  pullback.map
    N13ClosedFiberOverlaps.affineOverlapToBase
    N13ClosedFiberCharts.closedBaseMap
    (N13IntegralCurveScheme.chartToBase false)
    N13ClosedFiberCharts.closedBaseMap
    (Spec.map
      (CommRingCat.ofHom
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap)))
    (𝟙 _)
    (𝟙 _)
    (by
      change
        Spec.map
            (CommRingCat.ofHom
              (algebraMap R₂ OrdinaryAffineOverlap)) =
          Spec.map
                (CommRingCat.ofHom
                  (algebraMap OrdinaryAffine OrdinaryAffineOverlap)) ≫
            Spec.map
              (CommRingCat.ofHom
                N13IntegralCurveScheme.affineBaseMap)
      rw [show
        N13IntegralCurveScheme.affineBaseMap =
          algebraMap R₂ OrdinaryAffine by rfl]
      rw [← Spec.map_comp]
      congr 1)
    (by simp)

@[reassoc]
theorem affineRestrictionBaseChange_fst :
    affineRestrictionBaseChange ≫
        pullback.fst
          (N13IntegralCurveScheme.chartToBase false)
          N13ClosedFiberCharts.closedBaseMap =
      pullback.fst
            N13ClosedFiberOverlaps.affineOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryAffine OrdinaryAffineOverlap)) := by
  unfold affineRestrictionBaseChange
  exact pullback.lift_fst _ _ _

/-- Base change of the infinity principal-open inclusion. -/
def infinityRestrictionBaseChange :
    pullback
        N13ClosedFiberOverlaps.infinityOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ⟶
      pullback
        (N13IntegralCurveScheme.chartToBase true)
        N13ClosedFiberCharts.closedBaseMap :=
  pullback.map
    N13ClosedFiberOverlaps.infinityOverlapToBase
    N13ClosedFiberCharts.closedBaseMap
    (N13IntegralCurveScheme.chartToBase true)
    N13ClosedFiberCharts.closedBaseMap
    (Spec.map
      (CommRingCat.ofHom
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)))
    (𝟙 _)
    (𝟙 _)
    (by
      change
        Spec.map
            (CommRingCat.ofHom
              (algebraMap R₂ OrdinaryInfinityOverlap)) =
          Spec.map
                (CommRingCat.ofHom
                  (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)) ≫
            Spec.map
              (CommRingCat.ofHom
                N13IntegralCurveScheme.infinityBaseMap)
      rw [show
        N13IntegralCurveScheme.infinityBaseMap =
          algebraMap R₂ OrdinaryInfinity by rfl]
      rw [← Spec.map_comp]
      congr 1)
    (by simp)

@[reassoc]
theorem infinityRestrictionBaseChange_fst :
    infinityRestrictionBaseChange ≫
        pullback.fst
          (N13IntegralCurveScheme.chartToBase true)
          N13ClosedFiberCharts.closedBaseMap =
      pullback.fst
            N13ClosedFiberOverlaps.infinityOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)) := by
  unfold infinityRestrictionBaseChange
  exact pullback.lift_fst _ _ _

private theorem affineRestriction_reduce :
    Spec.map
          (CommRingCat.ofHom
            (algebraMap SpecialAffine SpecialAffineOverlap)) ≫
        Spec.map
          (CommRingCat.ofHom
            N13GeneralizedMumfordReduction.reduceCoordinate) =
      Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceAffineOverlap) ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryAffine OrdinaryAffineOverlap)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact
    congrArg CommRingCat.ofHom
      N13OverlapReductionCompatibility.reduceAffineOverlap_comp_algebraMap.symm

private theorem infinityRestriction_reduce :
    Spec.map
          (CommRingCat.ofHom
            (algebraMap SpecialInfinity SpecialInfinityOverlap)) ≫
        Spec.map
          (CommRingCat.ofHom
            N13IntegralInfinityReduction.reduceCoordinate) =
      Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceInfinityOverlap) ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact
    congrArg CommRingCat.ofHom
      N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap.symm

/-- The affine overlap and chart closed-fibre isomorphisms commute with
restriction. -/
theorem affineClosedFiberRestriction_comm :
    N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap SpecialAffine SpecialAffineOverlap)) =
      affineRestrictionBaseChange ≫
        N13ClosedFiberCharts.affineClosedFiberIso.hom := by
  letI :
      IsClosedImmersion
        (Spec.map
          (CommRingCat.ofHom
            N13GeneralizedMumfordReduction.reduceCoordinate)) :=
    IsClosedImmersion.spec_of_surjective _
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
  apply (cancel_mono
    (Spec.map
      (CommRingCat.ofHom
        N13GeneralizedMumfordReduction.reduceCoordinate))).mp
  calc
    (N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap SpecialAffine SpecialAffineOverlap))) ≫
        Spec.map
          (CommRingCat.ofHom
            N13GeneralizedMumfordReduction.reduceCoordinate) =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        (Spec.map
              (CommRingCat.ofHom
                (algebraMap SpecialAffine SpecialAffineOverlap)) ≫
          Spec.map
            (CommRingCat.ofHom
              N13GeneralizedMumfordReduction.reduceCoordinate)) :=
        Category.assoc _ _ _
    _ =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        (Spec.map
              (CommRingCat.ofHom
                N13OverlapReductionCompatibility.reduceAffineOverlap) ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap OrdinaryAffine OrdinaryAffineOverlap))) :=
        congrArg
          (fun k =>
            N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫ k)
          affineRestriction_reduce
    _ =
      (N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
          Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceAffineOverlap)) ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryAffine OrdinaryAffineOverlap)) :=
        (Category.assoc _ _ _).symm
    _ =
      pullback.fst
            N13ClosedFiberOverlaps.affineOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryAffine OrdinaryAffineOverlap)) :=
        congrArg
          (fun k =>
            k ≫ Spec.map
              (CommRingCat.ofHom
                (algebraMap OrdinaryAffine OrdinaryAffineOverlap)))
          N13ClosedFiberOverlaps.affineOverlapClosedFiberIso_hom_reduceAffineOverlap
    _ =
      (affineRestrictionBaseChange ≫
          N13ClosedFiberCharts.affineClosedFiberIso.hom) ≫
        Spec.map
          (CommRingCat.ofHom
            N13GeneralizedMumfordReduction.reduceCoordinate) :=
        affineRestrictionBaseChange_fst.symm.trans
          (N13ClosedFiberCharts.comp_affineClosedFiberIso_hom_reduceCoordinate
            affineRestrictionBaseChange).symm

/-- The infinity overlap and chart closed-fibre isomorphisms commute
with restriction. -/
theorem infinityClosedFiberRestriction_comm :
    N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap SpecialInfinity SpecialInfinityOverlap)) =
      infinityRestrictionBaseChange ≫
        N13ClosedFiberCharts.infinityClosedFiberIso.hom := by
  letI :
      IsClosedImmersion
        (Spec.map
          (CommRingCat.ofHom
            N13IntegralInfinityReduction.reduceCoordinate)) :=
    IsClosedImmersion.spec_of_surjective _
      N13IntegralInfinityReduction.reduceCoordinate_surjective
  apply (cancel_mono
    (Spec.map
      (CommRingCat.ofHom
        N13IntegralInfinityReduction.reduceCoordinate))).mp
  calc
    (N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap SpecialInfinity SpecialInfinityOverlap))) ≫
        Spec.map
          (CommRingCat.ofHom
            N13IntegralInfinityReduction.reduceCoordinate) =
      N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
        (Spec.map
              (CommRingCat.ofHom
                (algebraMap SpecialInfinity SpecialInfinityOverlap)) ≫
          Spec.map
            (CommRingCat.ofHom
              N13IntegralInfinityReduction.reduceCoordinate)) :=
        Category.assoc _ _ _
    _ =
      N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
        (Spec.map
              (CommRingCat.ofHom
                N13OverlapReductionCompatibility.reduceInfinityOverlap) ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap))) :=
        congrArg
          (fun k =>
            N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫ k)
          infinityRestriction_reduce
    _ =
      (N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
          Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceInfinityOverlap)) ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)) :=
        (Category.assoc _ _ _).symm
    _ =
      pullback.fst
            N13ClosedFiberOverlaps.infinityOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)) :=
        congrArg
          (fun k =>
            k ≫ Spec.map
              (CommRingCat.ofHom
                (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap)))
          N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso_hom_reduceInfinityOverlap
    _ =
      (infinityRestrictionBaseChange ≫
          N13ClosedFiberCharts.infinityClosedFiberIso.hom) ≫
        Spec.map
          (CommRingCat.ofHom
            N13IntegralInfinityReduction.reduceCoordinate) :=
        infinityRestrictionBaseChange_fst.symm.trans
          (N13ClosedFiberCharts.comp_infinityClosedFiberIso_hom_reduceCoordinate
            infinityRestrictionBaseChange).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem affinePullbackGluingRestriction :
    N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
          pullback.fst
              (pullback.fst
                    (D.ι false ≫ N13IntegralCurveScheme.toBase)
                    N13ClosedFiberCharts.closedBaseMap ≫
                D.ι false)
              (D.ι true) ≫
        affineChartBaseChangeTransportIso.hom =
      affineRestrictionBaseChange := by
  rw [N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso,
    Iso.trans_hom, Category.assoc,
    GlueDataClosedBaseChange.overlapBaseChangeIso_hom_fst_assoc]
  apply pullback.hom_ext
  · simp [N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso,
      N13ClosedFiberGlueOverlaps.affineOverlapIso,
      N13IntegralCurveScheme.overlapInclusion,
      GlueDataClosedBaseChange.overlapToChartBaseChange,
      affineChartBaseChangeTransportIso,
      affineRestrictionBaseChange, Category.assoc]
  · simp [N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso,
      GlueDataClosedBaseChange.overlapToChartBaseChange,
      affineChartBaseChangeTransportIso,
      affineRestrictionBaseChange, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem infinityPullbackGluingRestriction :
    N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom ≫
          pullback.fst
              (pullback.fst
                    (D.ι true ≫ N13IntegralCurveScheme.toBase)
                    N13ClosedFiberCharts.closedBaseMap ≫
                D.ι true)
              (D.ι false) ≫
        infinityChartBaseChangeTransportIso.hom =
      infinityRestrictionBaseChange := by
  rw [N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso,
    Iso.trans_hom, Category.assoc,
    GlueDataClosedBaseChange.overlapBaseChangeIso_hom_fst_assoc]
  apply pullback.hom_ext
  · simp [N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso,
      N13ClosedFiberGlueOverlaps.infinityOverlapIso,
      N13IntegralCurveScheme.overlapInclusion,
      GlueDataClosedBaseChange.overlapToChartBaseChange,
      infinityChartBaseChangeTransportIso,
      infinityRestrictionBaseChange, Category.assoc]
  · simp [N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso,
      GlueDataClosedBaseChange.overlapToChartBaseChange,
      infinityChartBaseChangeTransportIso,
      infinityRestrictionBaseChange, Category.assoc]

/-- Naturality of the `false,true` overlap inclusion. -/
theorem affinePullback_f :
    P.f false true ≫ affinePullbackChartIso.hom =
      affinePullbackOverlapIso.hom ≫ S.f false true := by
  have hRight :
      N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
            (affinePullbackOverlapIso.hom ≫ S.f false true) =
        N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
          N13SpecialFibreScheme.overlapInclusion
            false true (by decide) := by
    calc
      N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
            (affinePullbackOverlapIso.hom ≫ S.f false true) =
          N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
              N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.inv ≫
            (N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
              (N13SpecialFibreScheme.affineOverlapToGlueDataIso.hom ≫
                N13SpecialFibreScheme.glueData.f false true)) := by
        rfl
      _ =
          N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
            (N13SpecialFibreScheme.affineOverlapToGlueDataIso.hom ≫
              N13SpecialFibreScheme.glueData.f false true) := by
        exact Iso.hom_inv_id_assoc _ _
      _ =
          N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
            N13SpecialFibreScheme.overlapInclusion
              false true (by decide) := by
        exact congrArg
          (fun k =>
            N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫ k)
          N13SpecialFibreScheme.affineOverlapToGlueDataIso_hom_f
  apply (cancel_epi
    N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom).mp
  exact
    (affinePullbackGluingRestriction_assoc
        N13ClosedFiberCharts.affineClosedFiberIso.hom).trans
      (affineClosedFiberRestriction_comm.symm.trans hRight.symm)

/-- Naturality of the `true,false` overlap inclusion. -/
theorem infinityPullback_f :
    P.f true false ≫ infinityPullbackChartIso.hom =
      infinityPullbackOverlapIso.hom ≫ S.f true false := by
  have hRight :
      N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom ≫
            (infinityPullbackOverlapIso.hom ≫ S.f true false) =
        N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
          N13SpecialFibreScheme.overlapInclusion
            true false (by decide) := by
    calc
      N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom ≫
            (infinityPullbackOverlapIso.hom ≫ S.f true false) =
          N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom ≫
              N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.inv ≫
            (N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
              (N13SpecialFibreScheme.infinityOverlapToGlueDataIso.hom ≫
                N13SpecialFibreScheme.glueData.f true false)) := by
        rfl
      _ =
          N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
            (N13SpecialFibreScheme.infinityOverlapToGlueDataIso.hom ≫
              N13SpecialFibreScheme.glueData.f true false) := by
        exact Iso.hom_inv_id_assoc _ _
      _ =
          N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
            N13SpecialFibreScheme.overlapInclusion
              true false (by decide) := by
        exact congrArg
          (fun k =>
            N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫ k)
          N13SpecialFibreScheme.infinityOverlapToGlueDataIso_hom_f
  apply (cancel_epi
    N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom).mp
  exact
    (infinityPullbackGluingRestriction_assoc
        N13ClosedFiberCharts.infinityClosedFiberIso.hom).trans
      (infinityClosedFiberRestriction_comm.symm.trans hRight.symm)

end MazurProof.N13ClosedFiberGlueComparison
