import FLT.Assumptions.MazurProof.GlueDataClosedBaseChange
import FLT.Assumptions.MazurProof.N13ClosedFiberOverlaps

/-!
# Off-diagonal overlap adapters for the N13 glue data

The full glue data produced by `GlueData.ofGlueData'` stores its overlap
objects behind a dependent diagonal/off-diagonal conditional.  These
lemmas expose the two concrete off-diagonal objects without treating
them as definitional equalities.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberGlueOverlaps

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev D :=
  N13IntegralCurveScheme.glueData

/-- The `false,true` object of the full glue data is the ordinary affine
principal-open overlap. -/
theorem affineOverlap_eq :
    D.V (false, true) =
      Spec (.of N13OrdinaryCurveOverlap.AffineOverlap) := by
  simp [D, N13IntegralCurveScheme.glueData,
    CategoryTheory.GlueData.ofGlueData',
    N13IntegralCurveScheme.glueData',
    N13IntegralCurveScheme.overlap]

/-- The `true,false` object of the full glue data is the ordinary
infinity principal-open overlap. -/
theorem infinityOverlap_eq :
    D.V (true, false) =
      Spec (.of N13OrdinaryCurveOverlap.InfinityOverlap) := by
  simp [D, N13IntegralCurveScheme.glueData,
    CategoryTheory.GlueData.ofGlueData',
    N13IntegralCurveScheme.glueData',
    N13IntegralCurveScheme.overlap]

/-- The explicit affine overlap, oriented toward the corresponding
object of the full glue data. -/
def affineOverlapIso :
    Spec (.of N13OrdinaryCurveOverlap.AffineOverlap) ≅
      D.V (false, true) :=
  N13IntegralCurveScheme.affineOverlapToGlueDataIso

/-- The explicit infinity overlap, oriented toward the corresponding
object of the full glue data. -/
def infinityOverlapIso :
    Spec (.of N13OrdinaryCurveOverlap.InfinityOverlap) ≅
      D.V (true, false) :=
  N13IntegralCurveScheme.infinityOverlapToGlueDataIso

/-- The explicit affine-overlap structure map agrees with the map
induced from the full glue data. -/
theorem affineOverlapIso_hom_overlapToBase :
    affineOverlapIso.hom ≫
        GlueDataClosedBaseChange.overlapToBase
          D N13IntegralCurveScheme.toBase false true =
      N13ClosedFiberOverlaps.affineOverlapToBase := by
  change
    N13IntegralCurveScheme.affineOverlapToGlueDataIso.hom ≫
        (N13IntegralCurveScheme.glueData.f false true ≫
          N13IntegralCurveScheme.glueData.ι false ≫
            N13IntegralCurveScheme.toBase) =
      N13ClosedFiberOverlaps.affineOverlapToBase
  exact N13IntegralCurveScheme.affineOverlapToGlueDataIso_hom_toBase

/-- The explicit infinity-overlap structure map agrees with the map
induced from the full glue data. -/
theorem infinityOverlapIso_hom_overlapToBase :
    infinityOverlapIso.hom ≫
        GlueDataClosedBaseChange.overlapToBase
          D N13IntegralCurveScheme.toBase true false =
      N13ClosedFiberOverlaps.infinityOverlapToBase := by
  change
    N13IntegralCurveScheme.infinityOverlapToGlueDataIso.hom ≫
        (N13IntegralCurveScheme.glueData.f true false ≫
          N13IntegralCurveScheme.glueData.ι true ≫
            N13IntegralCurveScheme.toBase) =
      N13ClosedFiberOverlaps.infinityOverlapToBase
  exact N13IntegralCurveScheme.infinityOverlapToGlueDataIso_hom_toBase

/-- Transport the explicit affine overlap base change to the full
glue-data overlap base change. -/
def affineOverlapBaseChangeTransportIso :
    pullback
        N13ClosedFiberOverlaps.affineOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ≅
      pullback
        (GlueDataClosedBaseChange.overlapToBase
          D N13IntegralCurveScheme.toBase false true)
        N13ClosedFiberCharts.closedBaseMap :=
  asIso <|
    pullback.map
      N13ClosedFiberOverlaps.affineOverlapToBase
      N13ClosedFiberCharts.closedBaseMap
      (GlueDataClosedBaseChange.overlapToBase
        D N13IntegralCurveScheme.toBase false true)
      N13ClosedFiberCharts.closedBaseMap
      affineOverlapIso.hom
      (𝟙 _)
      (𝟙 _)
      (by
        simpa only [Category.comp_id] using
          affineOverlapIso_hom_overlapToBase.symm)
      (by simp)

/-- Transport the explicit infinity overlap base change to the full
glue-data overlap base change. -/
def infinityOverlapBaseChangeTransportIso :
    pullback
        N13ClosedFiberOverlaps.infinityOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ≅
      pullback
        (GlueDataClosedBaseChange.overlapToBase
          D N13IntegralCurveScheme.toBase true false)
        N13ClosedFiberCharts.closedBaseMap :=
  asIso <|
    pullback.map
      N13ClosedFiberOverlaps.infinityOverlapToBase
      N13ClosedFiberCharts.closedBaseMap
      (GlueDataClosedBaseChange.overlapToBase
        D N13IntegralCurveScheme.toBase true false)
      N13ClosedFiberCharts.closedBaseMap
      infinityOverlapIso.hom
      (𝟙 _)
      (𝟙 _)
      (by
        simpa only [Category.comp_id] using
          infinityOverlapIso_hom_overlapToBase.symm)
      (by simp)

/-- The explicit affine-overlap base change is the overlap object used
by the pullback gluing construction. -/
def affinePullbackGluingOverlapIso :
    pullback
        N13ClosedFiberOverlaps.affineOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ≅
      pullback
        (pullback.fst
            (D.ι false ≫ N13IntegralCurveScheme.toBase)
            N13ClosedFiberCharts.closedBaseMap ≫
          D.ι false)
        (D.ι true) :=
  affineOverlapBaseChangeTransportIso ≪≫
    GlueDataClosedBaseChange.overlapBaseChangeIso
      D
      N13IntegralCurveScheme.toBase
      N13ClosedFiberCharts.closedBaseMap
      false true

/-- The explicit infinity-overlap base change is the overlap object used
by the pullback gluing construction. -/
def infinityPullbackGluingOverlapIso :
    pullback
        N13ClosedFiberOverlaps.infinityOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ≅
      pullback
        (pullback.fst
            (D.ι true ≫ N13IntegralCurveScheme.toBase)
            N13ClosedFiberCharts.closedBaseMap ≫
          D.ι true)
        (D.ι false) :=
  infinityOverlapBaseChangeTransportIso ≪≫
    GlueDataClosedBaseChange.overlapBaseChangeIso
      D
      N13IntegralCurveScheme.toBase
      N13ClosedFiberCharts.closedBaseMap
      true false

end MazurProof.N13ClosedFiberGlueOverlaps
