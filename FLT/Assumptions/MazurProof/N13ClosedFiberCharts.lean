import FLT.Assumptions.MazurProof.ClosedFiberAffineCore
import FLT.Assumptions.MazurProof.N13IntegralCurveScheme
import FLT.Assumptions.MazurProof.N13SpecialFibreScheme
import FLT.Assumptions.MazurProof.N13IntegralInfinityReduction

/-!
# Closed fibres of the two N13 charts

The affine and infinity reductions identify the two special charts with
the corresponding closed base changes of the integral charts at `(2)`.
This file is the project-specific adapter from the concrete reduction
theorems to `ClosedFiberAffineCore`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberCharts

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev R₂ :=
  N13GeneralizedMumfordReduction.R₂

private abbrev Affine :=
  N13GeneralizedMumfordReduction.IntegralRing

private abbrev SpecialAffine :=
  N13GeneralizedMumfordReduction.SpecialRing

private abbrev Infinity :=
  N13IntegralInfinityReduction.IntegralRing

private abbrev SpecialInfinity :=
  N13IntegralInfinityReduction.SpecialRing

/-- The closed point of the two-adic base used for the special fibre. -/
def verticalIdeal : Ideal R₂ :=
  Ideal.span ({(2 : R₂)} : Set R₂)

/-- The closed subscheme of the base cut out by `2`. -/
abbrev ClosedBase : Scheme :=
  Spec (.of (R₂ ⧸ verticalIdeal))

/-- The canonical closed immersion of the closed base into `Spec R₂`. -/
def closedBaseMap :
    ClosedBase ⟶ Spec (.of R₂) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap R₂ (R₂ ⧸ verticalIdeal)))

/-- The explicit affine coefficient map is the canonical algebra map. -/
theorem affineBaseMap_eq_algebraMap :
    N13IntegralCurveScheme.affineBaseMap =
      algebraMap R₂ Affine := by
  rfl

/-- The explicit infinity coefficient map is the canonical algebra map. -/
theorem infinityBaseMap_eq_algebraMap :
    N13IntegralCurveScheme.infinityBaseMap =
      algebraMap R₂ Infinity := by
  rfl

private theorem affine_kernel_extended :
    RingHom.ker N13GeneralizedMumfordReduction.reduceCoordinate =
      verticalIdeal.map (algebraMap R₂ Affine) := by
  rw [N13GeneralizedMumfordReduction.ker_reduceCoordinate]
  simp only [verticalIdeal, Ideal.map_span, Set.image_singleton]

private theorem infinity_kernel_extended :
    RingHom.ker N13IntegralInfinityReduction.reduceCoordinate =
      verticalIdeal.map (algebraMap R₂ Infinity) := by
  rw [N13IntegralInfinityReduction.ker_reduceCoordinate]
  simp only [verticalIdeal, Ideal.map_span, Set.image_singleton]

/-- The special affine chart is the closed fibre of the integral affine
chart at `2`. -/
def affineClosedFiberIso :
    pullback
        (N13IntegralCurveScheme.chartToBase false)
        closedBaseMap ≅
      N13SpecialFibreScheme.chart false := by
  rw [show
    N13IntegralCurveScheme.chartToBase false =
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R₂ Affine)) by
      change
        Spec.map
            (CommRingCat.ofHom
              N13IntegralCurveScheme.affineBaseMap) =
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R₂ Affine))
      rw [affineBaseMap_eq_algebraMap]]
  exact
    ClosedFiberAffineCore.specPullbackIsoOfReduction
      verticalIdeal
      N13GeneralizedMumfordReduction.reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
      affine_kernel_extended

/-- The special infinity chart is the closed fibre of the integral
infinity chart at `2`. -/
def infinityClosedFiberIso :
    pullback
        (N13IntegralCurveScheme.chartToBase true)
        closedBaseMap ≅
      N13SpecialFibreScheme.chart true := by
  rw [show
    N13IntegralCurveScheme.chartToBase true =
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R₂ Infinity)) by
      change
        Spec.map
            (CommRingCat.ofHom
              N13IntegralCurveScheme.infinityBaseMap) =
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R₂ Infinity))
      rw [infinityBaseMap_eq_algebraMap]]
  exact
    ClosedFiberAffineCore.specPullbackIsoOfReduction
      verticalIdeal
      N13IntegralInfinityReduction.reduceCoordinate
      N13IntegralInfinityReduction.reduceCoordinate_surjective
      infinity_kernel_extended

end MazurProof.N13ClosedFiberCharts
