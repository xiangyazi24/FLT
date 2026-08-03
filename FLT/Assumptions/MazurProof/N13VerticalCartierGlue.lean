import FLT.Assumptions.MazurProof.N13VerticalCartierCharts
import FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility

/-!
# Gluing the N13 vertical Cartier equations

The image of `2` cuts out the closed fibre on both ordinary charts.  On the
ordinary overlap these two local equations agree literally, rather than only
up to an unspecified unit.  Hence the Cartier transition of the closed fibre
is the identity, as is every integral power of that transition.

This is the project-specific gluing statement needed later to show that a
vertical twist specializes trivially.  It uses no general Cartier-divisor
infrastructure.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13VerticalCartierGlue

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Affine :=
  N13OrdinaryCurveOverlap.AffineCurve

abbrev Infinity :=
  N13OrdinaryCurveOverlap.InfinityCurve

abbrev AffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap

abbrev InfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap

abbrev SpecialAffineOverlap :=
  N13SpecialCurveOverlap.AffineOverlap

abbrev SpecialInfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap

/-- The affine-chart Cartier equation restricted to the ordinary overlap. -/
def affineOverlapParameter : AffineOverlap :=
  algebraMap Affine AffineOverlap
    N13VerticalCartierCharts.affineParameter

/-- The infinity-chart Cartier equation restricted to the ordinary overlap. -/
def infinityOverlapParameter : InfinityOverlap :=
  algebraMap Infinity InfinityOverlap
    N13VerticalCartierCharts.infinityParameter

/-- The two local equations are the same after the ordinary chart
transition. -/
theorem overlapEquiv_affineOverlapParameter :
    N13OrdinaryCurveOverlap.overlapEquiv
        affineOverlapParameter =
      infinityOverlapParameter := by
  change
    N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap
        (algebraMap Affine AffineOverlap
          (algebraMap N13OrdinaryCurveOverlap.R₂ Affine 2)) =
      algebraMap Infinity InfinityOverlap
        (algebraMap N13OrdinaryCurveOverlap.R₂ Infinity 2)
  rw [N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap]
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly
            (R := N13OrdinaryCurveOverlap.R₂))
          (Polynomial.C 2)) =
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap 2
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_of]
  simp [N13OrdinaryCurveOverlap.affineCoeffMap]

/-- The reverse ordinary chart transition also identifies the two local
Cartier equations. -/
theorem overlapEquiv_symm_infinityOverlapParameter :
    N13OrdinaryCurveOverlap.overlapEquiv.symm
        infinityOverlapParameter =
      affineOverlapParameter := by
  apply N13OrdinaryCurveOverlap.overlapEquiv.injective
  rw [N13OrdinaryCurveOverlap.overlapEquiv.apply_symm_apply]
  exact overlapEquiv_affineOverlapParameter.symm

/-- The principal Cartier ideals agree on the overlap. -/
theorem map_affineCartierIdeal :
    Ideal.map
        N13OrdinaryCurveOverlap.overlapEquiv.toRingHom
        (Ideal.span ({affineOverlapParameter} : Set AffineOverlap)) =
      Ideal.span ({infinityOverlapParameter} : Set InfinityOverlap) := by
  rw [Ideal.map_span, Set.image_singleton]
  change
    Ideal.span
        ({N13OrdinaryCurveOverlap.overlapEquiv
          affineOverlapParameter} : Set InfinityOverlap) =
      Ideal.span ({infinityOverlapParameter} : Set InfinityOverlap)
  rw [overlapEquiv_affineOverlapParameter]

/-- Because the two equations agree literally, their Cartier transition unit
is the identity. -/
def overlapTransition : InfinityOverlapˣ :=
  1

theorem overlapTransition_spec :
    N13OrdinaryCurveOverlap.overlapEquiv
        affineOverlapParameter =
      (overlapTransition : InfinityOverlap) *
        infinityOverlapParameter := by
  simpa [overlapTransition] using
    overlapEquiv_affineOverlapParameter

/-- Every vertical tensor power still has identity transition. -/
theorem overlapTransition_zpow (n : ℤ) :
    overlapTransition ^ n = 1 := by
  simp [overlapTransition]

/-- Reduction of the vertical transition on the special overlap is the
identity. -/
theorem reduce_overlapTransition :
    N13OverlapReductionCompatibility.reduceInfinityOverlap
        (overlapTransition : InfinityOverlap) =
      (1 : SpecialInfinityOverlap) := by
  simp [overlapTransition]

/-- The same holds for every integral vertical twist. -/
theorem reduce_overlapTransition_zpow (n : ℤ) :
    N13OverlapReductionCompatibility.reduceInfinityOverlap
        ((overlapTransition ^ n : InfinityOverlapˣ) :
          InfinityOverlap) =
      (1 : SpecialInfinityOverlap) := by
  rw [overlapTransition_zpow]
  simp

end

end MazurProof.N13VerticalCartierGlue
