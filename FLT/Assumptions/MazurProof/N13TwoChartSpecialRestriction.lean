import FLT.Assumptions.MazurProof.N13TwoChartLineTensor
import FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility

/-!
# Chartwise special restriction of proper N13 lines

A `TwoChartLine` is an invertible ideal on each ordinary chart together with
literal equality after extension to their common overlap.  Reducing both chart
ideals modulo two preserves that overlap equality because the ordinary and
special overlap maps form a commutative square.

This construction deliberately retains both reduced ideals.  It is the
ring-theoretic restriction datum needed before identifying the special fibre
with a concrete effective divisor; it does not assert a general sheaf-descent
theorem that is absent from the pinned Mathlib API.
-/

namespace MazurProof.N13TwoChartSpecialRestriction

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Proper line data on the two ordinary charts. -/
abbrev Line : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine

/-- Coordinate ring of the reduced ordinary affine chart. -/
abbrev SpecialAffine : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

/-- Coordinate ring of the reduced infinity chart. -/
abbrev SpecialInfinity : Type :=
  N13IntegralInfinityReduction.SpecialRing

/-- Literal reduction of the affine-chart ideal. -/
def affineIdeal (L : Line) : Ideal SpecialAffine :=
  Ideal.map
    N13GeneralizedMumfordReduction.reduceCoordinate
    L.affineIdeal

/-- Literal reduction of the infinity-chart ideal. -/
def infinityIdeal (L : Line) : Ideal SpecialInfinity :=
  Ideal.map
    N13IntegralInfinityReduction.reduceCoordinate
    L.infinityIdeal

/-- Reducing the direct ordinary affine-to-infinity map gives the direct
special affine-to-infinity map.

The localized overlap square is already known.  Evaluating it on elements
coming from the unlocalized affine chart removes the intermediate affine
localization and yields precisely the direct chart map used by
`TwoChartLine.overlap_eq`. -/
theorem reduceInfinityOverlap_comp_affineToInfinityOverlap :
    N13OverlapReductionCompatibility.reduceInfinityOverlap.comp
        N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      N13SpecialCurveOverlap.affineToInfinityOverlap.comp
        N13GeneralizedMumfordReduction.reduceCoordinate := by
  apply DFunLike.ext _ _
  intro z
  have h :=
    DFunLike.congr_fun
      N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_affineOverlapToInfinityOverlap
      (algebraMap
        N13OrdinaryCurveOverlap.AffineCurve
        N13OrdinaryCurveOverlap.AffineOverlap z)
  calc
    _ =
        N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
          (N13OverlapReductionCompatibility.reduceAffineOverlap
            (algebraMap
              N13OrdinaryCurveOverlap.AffineCurve
              N13OrdinaryCurveOverlap.AffineOverlap z)) := by
      simpa only [RingHom.comp_apply,
        N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap]
        using h
    _ =
        N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
          (algebraMap SpecialAffine
            N13SpecialCurveOverlap.AffineOverlap
            (N13GeneralizedMumfordReduction.reduceCoordinate z)) := by
      congr 1
      simpa [RingHom.comp_apply] using
        DFunLike.congr_fun
          N13OverlapReductionCompatibility.reduceAffineOverlap_comp_algebraMap
          z
    _ = _ :=
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap _

/-- Reducing an integral two-chart line gives two special ideals that still
agree after extension to the special overlap. -/
theorem overlap_eq (L : Line) :
    Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (affineIdeal L) =
      Ideal.map
        (algebraMap SpecialInfinity
          N13SpecialCurveOverlap.InfinityOverlap)
        (infinityIdeal L) := by
  have h :=
    congrArg
      (Ideal.map
        N13OverlapReductionCompatibility.reduceInfinityOverlap)
      L.overlap_eq
  simpa only [affineIdeal, infinityIdeal, Ideal.map_map,
    reduceInfinityOverlap_comp_affineToInfinityOverlap,
    N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap]
    using h

/-- Compatible ideals on the two affine charts of the completed special
curve. -/
structure ChartPair where
  affineIdeal : Ideal SpecialAffine
  infinityIdeal : Ideal SpecialInfinity
  overlap_eq :
    Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        affineIdeal =
      Ideal.map
        (algebraMap SpecialInfinity
          N13SpecialCurveOverlap.InfinityOverlap)
        infinityIdeal

/-- Ring-level special restriction of a concrete integral two-chart line. -/
def restrict (L : Line) : ChartPair where
  affineIdeal := affineIdeal L
  infinityIdeal := infinityIdeal L
  overlap_eq := overlap_eq L

/-- Chartwise restriction carries tensor products of proper lines to products
of their reduced affine ideals. -/
@[simp] theorem restrict_tensor_affineIdeal
    (L M : Line) :
    (restrict (N13TwoChartLineTensor.tensor L M)).affineIdeal =
      (restrict L).affineIdeal * (restrict M).affineIdeal := by
  exact Ideal.map_mul _ _ _

/-- Chartwise restriction carries tensor products of proper lines to products
of their reduced infinity ideals. -/
@[simp] theorem restrict_tensor_infinityIdeal
    (L M : Line) :
    (restrict (N13TwoChartLineTensor.tensor L M)).infinityIdeal =
      (restrict L).infinityIdeal * (restrict M).infinityIdeal := by
  exact Ideal.map_mul _ _ _

/-- Restriction of a natural tensor power is the corresponding power of the
reduced affine ideal. -/
@[simp] theorem restrict_tensorPow_affineIdeal
    (L : Line) (n : ℕ) :
    (restrict (N13TwoChartLineTensor.tensorPow L n)).affineIdeal =
      (restrict L).affineIdeal ^ n := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13TwoChartLineTensor.tensorPow L n).affineIdeal =
      (Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        L.affineIdeal) ^ n
  rw [N13TwoChartLineTensor.tensorPow_affineIdeal, Ideal.map_pow]

/-- Restriction of a natural tensor power is the corresponding power of the
reduced infinity ideal. -/
@[simp] theorem restrict_tensorPow_infinityIdeal
    (L : Line) (n : ℕ) :
    (restrict (N13TwoChartLineTensor.tensorPow L n)).infinityIdeal =
      (restrict L).infinityIdeal ^ n := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13TwoChartLineTensor.tensorPow L n).infinityIdeal =
      (Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        L.infinityIdeal) ^ n
  rw [N13TwoChartLineTensor.tensorPow_infinityIdeal, Ideal.map_pow]

end

end MazurProof.N13TwoChartSpecialRestriction
