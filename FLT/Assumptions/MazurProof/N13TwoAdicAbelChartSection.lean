import FLT.Assumptions.MazurProof.N13InfinityBaseChange
import FLT.Assumptions.MazurProof.N13TwoAdicAbelChartLaw
import FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic

/-!
# Recovering the N13 kernel chart from Picard representatives

The two-disk Abel map is already known to be injective in `J(ℚ₂)`.
Consequently a map from an additive group into `J(ℚ₂)`, together with a
two-disk representative for each of its elements, automatically gives the
correct base pair and an injective representative map.  Those facts should
not remain separate geometric hypotheses.

For a subgroup of the rational Picard group, coefficient extension
`J(ℚ) → J(ℚ₂)` is injective as well.  Thus the only inputs left for the
formal-kernel chart are existence of the two-disk representatives and the
regularity estimate for their transported addition law.
-/

namespace MazurProof.N13TwoAdicAbelChartSection

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

universe u

abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair

abbrev Pic₂ : Type :=
  N13TwoAdicAbelChartPic.Pic

variable {K : Type u} [AddCommGroup K]

/-- A faithful Picard realization whose elements are represented by the
two-disk Abel chart.  The representative is not assumed injective and its
value at zero is not specified: both follow from `realize`. -/
structure Data (K : Type u) [AddCommGroup K] where
  toPic : K →+ Pic₂
  toPic_injective : Function.Injective toPic
  pair : K → DiskPair
  realize :
    ∀ z,
      N13TwoAdicAbelChartPic.DiskPair.centeredPic (pair z) =
        toPic z
  law :
    N13TwoAdicAbelChartLaw.PolynomialLaw
      (fun z =>
        N13TwoAdicAbelChartData.DiskPair.coord (pair z))

namespace Data

variable (D : Data K)

theorem pair_zero :
    D.pair 0 = N13TwoAdicAbelChartData.basePair := by
  apply N13TwoAdicAbelChartPic.DiskPair.centeredPic_injective
  rw [D.realize, map_zero,
    N13TwoAdicAbelChartPic.DiskPair.centeredPic_basePair]

theorem pair_injective :
    Function.Injective D.pair := by
  intro z w hzw
  apply D.toPic_injective
  rw [← D.realize z, ← D.realize w, hzw]

/-- Picard realization supplies the geometric chart package with no
additional uniqueness hypothesis. -/
def toGeometricData :
    N13TwoAdicAbelChartLaw.GeometricData K where
  pair := D.pair
  pair_zero := D.pair_zero
  pair_injective := D.pair_injective
  law := D.law

include D

theorem separated :
    N18RouteC.Separated.NSeparated K 2 :=
  D.toGeometricData.separated

end Data

abbrev RationalPic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model ℚ)
    (N13Infinity.positiveInfinityOrder ℚ)

/-- Restrict rational-to-two-adic Picard base change to a subgroup. -/
def subgroupToPic
    (H : AddSubgroup RationalPic) :
    H →+ Pic₂ :=
  N13InfinityBaseChange.picMapRatToQ₂.comp H.subtype

theorem subgroupToPic_injective
    (H : AddSubgroup RationalPic) :
    Function.Injective (subgroupToPic H) :=
  N13InfinityBaseChange.picMapRatToQ₂_injective.comp
    H.subtype_injective

/-- The reduced data required for an actual rational reduction kernel.
Faithfulness is inherited from rational Picard base change. -/
structure RationalKernelData
    (H : AddSubgroup RationalPic) where
  pair : H → DiskPair
  realize :
    ∀ z,
      N13TwoAdicAbelChartPic.DiskPair.centeredPic (pair z) =
        subgroupToPic H z
  law :
    N13TwoAdicAbelChartLaw.PolynomialLaw
      (fun z =>
        N13TwoAdicAbelChartData.DiskPair.coord (pair z))

namespace RationalKernelData

variable {H : AddSubgroup RationalPic}

def toData (D : RationalKernelData H) :
    Data H where
  toPic := subgroupToPic H
  toPic_injective := subgroupToPic_injective H
  pair := D.pair
  realize := D.realize
  law := D.law

theorem separated (D : RationalKernelData H) :
    N18RouteC.Separated.NSeparated H 2 :=
  D.toData.separated

end RationalKernelData

end

end MazurProof.N13TwoAdicAbelChartSection
