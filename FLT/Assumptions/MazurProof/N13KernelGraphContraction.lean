import FLT.Assumptions.MazurProof.N13KernelInfinityMultiplicity
import FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

The finite C+B special divisor is the literal graph ideal (X²+X,Y).
Vertical saturation then identifies a certified affine lattice with the
canonical contraction of its same generic Mumford graph. These conclusions
retain the actual witness and do not use normal-form spread coherence.
-/

namespace MazurProof.N13KernelGraphContraction

noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelInfinityMultiplicity
open N13TwoChartPicardRealization N13EffectiveGraphData N13EffectiveInfinityRepair
open scoped nonZeroDivisors
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev A := N13IntegralModelContraction.IntegralRing
abbrev R := N13IntegralModelContraction.RationalRing
local instance : Algebra A R := N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
local instance : IsLocalization N13IntegralModelContraction.verticalScalars R :=
  N13IntegralModelContraction.rationalRing_isLocalization

theorem baseDivisor_affineIdeal :
    (N13SpecialDivisorCharts.ofDivisor baseDivisor).affineIdeal =
      N13SpecialQuotientBasis.specialIdeal := by
  change N13GoodCoordinateRingTwo.mumfordIdeal (X - C 0) (C 0) *
    N13GoodCoordinateRingTwo.mumfordIdeal (X - C 1) (C 0) = _
  simp only [C_0, C_1, sub_zero]
  have hm := GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
    N13GoodCoordinateRingTwo.xClassHom N13GoodCoordinateRingTwo.yClass
    X (X - 1) 0 0 0 (by simp) (by simp)
    (show ∃ a b : (ZMod 2)[X], a * X + b * (X - 1) = 1 from
      ⟨1, -1, by ring⟩)
  have hp : (X : (ZMod 2)[X]) * (X - 1) = X ^ 2 + X := by
    have hn : (-1 : (ZMod 2)[X]) = 1 := by norm_num
    rw [sub_eq_add_neg, hn]
    ring
  simpa [N13GoodCoordinateRingTwo.mumfordIdeal,
    GeneralizedGraphIdealCore.graphIdeal, GeneralizedGraphIdealCore.ySubClass,
    N13GoodCoordinateRingTwo.ySubClass,
    N13SpecialQuotientBasis.specialIdeal, hp] using hm

theorem contract_map_eq_of_saturated (L : Line) (hs : AffineVerticallySaturated L) :
    N13IntegralModelContraction.contractIdeal
      (Ideal.map N13IntegralFractionalHull.integralToRational L.affineIdeal) =
        L.affineIdeal := by
  apply le_antisymm
  · intro a ha
    change algebraMap A R a ∈ Ideal.map (algebraMap A R) L.affineIdeal at ha
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      N13IntegralModelContraction.verticalScalars] at ha
    obtain ⟨q, hq, hqa⟩ := ha
    obtain ⟨r, hr, hqr⟩ := hq
    rw [← hqr] at hqa
    exact hs r (mem_nonZeroDivisors_iff_ne_zero.mp hr) a hqa
  · intro a ha
    exact Ideal.mem_map_of_mem (algebraMap A R) ha

theorem map_affineIdeal_of_semiRaw
    (D : Data) (E : N13Mumford.SemiMumford Q₂)
    (hr : genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E) :
    Ideal.map N13IntegralFractionalHull.integralToRational D.charts.affineIdeal =
      SexticMumford.mumfordIdeal Model E.u E.v := by
  have hu := congrArg Prod.fst hr
  have hf := congrArg (fun U : Units N13IntegralFractionalHull.RationalFractionalIdeal =>
    (U : N13IntegralFractionalHull.RationalFractionalIdeal)) hu
  change (genericIdealUnit D.charts : N13IntegralFractionalHull.RationalFractionalIdeal) =
    (SexticMumford.mumfordIdealUnit Model E :
      N13IntegralFractionalHull.RationalFractionalIdeal) at hf
  rw [coe_genericIdealUnit, SexticMumford.coe_mumfordIdealUnit] at hf
  exact FractionalIdeal.coeIdeal_injective hf

/-- The balanced graph has the exact required contracted special ideal.
Its class still needs the separately proved mark-shift identity. -/
theorem balancedGraph_map_contract
    (D : Data) (E : N13Mumford.SemiMumford Q₂) (hd : E.u.natDegree ≤ 2)
    (hr : genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E)
    (hsat : AffineVerticallySaturated D.charts)
    (hspecial : D.specialDivisor = baseDivisor) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
      (N13IntegralModelContraction.contractIdeal
        (N13CanonicalContractionQuotient.graphIdeal (balancedGraph E hd).toSemi)) =
      N13SpecialQuotientBasis.specialIdeal := by
  change Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
    (N13IntegralModelContraction.contractIdeal
      (SexticMumford.mumfordIdeal Model E.u E.v)) = _
  rw [← map_affineIdeal_of_semiRaw D E hr, contract_map_eq_of_saturated D.charts hsat]
  have h := D.special_affine
  rw [hspecial] at h
  exact h.trans baseDivisor_affineIdeal

end
end MazurProof.N13KernelGraphContraction
