import FLT.Assumptions.MazurProof.N13KernelBaseDivisor
import FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

The finite special divisor C+B forces both actual generic infinity orders
to vanish. The proof uses the integral branch constant coefficients and
the literal element t-1 in the reduced infinity ideal; it does not infer
generic marking from an independent integer attached to Data.
-/

namespace MazurProof.N13KernelInfinityMultiplicity

noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev S := N13SpecialInfinityChart.CoordinateRing
abbrev SP := PowerSeries (ZMod 2)
abbrev red := N13IntegralInfinityReduction.reduceCoordinate
abbrev redBase := N13IntegralInfinityReduction.reduceBase

theorem plus_constant_reduction (a : B) :
    PowerSeries.constantCoeff (N13SpecialInfinityBranchJets.plus (red a)) =
      redBase (PowerSeries.constantCoeff (positiveIntegralExpansion a)) := by
  rw [N13SpecialInfinityBranchJets.plus_normal_form,
    N13InfinityBranchJets.plus_normal_form]
  simp [N13SpecialInfinityBranchJets.beta_eq_coe,
    N13InfinityBranchJets.beta_eq_coe,
    N13SpecialInfinityBranchJets.r₀_constant,
    N13FormalInfinityBranches.branchZero_constantCoeff,
    N13IntegralInfinityReduction.reducePoly]

theorem minus_constant_reduction (a : B) :
    PowerSeries.constantCoeff (N13SpecialInfinityBranchJets.minus (red a)) =
      redBase (PowerSeries.constantCoeff (negativeIntegralExpansion a)) := by
  rw [N13SpecialInfinityBranchJets.minus_normal_form,
    N13InfinityBranchJets.minus_normal_form]
  simp [N13SpecialInfinityBranchJets.beta_eq_coe,
    N13InfinityBranchJets.beta_eq_coe,
    N13SpecialInfinityBranchJets.r₁_constant,
    N13FormalInfinityBranches.branchOne_constantCoeff,
    N13IntegralInfinityReduction.reducePoly,
    ZMod.neg_eq_self_mod_two]

theorem baseDivisor_infinity_t_sub_one_mem :
    N13SpecialInfinityChart.tClass - 1 ∈
      (N13SpecialDivisorCharts.ofDivisor baseDivisor).infinityIdeal := by
  change N13SpecialInfinityChart.tClass - 1 ∈
    (⊤ : Ideal S) * N13SpecialDivisorCharts.infinityPointIdeal 1 0
  rw [Ideal.top_mul]
  change N13SpecialInfinityChart.tClass - 1 ∈
    Ideal.span ({N13SpecialInfinityChart.tClass -
      algebraMap (Polynomial (ZMod 2)) S (Polynomial.C 1),
      N13SpecialInfinityChart.vClass -
        algebraMap (Polynomial (ZMod 2)) S (Polynomial.C 0)} : Set S)
  apply Ideal.subset_span
  simp

private theorem multiplicity_zero
    (I : Ideal B) (f : B →+* P) (g : S →+* SP)
    (hconstant : ∀ a, PowerSeries.constantCoeff (g (red a)) =
      redBase (PowerSeries.constantCoeff (f a)))
    (ht : g N13SpecialInfinityChart.tClass = PowerSeries.X)
    (hmem : N13SpecialInfinityChart.tClass - 1 ∈ Ideal.map red I)
    (n : ℕ)
    (hn : Ideal.map (N13TwoAdicInfinityCompatibility.powerMap.comp f) I =
      Ideal.span ({PowerSeries.X ^ n} : Set QP)) : n = 0 := by
  by_contra hpos
  let e : S →+* ZMod 2 := PowerSeries.constantCoeff.comp g
  have hI : Ideal.map red I ≤ RingHom.ker e := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change e (red a) = 0
    have hm := Ideal.mem_map_of_mem
      (N13TwoAdicInfinityCompatibility.powerMap.comp f) ha
    rw [hn, Ideal.mem_span_singleton] at hm
    have hc := PowerSeries.X_pow_dvd_iff.mp hm 0 (Nat.pos_of_ne_zero hpos)
    have hi : PowerSeries.constantCoeff (f a) = 0 := by
      apply IsFractionRing.injective ℤ_[2] ℚ_[2]
      simpa [N13TwoAdicInfinityCompatibility.powerMap,
        N13TwoAdicInfinityCompatibility.coeffMap] using hc
    change PowerSeries.constantCoeff (g (red a)) = 0
    rw [hconstant, hi, map_zero]
  have hz : e (N13SpecialInfinityChart.tClass - 1) = 0 := hI hmem
  have hv : e (N13SpecialInfinityChart.tClass - 1) = -1 := by
    simp [e, ht]
  rw [hv] at hz
  exact neg_ne_zero.mpr one_ne_zero hz

theorem multiplicities_zero_of_special_divisor
    (D : Data) (hs : D.specialDivisor = baseDivisor)
    (p m : ℕ) (hm : HasInfinityMultiplicities D.charts p m) : p = 0 ∧ m = 0 := by
  have ht : N13SpecialInfinityChart.tClass - 1 ∈ Ideal.map red D.charts.infinityIdeal := by
    have h := D.special_infinity
    rw [hs] at h
    change Ideal.map red D.charts.infinityIdeal = _ at h
    rw [h]
    exact baseDivisor_infinity_t_sub_one_mem
  exact ⟨multiplicity_zero _ positiveIntegralExpansion N13SpecialInfinityBranchJets.plus
      plus_constant_reduction N13SpecialInfinityBranchJets.plus_t ht p hm.1,
    multiplicity_zero _ negativeIntegralExpansion N13SpecialInfinityBranchJets.minus
      minus_constant_reduction N13SpecialInfinityBranchJets.minus_t ht m hm.2⟩

/-- The same certified witness has affine degree two and effective nInf=-1.
Consequently its actual raw mark is -2 before balancing the graph. -/
theorem certified_finite_graph (D : Data) (hD : Certified D)
    (hs : D.specialDivisor = baseDivisor) :
    ∃ E : N13Mumford.SemiMumford Q₂,
      EffectiveChamber E ∧ E.u.natDegree = 2 ∧ E.nInf = -1 ∧
      genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E ∧
      AffineVerticallySaturated D.charts := by
  obtain ⟨E, he, hr, hsat, hm⟩ := hD
  obtain ⟨hp, hn⟩ := multiplicities_zero_of_special_divisor D hs _ _ hm
  have hpc := positiveMultiplicity_cast E he
  have hnc := negativeMultiplicity_cast E he
  rw [hp] at hpc
  rw [hn] at hnc
  refine ⟨E, he, ?_, ?_, hr, hsat⟩ <;> omega

theorem chosen_translated_finite_graph (z : Kernel) :
    ∃ E : N13Mumford.SemiMumford Q₂,
      EffectiveChamber E ∧ E.u.natDegree = 2 ∧ E.nInf = -1 ∧
      genericRaw (N13CalibratedChooser.choose ((z : N13ConstructedSpecialization.G) +
          baseTranslate)).charts
        (N13CalibratedChooser.choose ((z : N13ConstructedSpecialization.G) +
          baseTranslate)).infinityOrder = SexticMumford.semiMumfordRaw Model E ∧
      AffineVerticallySaturated
        (N13CalibratedChooser.choose ((z : N13ConstructedSpecialization.G) +
          baseTranslate)).charts :=
  certified_finite_graph _ (N13CalibratedChooser.choose_certified _)
    (chosen_translated_divisor z)

end
end MazurProof.N13KernelInfinityMultiplicity
