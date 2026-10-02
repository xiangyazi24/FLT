import FLT.Assumptions.MazurProof.N13SpecialSixJetOrders
import FLT.Assumptions.MazurProof.N13SpecialFinitePointOrders

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The unchanged degree-four principal-comparison/code bridge. All six local
orders are tied to the actual chart ideals and to the SAME numerator of
the comparison. The bounded certificate then forces the code difference
to vanish. No Picard-code compatibility or additivity premise is assumed.
-/

namespace MazurProof.N13SpecialDegreeFourCode

noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders

private theorem include_ne_zero (p : P) (hp : p ≠ 0) : includeSeries p ≠ 0 := by
  have hne := (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)).ne hp
  rw [map_zero] at hne
  exact hne

theorem finite_comparison_order_balance
    (a : K) (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    (includeSeries (finiteBranch a negative h.aNum)).order + (finiteTensorOrder a negative D E : ℤ) =
      (includeSeries (finiteBranch a negative h.aDen)).order + (finiteTensorOrder a negative F H : ℤ) := by
  have he := congrArg (Ideal.map (finiteBranch a negative)) h.affine_eq
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    N13SpecialFinitePointOrders.tensor_branch_ideal] at he
  exact order_balance_of_principal_power_eq _ _
    (finiteBranch_ne_zero a negative _ h.aNum_ne) (finiteBranch_ne_zero a negative _ h.aDen_ne) _ _ he

theorem finite_cleared_order_balance
    (a : K) (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (includeSeries (finiteBranch a negative z)).order + (finiteTensorOrder a negative D E : ℤ) =
      (finiteTensorOrder a negative F H : ℤ) +
        (includeSeries (N13SpecialFiniteBranchJets.evalBase a (tensorPolynomial D E))).order := by
  have hi := finite_comparison_order_balance a negative D E F H h
  have he := congrArg (includeSeries.comp (finiteBranch a negative)) hcross
  simp only [RingHom.comp_apply, map_mul, finiteBranch_xClass] at he
  have ho := congrArg HahnSeries.order he
  rw [HahnSeries.order_mul
      (include_ne_zero _ (finiteBranch_ne_zero a negative _ h.aNum_ne))
      (include_ne_zero _ (evalBase_ne_zero a _ (tensorPolynomial_monic D E).ne_zero)),
    HahnSeries.order_mul (include_ne_zero _ (finiteBranch_ne_zero a negative _ h.aDen_ne))
      (include_ne_zero _ (finiteBranch_ne_zero a negative z hz))] at ho
  omega

theorem finite_sheet_difference
    (a : K) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (includeSeries (finiteBranch a false z)).order - (includeSeries (finiteBranch a true z)).order =
      ((finiteTensorOrder a false F H : ℤ) - finiteTensorOrder a true F H) -
        ((finiteTensorOrder a false D E : ℤ) - finiteTensorOrder a true D E) := by
  have hp := finite_cleared_order_balance a false D E F H h z hz hcross
  have hm := finite_cleared_order_balance a true D E F H h z hz hcross
  omega

theorem infinity_cleared_order_balance
    (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (affineBranch negative z).order + (tensorOrder negative D E : ℤ) +
        (tensorPolynomial D E).natDegree = (tensorOrder negative F H : ℤ) := by
  have hnonzero (w : R) (hw : w ≠ 0) : affineBranch negative w ≠ 0 := by
    simpa only [map_zero] using (N13SpecialBranchFaithfulness.affineBranch_injective negative).ne hw
  have ha := hnonzero h.aNum h.aNum_ne
  have hb := hnonzero h.aDen h.aDen_ne
  have hc := include_ne_zero _ (N13SpecialBranchFaithfulness.infinityBranch_ne_zero negative _ h.iNum_ne)
  have hd := include_ne_zero _ (N13SpecialBranchFaithfulness.infinityBranch_ne_zero negative _ h.iDen_ne)
  have he := congrArg HahnSeries.order (cross_relation negative _ _ _ _ h.overlap_eq)
  rw [HahnSeries.order_mul ha hd, HahnSeries.order_mul hb hc] at he
  have hi := comparison_infinity_order_balance negative D E F H h
  have hn := congrArg (affineBranch negative) hcross
  have hbase (p : K[X]) : affineBranch negative (N13GoodCoordinateRingTwo.xClass p) = base p := by
    cases negative <;> simp [affineBranch]
  simp only [map_mul, hbase] at hn
  have hq := (tensorPolynomial_monic D E).ne_zero
  have ho := congrArg HahnSeries.order hn
  rw [HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hq),
    HahnSeries.order_mul hb (hnonzero z hz), N13BranchNorm.evalPoly_order K _ hq] at ho
  omega

theorem infinity_sheet_difference
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (plus z).order - (minus z).order =
      ((tensorOrder false F H : ℤ) - tensorOrder true F H) -
        ((tensorOrder false D E : ℤ) - tensorOrder true D E) := by
  have hp := infinity_cleared_order_balance false D E F H h z hz hcross
  have hm := infinity_cleared_order_balance true D E F H h z hz hcross
  change (plus z).order + _ + _ = _ at hp
  change (minus z).order + _ + _ = _ at hm
  omega

theorem weightedLocalCode_eq_code_difference
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    weightedLocalCode z =
      (N13SpecialAbelCode.divisorCode F + N13SpecialAbelCode.divisorCode H) -
        (N13SpecialAbelCode.divisorCode D + N13SpecialAbelCode.divisorCode E) := by
  have hzero := congrArg (fun n : ℤ => (n : ZMod 19)) (finite_sheet_difference 0 D E F H h z hz hcross)
  have hone := congrArg (fun n : ℤ => (n : ZMod 19)) (finite_sheet_difference 1 D E F H h z hz hcross)
  have hinfinity := congrArg (fun n : ℤ => (n : ZMod 19)) (infinity_sheet_difference D E F H h z hz hcross)
  push_cast at hzero hone hinfinity
  rw [divisorCode_eq_counts, divisorCode_eq_counts, divisorCode_eq_counts, divisorCode_eq_counts]
  change ((includeSeries (finiteBranch 0 false z)).order : ZMod 19) -
      ((includeSeries (finiteBranch 0 true z)).order : ZMod 19) +
      7 * ((includeSeries (finiteBranch 1 false z)).order : ZMod 19) -
      7 * ((includeSeries (finiteBranch 1 true z)).order : ZMod 19) +
      8 * ((plus z).order : ZMod 19) - 8 * ((minus z).order : ZMod 19) = _
  simp only [countCode, finiteTensorOrder, tensorOrder, Nat.cast_add] at hzero hone hinfinity ⊢
  linear_combination hzero + 7 * hone + 8 * hinfinity

/-- The exact previously missing B03 bridge, without new hypotheses. -/
theorem degreeFourCode_eq_of_comparison
    (D E F H : N13SymmetricSquareTwo.EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (N13SpecialDivisorCharts.tensor (N13SpecialDivisorCharts.ofDivisor D) (N13SpecialDivisorCharts.ofDivisor E))
      (N13SpecialDivisorCharts.tensor (N13SpecialDivisorCharts.ofDivisor F) (N13SpecialDivisorCharts.ofDivisor H))) :
    N13SpecialAbelCode.divisorCode D + N13SpecialAbelCode.divisorCode E =
      N13SpecialAbelCode.divisorCode F + N13SpecialAbelCode.divisorCode H := by
  obtain ⟨a, b, hn, hcross, hjets, hcode⟩ := N13SpecialCertifiedNumerator.exists_certified_numerator D E F H h
  have hz := weightedLocalCode_of_certified_jets a b hn hjets hcode
  have he := weightedLocalCode_eq_code_difference D E F H h (function a b) hn hcross
  rw [hz] at he
  exact (sub_eq_zero.mp he.symm).symm

end
end MazurProof.N13SpecialDegreeFourCode
