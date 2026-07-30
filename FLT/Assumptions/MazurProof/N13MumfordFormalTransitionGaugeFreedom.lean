import FLT.Assumptions.MazurProof.N13MumfordFormalTransitionJet
import FLT.Assumptions.MazurProof.N13ActualCechComplex

open Polynomial

namespace MazurProof.N13MumfordFormalTransitionJetGauge

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13MumfordFormalTransitionJet.R₂

abbrev Power : Type :=
  N13FormalInfinityChart.Power

abbrev InfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve

abbrev ChartCochains : Type :=
  N13ActualCechComplex.IntegralAffineRing × InfinityCurve

abbrev Overlap : Type :=
  N13MumfordFormalTransitionJet.Overlap

/-- The fixed base factor is the Laurent polynomial `t⁻² + t⁻¹`. -/
theorem baseOverlap_eq :
    N13MumfordFormalTransitionJet.baseOverlap =
      (N13FormalCurveOverlap.tPow (-2) +
        N13FormalCurveOverlap.tPow (-1), 0) := by
  rw [N13MumfordFormalTransitionJet.baseOverlap,
    N13MumfordFormalTransition.baseFormalPolyUnit,
    N13MumfordFormalTransition.coe_formalPolyUnit,
    N13FormalCurveOverlap.toOverlap_algebraMap]
  apply Prod.ext
  · simp [N13AbelChartBase.baseSmoothMumford,
      N13FormalAbelLinearization.uBase,
      N13FormalCurveOverlap.polyAtTInv,
      N13FormalCurveOverlap.tPow]
  · rfl

/-- The weighted first jet as a linear map. -/
def firstJetLinear : Overlap →ₗ[R₂] (Fin 2 → R₂) where
  toFun := N13MumfordFormalTransitionJet.firstJet
  map_add' z w := by
    funext i
    fin_cases i <;>
      simp [N13MumfordFormalTransitionJet.firstJet] <;>
      abel
  map_smul' c z := by
    funext i
    fin_cases i
    · simp [N13MumfordFormalTransitionJet.firstJet]
    · simp [N13MumfordFormalTransitionJet.firstJet]
      ring

/-- Linearized chart gauge after restoring the fixed base factor. -/
def weightedChartGauge :
    ChartCochains →ₗ[R₂] Overlap :=
  (N13FormalLineBundleCech.leftMul
      N13MumfordFormalTransitionJet.baseOverlap).comp
    N13ActualCechComplex.chartCoboundaryLinear

/-- The weighted first jet of a pure two-chart gauge. -/
def weightedGaugeJet :
    ChartCochains →ₗ[R₂] (Fin 2 → R₂) :=
  firstJetLinear.comp weightedChartGauge

/-- A scalar power series whose pure infinity-chart gauge realizes the
prescribed weighted first jet. -/
def gaugeSeedPower (z : Fin 2 → R₂) : Power :=
  PowerSeries.C (z 0 + z 1) * PowerSeries.X +
    PowerSeries.C (-z 1) * PowerSeries.X ^ 2

/-- Regard the scalar seed as an actual function on the complete infinity
chart. -/
def gaugeSeed (z : Fin 2 → R₂) : ChartCochains :=
  (0, N13FormalInfinityChart.ofPowerPair (gaugeSeedPower z, 0))

theorem infinityOverlap_gaugeSeed (z : Fin 2 → R₂) :
    N13FormalInfinityChart.infinityOverlap (gaugeSeed z).2 =
      (N13FormalInfinityChart.includePowerRing (gaugeSeedPower z), 0) := by
  rw [gaugeSeed, N13FormalInfinityChart.infinityOverlap_ofPowerPair]
  apply Prod.ext <;>
    simp [N13CechLaurentSeriesCore.includePowerPair,
      N13CechLaurentSeriesCore.includePower,
      N13FormalInfinityChart.includePowerRing]

theorem includePowerRing_gaugeSeedPower (z : Fin 2 → R₂) :
    N13FormalInfinityChart.includePowerRing (gaugeSeedPower z) =
      HahnSeries.single 1 (z 0 + z 1) +
        HahnSeries.single 2 (-z 1) := by
  simp [gaugeSeedPower, N13FormalInfinityChart.includePowerRing,
    add_mul, HahnSeries.single_mul_single]

/-- Exact overlap represented by the gauge seed after base weighting. -/
theorem weightedChartGauge_gaugeSeed (z : Fin 2 → R₂) :
    weightedChartGauge (gaugeSeed z) =
      (-(HahnSeries.single (-1) (z 0 + z 1)) -
          HahnSeries.single 0 (z 0) +
          HahnSeries.single 1 (z 1), 0) := by
  rw [weightedChartGauge, LinearMap.comp_apply,
    N13ActualCechComplex.chartCoboundaryLinear_apply,
    N13ActualCechComplex.chartCoboundary_apply]
  change
    N13FormalLineBundleCech.mulOverlap
        N13MumfordFormalTransitionJet.baseOverlap
        (N13FormalCurveOverlap.affineOverlap 0 -
          N13FormalInfinityChart.infinityOverlap (gaugeSeed z).2) =
      _
  rw [N13FormalCurveOverlap.affineOverlap_zero, zero_sub,
    infinityOverlap_gaugeSeed, baseOverlap_eq,
    includePowerRing_gaugeSeedPower]
  apply Prod.ext
  · have h₁ :
        HahnSeries.single (-2) (1 : R₂) *
            HahnSeries.single 1 (z 0 + z 1) =
          HahnSeries.single (-1) (z 0 + z 1) := by
      rw [HahnSeries.single_mul_single]
      norm_num
    have h₂ :
        HahnSeries.single (-2) (1 : R₂) *
            HahnSeries.single 2 (-z 1) =
          HahnSeries.single 0 (-z 1) := by
      rw [HahnSeries.single_mul_single]
      norm_num
    have h₃ :
        HahnSeries.single (-1) (1 : R₂) *
            HahnSeries.single 1 (z 0 + z 1) =
          HahnSeries.single 0 (z 0 + z 1) := by
      rw [HahnSeries.single_mul_single]
      norm_num
    have h₄ :
        HahnSeries.single (-1) (1 : R₂) *
            HahnSeries.single 2 (-z 1) =
          HahnSeries.single 1 (-z 1) := by
      rw [HahnSeries.single_mul_single]
      norm_num
    simp only [N13FormalLineBundleCech.mulOverlap, Prod.fst_neg,
      Prod.snd_neg, neg_zero, zero_mul,
      zero_add, mul_neg, mul_add, neg_add_rev, add_mul,
      N13FormalCurveOverlap.tPow]
    rw [h₁, h₂, h₃, h₄]
    simp only [HahnSeries.single_neg, HahnSeries.single_add, neg_neg]
    abel
  · simp [N13FormalLineBundleCech.mulOverlap]

/-- Every two-vector occurs as the weighted first jet of a genuine pure
chart coboundary. -/
theorem weightedGaugeJet_gaugeSeed (z : Fin 2 → R₂) :
    weightedGaugeJet (gaugeSeed z) = z := by
  rw [weightedGaugeJet, LinearMap.comp_apply,
    firstJetLinear, weightedChartGauge_gaugeSeed]
  funext i
  fin_cases i <;>
    simp [N13MumfordFormalTransitionJet.firstJet]

theorem weightedGaugeJet_surjective :
    Function.Surjective weightedGaugeJet :=
  fun z => ⟨gaugeSeed z, weightedGaugeJet_gaugeSeed z⟩

/-- The raw first jet does not vanish on weighted pure chart gauges.  Hence
it cannot descend through the quotient by their range without first imposing
a genuine normalization of the chart frames. -/
theorem range_weightedChartGauge_not_le_ker_firstJet :
    ¬ LinearMap.range weightedChartGauge ≤
      LinearMap.ker firstJetLinear := by
  intro h
  let z : Fin 2 → R₂ := ![1, 0]
  have hz :
      weightedChartGauge (gaugeSeed z) ∈
        LinearMap.range weightedChartGauge :=
    LinearMap.mem_range_self weightedChartGauge (gaugeSeed z)
  have hk := h hz
  have hzero : weightedGaugeJet (gaugeSeed z) = 0 := by
    simpa [weightedGaugeJet, LinearMap.comp_apply] using
      (LinearMap.mem_ker.mp hk)
  rw [weightedGaugeJet_gaugeSeed] at hzero
  have hcoord := congrFun hzero 0
  norm_num [z] at hcoord

/-- The largest additive chart-gauge submodule invisible to the weighted
first jet.  Any geometric rigidification capable of comparing the fixed
Mumford frames must land in this kernel. -/
def normalizedChartGauge : Submodule R₂ ChartCochains :=
  LinearMap.ker weightedGaugeJet

theorem mem_normalizedChartGauge_iff
    (γ : ChartCochains) :
    γ ∈ normalizedChartGauge ↔
      weightedGaugeJet γ 0 = 0 ∧
        weightedGaugeJet γ 1 = 0 := by
  change weightedGaugeJet γ = 0 ↔ _
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h₀, h₁⟩
    funext i
    fin_cases i
    · exact h₀
    · exact h₁

/-- In Laurent coordinates the normalization consists of exactly the
vanishing of the coefficients of degrees `0` and `-1`. -/
theorem mem_normalizedChartGauge_iff_coeff
    (γ : ChartCochains) :
    γ ∈ normalizedChartGauge ↔
      (weightedChartGauge γ).1.coeff 0 = 0 ∧
        (weightedChartGauge γ).1.coeff (-1) = 0 := by
  rw [mem_normalizedChartGauge_iff]
  change
    -(weightedChartGauge γ).1.coeff 0 = 0 ∧
          (-(weightedChartGauge γ).1.coeff (-1) +
            (weightedChartGauge γ).1.coeff 0) = 0 ↔
      _
  constructor
  · rintro ⟨h₀, h₁⟩
    have hc₀ :
        (weightedChartGauge γ).1.coeff 0 = 0 := by
      simpa using congrArg Neg.neg h₀
    refine ⟨hc₀, ?_⟩
    rw [hc₀, add_zero] at h₁
    simpa using congrArg Neg.neg h₁
  · rintro ⟨hc₀, hc₁⟩
    simp [hc₀, hc₁]

/-- Remove the unique pure-infinity two-jet supplied by `gaugeSeed`. -/
def normalizeGauge (γ : ChartCochains) : ChartCochains :=
  γ - gaugeSeed (weightedGaugeJet γ)

theorem normalizeGauge_mem
    (γ : ChartCochains) :
    normalizeGauge γ ∈ normalizedChartGauge := by
  change weightedGaugeJet (normalizeGauge γ) = 0
  rw [normalizeGauge, map_sub, weightedGaugeJet_gaugeSeed, sub_self]

/-- Every additive gauge is its normalized part plus its explicit
pure-infinity two-jet. -/
theorem normalizeGauge_add_gaugeSeed
    (γ : ChartCochains) :
    normalizeGauge γ + gaugeSeed (weightedGaugeJet γ) = γ :=
  sub_add_cancel _ _

/-- The preceding normalized-plus-jet decomposition is unique. -/
theorem normalized_decomposition_unique
    (γ n : ChartCochains) (z : Fin 2 → R₂)
    (hn : n ∈ normalizedChartGauge)
    (hγ : γ = n + gaugeSeed z) :
    n = normalizeGauge γ ∧ z = weightedGaugeJet γ := by
  have hnzero : weightedGaugeJet n = 0 :=
    LinearMap.mem_ker.mp hn
  have hz : weightedGaugeJet γ = z := by
    rw [hγ, map_add, hnzero, zero_add,
      weightedGaugeJet_gaugeSeed]
  refine ⟨?_, hz.symm⟩
  rw [normalizeGauge, hz]
  exact eq_sub_of_add_eq hγ.symm

end

end MazurProof.N13MumfordFormalTransitionJetGauge
