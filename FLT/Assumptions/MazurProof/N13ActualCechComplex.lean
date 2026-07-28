import FLT.Assumptions.MazurProof.N13ActualCechCharts

open Polynomial

/-!
# Exactness of the actual N13 additive Čech complex

The Laurent-series calculation is now expressed using the two genuine chart
rings.  The difference of their restriction maps has image exactly the
kernel of the two principal-part coefficients

`v t⁻², v t⁻¹`.

Thus the rank-two obstruction module is the actual additive Čech cokernel,
not merely a coefficientwise proxy for it.
-/

namespace MazurProof.N13ActualCechComplex

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13FormalCurveOverlap.R₂

abbrev Overlap : Type :=
  N13FormalCurveOverlap.Overlap

abbrev IntegralAffineRing : Type :=
  N13FormalCurveOverlap.IntegralAffineRing

abbrev InfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve

abbrev Obstruction : Type :=
  N13CechLaurentSeriesCore.Obstruction (R := R₂)

@[simp] theorem infinityOverlap_zero :
    N13FormalInfinityChart.infinityOverlap
        (0 : InfinityCurve) = 0 := by
  simp [N13FormalInfinityChart.infinityOverlap]

@[simp] theorem infinityOverlap_add
    (z w : InfinityCurve) :
    N13FormalInfinityChart.infinityOverlap (z + w) =
      N13FormalInfinityChart.infinityOverlap z +
        N13FormalInfinityChart.infinityOverlap w := by
  simp [N13FormalInfinityChart.infinityOverlap]

@[simp] theorem infinityOverlap_neg
    (z : InfinityCurve) :
    N13FormalInfinityChart.infinityOverlap (-z) =
      -N13FormalInfinityChart.infinityOverlap z := by
  simp [N13FormalInfinityChart.infinityOverlap]

/-- The actual affine restriction is linear over the two-adic integers. -/
theorem affineOverlap_smul
    (c : R₂) (z : IntegralAffineRing) :
    N13FormalCurveOverlap.affineOverlap (c • z) =
      c • N13FormalCurveOverlap.affineOverlap z := by
  have hscalar :
      (C c : R₂[X]) • z = c • z := by
    rw [show (C c : R₂[X]) = c • 1 by
      simp [Algebra.smul_def]]
    rw [smul_assoc, one_smul]
  have h0 :
      N13GeneralizedMumfordIntegral.coeff0 (c • z) =
        C c * N13GeneralizedMumfordIntegral.coeff0 z := by
    rw [← hscalar]
    exact LinearMap.map_smul _ _ _
  have hY :
      N13GeneralizedMumfordIntegral.coeffY (c • z) =
        C c * N13GeneralizedMumfordIntegral.coeffY z := by
    rw [← hscalar]
    exact LinearMap.map_smul _ _ _
  rw [N13FormalCurveOverlap.affineOverlap_eq_coeff,
    N13FormalCurveOverlap.affineOverlap_eq_coeff, h0, hY]
  apply Prod.ext
  · simp [← HahnSeries.single_zero_mul_eq_smul,
      HahnSeries.algebraMap_apply']
  · simp only [map_mul,
      N13FormalCurveOverlap.polyAtTInv_C]
    rw [HahnSeries.algebraMap_apply']
    simp
    simp only [← HahnSeries.single_zero_mul_eq_smul]
    rw [mul_assoc]

/-- The complete formal-infinity restriction is linear over the two-adic
integers. -/
theorem infinityOverlap_smul
    (c : R₂) (z : InfinityCurve) :
    N13FormalInfinityChart.infinityOverlap (c • z) =
      c • N13FormalInfinityChart.infinityOverlap z := by
  have hscalar :
      PowerSeries.C c • z = c • z := by
    rw [show PowerSeries.C c =
        c • (1 : N13FormalInfinityChart.Power) by
      simp [Algebra.smul_def]]
    rw [smul_assoc, one_smul]
  have h0 :
      N13FormalInfinityChart.coeff0 (c • z) =
        PowerSeries.C c *
          N13FormalInfinityChart.coeff0 z := by
    rw [← hscalar]
    exact LinearMap.map_smul _ _ _
  have hV :
      N13FormalInfinityChart.coeffV (c • z) =
        PowerSeries.C c *
          N13FormalInfinityChart.coeffV z := by
    rw [← hscalar]
    exact LinearMap.map_smul _ _ _
  rw [N13FormalInfinityChart.infinityOverlap_eq_coeff,
    N13FormalInfinityChart.infinityOverlap_eq_coeff, h0, hV]
  apply Prod.ext <;>
    simp [N13CechLaurentSeriesCore.includePowerPair,
      N13CechLaurentSeriesCore.includePower,
      ← HahnSeries.single_zero_mul_eq_smul]

/-- The genuine two-chart Čech coboundary, written with the usual
restriction difference. -/
def chartCoboundary :
    (IntegralAffineRing × InfinityCurve) →+ Overlap where
  toFun z :=
    N13FormalCurveOverlap.affineOverlap z.1 -
      N13FormalInfinityChart.infinityOverlap z.2
  map_zero' := by simp
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add,
      N13FormalCurveOverlap.affineOverlap_add,
      infinityOverlap_add]
    abel

@[simp] theorem chartCoboundary_apply
    (z : IntegralAffineRing × InfinityCurve) :
    chartCoboundary z =
      N13FormalCurveOverlap.affineOverlap z.1 -
        N13FormalInfinityChart.infinityOverlap z.2 :=
  rfl

/-- Exactness at the actual overlap: vanishing of the two obstruction
coefficients is equivalent to being a genuine chart coboundary. -/
theorem obstruction_eq_zero_iff_exists_chart_coboundary
    (z : Overlap) :
    N13CechLaurentSeriesCore.obstruction z = 0 ↔
      ∃ w : IntegralAffineRing × InfinityCurve,
        chartCoboundary w = z := by
  constructor
  · intro hz
    have hzker :
        z ∈ LinearMap.ker
          (N13CechLaurentSeriesCore.obstruction (R := R₂)) :=
      LinearMap.mem_ker.mpr hz
    rw [N13CechLaurentSeriesCore.ker_obstruction] at hzker
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.mp hzker
    obtain ⟨A, hA⟩ :=
      N13ActualCechCharts.exists_affine_preimage a ha
    obtain ⟨B, hB⟩ :=
      N13FormalInfinityChart.exists_infinity_preimage b hb
    refine ⟨(A, -B), ?_⟩
    simp [chartCoboundary, hA, hB, hab]
  · rintro ⟨w, rfl⟩
    rw [← LinearMap.mem_ker,
      N13CechLaurentSeriesCore.ker_obstruction]
    exact
      Submodule.sub_mem_sup
        (N13FormalCurveOverlap.affineOverlap_mem_affineSections w.1)
        (N13FormalInfinityChart.infinityOverlap_mem_infinitySections w.2)

/-- The actual additive Čech complex is right-exact: every obstruction pair
has a Laurent representative. -/
theorem obstruction_surjective :
    Function.Surjective
      (N13CechLaurentSeriesCore.obstruction (R := R₂)) :=
  N13CechLaurentSeriesCore.obstruction_surjective

/-- The actual chart coboundary as a two-adic linear map. -/
def chartCoboundaryLinear :
    (IntegralAffineRing × InfinityCurve) →ₗ[R₂] Overlap where
  toFun := chartCoboundary
  map_add' := chartCoboundary.map_add
  map_smul' c z := by
    change
      N13FormalCurveOverlap.affineOverlap (c • z.1) -
          N13FormalInfinityChart.infinityOverlap (c • z.2) =
        c •
          (N13FormalCurveOverlap.affineOverlap z.1 -
            N13FormalInfinityChart.infinityOverlap z.2)
    rw [affineOverlap_smul, infinityOverlap_smul, smul_sub]

@[simp] theorem chartCoboundaryLinear_apply
    (z : IntegralAffineRing × InfinityCurve) :
    chartCoboundaryLinear z = chartCoboundary z :=
  rfl

/-- Linear exactness of the genuine two-chart complex. -/
theorem range_chartCoboundaryLinear :
    LinearMap.range chartCoboundaryLinear =
      LinearMap.ker
        (N13CechLaurentSeriesCore.obstruction (R := R₂)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact LinearMap.mem_ker.mpr
      ((obstruction_eq_zero_iff_exists_chart_coboundary
        (chartCoboundary w)).2 ⟨w, rfl⟩)
  · intro hz
    obtain ⟨w, hw⟩ :=
      (obstruction_eq_zero_iff_exists_chart_coboundary z).1
        (LinearMap.mem_ker.mp hz)
    exact ⟨w, hw⟩

/-- The actual Čech cokernel with its natural two-adic module structure. -/
abbrev ActualCechH1Module : Type :=
  Overlap ⧸ LinearMap.range chartCoboundaryLinear

/-- Linear form of the canonical identification with the two obstruction
coefficients. -/
noncomputable def actualCechH1LinearEquiv :
    ActualCechH1Module ≃ₗ[R₂] Obstruction :=
  (Submodule.quotEquivOfEq
      (LinearMap.range chartCoboundaryLinear)
      (LinearMap.ker
        (N13CechLaurentSeriesCore.obstruction (R := R₂)))
      range_chartCoboundaryLinear).trans
    (LinearMap.quotKerEquivOfSurjective
      (N13CechLaurentSeriesCore.obstruction (R := R₂))
      obstruction_surjective)

/-- In particular, the genuine additive Čech cokernel is a finite
two-adic module. -/
noncomputable instance actualCechH1Module_finite :
    Module.Finite R₂ ActualCechH1Module :=
  Module.Finite.equiv actualCechH1LinearEquiv.symm

/-- The obstruction map regarded only as an additive homomorphism. -/
def obstructionAdd : Overlap →+ Obstruction :=
  (N13CechLaurentSeriesCore.obstruction (R := R₂)).toAddMonoidHom

/-- The image of the genuine chart coboundary is exactly the kernel of the
obstruction homomorphism. -/
theorem range_chartCoboundary :
    chartCoboundary.range = obstructionAdd.ker := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change
      N13CechLaurentSeriesCore.obstruction
          (chartCoboundary w) = 0
    exact
      (obstruction_eq_zero_iff_exists_chart_coboundary
        (chartCoboundary w)).2 ⟨w, rfl⟩
  · intro hz
    change
      N13CechLaurentSeriesCore.obstruction z = 0 at hz
    obtain ⟨w, hw⟩ :=
      (obstruction_eq_zero_iff_exists_chart_coboundary z).1 hz
    exact ⟨w, hw⟩

/-- First additive Čech cohomology formed from the two actual chart rings. -/
abbrev ActualCechH1 : Type :=
  Overlap ⧸ chartCoboundary.range

/-- The actual additive Čech cokernel is canonically the two-dimensional
principal-part obstruction group. -/
noncomputable def actualCechH1Equiv :
    ActualCechH1 ≃+ Obstruction :=
  (QuotientAddGroup.quotientAddEquivOfEq
      range_chartCoboundary).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      obstructionAdd obstruction_surjective)

end

end MazurProof.N13ActualCechComplex
