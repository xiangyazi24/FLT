import Mathlib
import FLT.Assumptions.MazurProof.RealTopologyS1

/-!
# Real topology route, S4: the right-branch elliptic integral

This file starts the analytic side of the real-torsion route using the same
short model as S3:

`shortCubic A B x = x^3 + A*x^2 + B*x`.

The later target is an injective additive hom from the kernel of
`componentBitHom` to an additive circle.  Here we only set up the integrand
and prove the elementary positivity/continuity facts on the right of the
chosen branch point.
-/

open MeasureTheory Set Real Filter Topology
open scoped Topology

namespace MazurProof.RealTopology

noncomputable section

/-- The right-branch integrand `1 / sqrt(shortCubic A B x)`. -/
def rightIntegrand (A B : ℝ) (x : ℝ) : ℝ :=
  (√(shortCubic A B x))⁻¹

/-- The tail integral `σ(x) = ∫_{x}^{∞} dt / sqrt(shortCubic A B t)`. -/
def sigma (A B : ℝ) (x : ℝ) : ℝ :=
  ∫ t in Ioi x, rightIntegrand A B t

/-- The half-period at the chosen right branch point. -/
def halfPeriod (A B e : ℝ) : ℝ :=
  sigma A B e

/-- Predicate selecting a root whose right ray is on the unbounded real component. -/
def IsRightSigmaRoot (A B e : ℝ) : Prop :=
  shortCubic A B e = 0 ∧
    0 < shortCubicDeriv A B e ∧
      ∀ ⦃x : ℝ⦄, e < x → 0 < shortCubic A B x

/-- The quotient factor `(shortCubic A B t - shortCubic A B e) / (t - e)`. -/
def shortCubicRootFactor (A B e t : ℝ) : ℝ :=
  t ^ 2 + t * e + e ^ 2 + A * (t + e) + B

theorem shortCubic_eq_sub_mul_rootFactor
    {A B e t : ℝ} (hroot : shortCubic A B e = 0) :
    shortCubic A B t = (t - e) * shortCubicRootFactor A B e t := by
  calc
    shortCubic A B t = shortCubic A B t - shortCubic A B e := by simp [hroot]
    _ = (t - e) * shortCubicRootFactor A B e t := by
      simp [shortCubic, shortCubicRootFactor]
      ring_nf

theorem shortCubicRootFactor_at_root {A B e : ℝ} :
    shortCubicRootFactor A B e e = shortCubicDeriv A B e := by
  simp [shortCubicRootFactor, shortCubicDeriv]
  ring_nf

theorem exists_rootFactor_pos_nhdsGT
    {A B e : ℝ}
    (hderiv : 0 < shortCubicDeriv A B e) :
    ∃ δ > 0, ∀ ⦃t : ℝ⦄, e < t → t < e + δ →
      0 < shortCubicRootFactor A B e t := by
  have hcont : Continuous (fun t : ℝ => shortCubicRootFactor A B e t) := by
    unfold shortCubicRootFactor
    fun_prop
  have hpos_at : 0 < shortCubicRootFactor A B e e := by
    simpa [shortCubicRootFactor_at_root] using hderiv
  have hnhds : {t : ℝ | 0 < shortCubicRootFactor A B e t} ∈ 𝓝 e :=
    (isOpen_lt continuous_const hcont).mem_nhds hpos_at
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t _ ht_upper
  exact hδ (by
    rw [Metric.mem_ball, Real.dist_eq]
    have hlt_abs : |t - e| < δ := by
      rw [abs_lt]
      constructor
      · linarith
      · linarith
    simpa [sub_eq_add_neg] using hlt_abs)

theorem exists_rootFactor_gt_half_deriv_nhdsGT
    {A B e : ℝ}
    (hderiv : 0 < shortCubicDeriv A B e) :
    ∃ δ > 0, ∀ ⦃t : ℝ⦄, e < t → t < e + δ →
      shortCubicDeriv A B e / 2 < shortCubicRootFactor A B e t := by
  have hcont : Continuous (fun t : ℝ => shortCubicRootFactor A B e t) := by
    unfold shortCubicRootFactor
    fun_prop
  have hhalf_at :
      shortCubicDeriv A B e / 2 < shortCubicRootFactor A B e e := by
    rw [shortCubicRootFactor_at_root]
    linarith
  have hnhds :
      {t : ℝ | shortCubicDeriv A B e / 2 < shortCubicRootFactor A B e t} ∈ 𝓝 e :=
    (isOpen_lt continuous_const hcont).mem_nhds hhalf_at
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t _ ht_upper
  exact hδ (by
    rw [Metric.mem_ball, Real.dist_eq]
    have hlt_abs : |t - e| < δ := by
      rw [abs_lt]
      constructor
      · linarith
      · linarith
    simpa [sub_eq_add_neg] using hlt_abs)

theorem exists_shortCubic_lower_bound_near_root
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    ∃ δ > 0, ∀ ⦃t : ℝ⦄, e < t → t < e + δ →
      (shortCubicDeriv A B e / 2) * (t - e) < shortCubic A B t := by
  rcases exists_rootFactor_gt_half_deriv_nhdsGT (A := A) (B := B) (e := e) hderiv with
    ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht_left ht_right
  rw [shortCubic_eq_sub_mul_rootFactor hroot]
  have ht_sub : 0 < t - e := sub_pos.mpr ht_left
  nlinarith [mul_lt_mul_of_pos_left (hδ ht_left ht_right) ht_sub]

theorem half_cube_le_shortCubic_of_large
    {A B t : ℝ}
    (h1 : 1 ≤ t) (hA : 4 * |A| ≤ t) (hB : 4 * |B| ≤ t) :
    (1 / 2 : ℝ) * t ^ 3 ≤ shortCubic A B t := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one h1
  have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos ht_pos
  have hA_abs_nonneg : 0 ≤ |A| := abs_nonneg A
  have hB_abs_nonneg : 0 ≤ |B| := abs_nonneg B
  have hA_bound : |A| * t ^ 2 ≤ (1 / 4 : ℝ) * t ^ 3 := by
    have hA' : |A| ≤ t / 4 := by linarith
    calc
      |A| * t ^ 2 ≤ (t / 4) * t ^ 2 := mul_le_mul_of_nonneg_right hA' ht_sq_pos.le
      _ = (1 / 4 : ℝ) * t ^ 3 := by ring
  have hB_bound : |B| * t ≤ (1 / 4 : ℝ) * t ^ 3 := by
    have hB' : |B| ≤ t / 4 := by linarith
    have ht_le_sq : t ≤ t ^ 2 := by nlinarith
    calc
      |B| * t ≤ (t / 4) * t := mul_le_mul_of_nonneg_right hB' ht_pos.le
      _ = (1 / 4 : ℝ) * t ^ 2 := by ring
      _ ≤ (1 / 4 : ℝ) * t ^ 3 := by
        have : t ^ 2 ≤ t ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left ht_le_sq ht_pos.le]
        nlinarith
  have hA_term : A * t ^ 2 ≥ -((1 / 4 : ℝ) * t ^ 3) := by
    have hneg_abs : -|A| ≤ A := neg_abs_le A
    have hmul : -|A| * t ^ 2 ≤ A * t ^ 2 :=
      mul_le_mul_of_nonneg_right hneg_abs ht_sq_pos.le
    nlinarith
  have hB_term : B * t ≥ -((1 / 4 : ℝ) * t ^ 3) := by
    have hneg_abs : -|B| ≤ B := neg_abs_le B
    have hmul : -|B| * t ≤ B * t :=
      mul_le_mul_of_nonneg_right hneg_abs ht_pos.le
    nlinarith
  unfold shortCubic
  nlinarith

def tailThreshold (A B : ℝ) : ℝ :=
  max 1 (max (4 * |A|) (4 * |B|))

theorem one_le_tailThreshold (A B : ℝ) :
    1 ≤ tailThreshold A B := by
  unfold tailThreshold
  exact le_max_left _ _

theorem tailThreshold_pos (A B : ℝ) :
    0 < tailThreshold A B :=
  zero_lt_one.trans_le (one_le_tailThreshold A B)

theorem half_cube_le_shortCubic_of_tailThreshold_le
    {A B t : ℝ} (ht : tailThreshold A B ≤ t) :
    (1 / 2 : ℝ) * t ^ 3 ≤ shortCubic A B t := by
  apply half_cube_le_shortCubic_of_large
  · exact le_trans (le_max_left 1 (max (4 * |A|) (4 * |B|))) ht
  · exact le_trans
      (le_trans (le_max_left (4 * |A|) (4 * |B|))
        (le_max_right 1 (max (4 * |A|) (4 * |B|)))) ht
  · exact le_trans
      (le_trans (le_max_right (4 * |A|) (4 * |B|))
        (le_max_right 1 (max (4 * |A|) (4 * |B|)))) ht

theorem shortCubic_pos_of_tailThreshold_le
    {A B t : ℝ} (ht : tailThreshold A B ≤ t) :
    0 < shortCubic A B t := by
  have h1 : 1 ≤ t := le_trans (le_max_left 1 (max (4 * |A|) (4 * |B|))) ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one h1
  have hhalf_pos : 0 < (1 / 2 : ℝ) * t ^ 3 := by positivity
  exact lt_of_lt_of_le hhalf_pos (half_cube_le_shortCubic_of_tailThreshold_le ht)

theorem rightIntegrand_pos_of_tailThreshold_le
    {A B t : ℝ} (ht : tailThreshold A B ≤ t) :
    0 < rightIntegrand A B t := by
  unfold rightIntegrand
  exact inv_pos.mpr (sqrt_pos_of_pos (shortCubic_pos_of_tailThreshold_le ht))

theorem sqrt_eq_rpow_half {x : ℝ} (hx : 0 ≤ x) :
    √x = x ^ ((1 : ℝ) / 2) := by
  rw [sqrt_eq_iff_mul_self_eq hx (rpow_nonneg hx _)]
  calc
    x = x ^ (1 : ℝ) := by simp
    _ = x ^ ((1 : ℝ) / 2 + (1 : ℝ) / 2) := by norm_num
    _ = x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) := by
      rw [rpow_add' hx (by norm_num : (1 : ℝ) / 2 + (1 : ℝ) / 2 ≠ 0)]

theorem inv_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    (√x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [sqrt_eq_rpow_half hx, rpow_neg hx]

theorem half_mul_cube_rpow_neg_half {t : ℝ} (ht : 0 < t) :
    ((1 / 2 : ℝ) * t ^ 3) ^ (-(1 / 2 : ℝ)) =
      √2 * t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 ≤ t := ht.le
  have hconst : (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) = √2 := by
    have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
    calc
      (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))
          = ((1 / 2 : ℝ) ^ ((1 / 2 : ℝ)))⁻¹ := by
            rw [rpow_neg hhalf]
      _ = (√(1 / 2 : ℝ))⁻¹ := by
            rw [← sqrt_eq_rpow_half hhalf]
      _ = (√((2 : ℝ)⁻¹))⁻¹ := by norm_num [one_div]
      _ = ((√(2 : ℝ))⁻¹)⁻¹ := by rw [sqrt_inv]
      _ = √2 := by rw [inv_inv]
  have htpart : (t ^ 3 : ℝ) ^ (-(1 / 2 : ℝ)) = t ^ (-(3 / 2 : ℝ)) := by
    calc
      (t ^ 3 : ℝ) ^ (-(1 / 2 : ℝ))
          = (t ^ (3 : ℝ)) ^ (-(1 / 2 : ℝ)) := by norm_num
      _ = t ^ ((3 : ℝ) * (-(1 / 2 : ℝ))) := by
            rw [← rpow_mul ht0]
      _ = t ^ (-(3 / 2 : ℝ)) := by ring_nf
  calc
    ((1 / 2 : ℝ) * t ^ 3) ^ (-(1 / 2 : ℝ))
        = (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (t ^ 3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ)) (pow_nonneg ht0 3)]
    _ = √2 * t ^ (-(3 / 2 : ℝ)) := by
          rw [hconst, htpart]

theorem rightIntegrand_le_const_mul_rpow_tail
    {A B t : ℝ} (ht : tailThreshold A B ≤ t) :
    rightIntegrand A B t ≤ √2 * t ^ (-(3 / 2 : ℝ)) := by
  have h1 : 1 ≤ t := (one_le_tailThreshold A B).trans ht
  have ht_pos : 0 < t := zero_lt_one.trans_le h1
  have hbase_pos : 0 < (1 / 2 : ℝ) * t ^ 3 := by
    exact mul_pos (by norm_num) (pow_pos ht_pos 3)
  have hshort_pos : 0 < shortCubic A B t :=
    shortCubic_pos_of_tailThreshold_le (A := A) (B := B) ht
  calc
    rightIntegrand A B t
        = (shortCubic A B t) ^ (-(1 / 2 : ℝ)) := by
          unfold rightIntegrand
          rw [inv_sqrt_eq_rpow_neg_half hshort_pos.le]
    _ ≤ ((1 / 2 : ℝ) * t ^ 3) ^ (-(1 / 2 : ℝ)) := by
          exact rpow_le_rpow_of_nonpos hbase_pos
            (half_cube_le_shortCubic_of_tailThreshold_le (A := A) (B := B) ht)
            (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    _ = √2 * t ^ (-(3 / 2 : ℝ)) :=
          half_mul_cube_rpow_neg_half ht_pos

theorem rightIntegrand_aestronglyMeasurable_restrict_Ioi (A B R : ℝ) :
    AEStronglyMeasurable (rightIntegrand A B) (volume.restrict (Ioi R)) := by
  unfold rightIntegrand
  have hcont : Continuous (fun x : ℝ => shortCubic A B x) := by
    unfold shortCubic
    fun_prop
  exact (hcont.measurable.sqrt.inv).aestronglyMeasurable

theorem rightIntegrand_integrableOn_Ioi_tailThreshold (A B : ℝ) :
    IntegrableOn (rightIntegrand A B) (Ioi (tailThreshold A B)) := by
  classical
  have hRpos : 0 < tailThreshold A B := tailThreshold_pos A B
  have hmodel :
      IntegrableOn
        (fun t : ℝ => √2 * t ^ (-(3 / 2 : ℝ)))
        (Ioi (tailThreshold A B)) := by
    exact (integrableOn_Ioi_rpow_of_lt
      (show (-(3 / 2 : ℝ)) < -1 by norm_num) hRpos).const_mul _
  refine hmodel.mono' ?hmeas ?hbound
  · exact rightIntegrand_aestronglyMeasurable_restrict_Ioi A B (tailThreshold A B)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hle : tailThreshold A B ≤ t := le_of_lt ht
    have htpos : 0 < t := (tailThreshold_pos A B).trans_le hle
    have hri_nonneg : 0 ≤ rightIntegrand A B t :=
      (rightIntegrand_pos_of_tailThreshold_le (A := A) (B := B) hle).le
    have hmodel_nonneg : 0 ≤ √2 * t ^ (-(3 / 2 : ℝ)) := by
      exact mul_nonneg (sqrt_nonneg _) (rpow_nonneg htpos.le _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hri_nonneg, abs_of_nonneg hmodel_nonneg]
      using rightIntegrand_le_const_mul_rpow_tail (A := A) (B := B) hle

theorem rightIntegrand_integrableOn_Ioi_of_tailThreshold_le
    {A B R : ℝ} (hR : tailThreshold A B ≤ R) :
    IntegrableOn (rightIntegrand A B) (Ioi R) :=
  (rightIntegrand_integrableOn_Ioi_tailThreshold A B).mono (Ioi_subset_Ioi hR) le_rfl

theorem exists_rightIntegrand_integrableOn_Ioi (A B : ℝ) :
    ∃ R : ℝ, IntegrableOn (rightIntegrand A B) (Ioi R) :=
  ⟨tailThreshold A B, rightIntegrand_integrableOn_Ioi_tailThreshold A B⟩

theorem rightIntegrand_aestronglyMeasurable_restrict_Ioo (A B a b : ℝ) :
    AEStronglyMeasurable (rightIntegrand A B) (volume.restrict (Ioo a b)) := by
  unfold rightIntegrand
  have hcont : Continuous (fun x : ℝ => shortCubic A B x) := by
    unfold shortCubic
    fun_prop
  exact (hcont.measurable.sqrt.inv).aestronglyMeasurable

theorem integrableOn_Ioo_sub_rpow_neg_half {e δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => (t - e) ^ (-(1 / 2 : ℝ))) (Ioo e (e + δ)) := by
  have hbase :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 δ :=
    intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : -1 < (-(1 / 2 : ℝ)))
  have hshift :
      IntervalIntegrable (fun t : ℝ => (t - e) ^ (-(1 / 2 : ℝ))) volume (0 + e) (δ + e) := by
    simpa using hbase.comp_sub_right e
  have hshift' :
      IntervalIntegrable (fun t : ℝ => (t - e) ^ (-(1 / 2 : ℝ))) volume e (e + δ) := by
    simpa [zero_add, add_comm, add_left_comm, add_assoc] using hshift
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (show e ≤ e + δ by linarith)).mp hshift'

theorem rightIntegrand_le_root_model_near
    {A B e δ t : ℝ}
    (hderiv : 0 < shortCubicDeriv A B e)
    (hnear : ∀ ⦃u : ℝ⦄, e < u → u < e + δ →
      (shortCubicDeriv A B e / 2) * (u - e) < shortCubic A B u)
    (ht_left : e < t) (ht_right : t < e + δ) :
    rightIntegrand A B t ≤
      (shortCubicDeriv A B e / 2) ^ (-(1 / 2 : ℝ)) *
        (t - e) ^ (-(1 / 2 : ℝ)) := by
  let c : ℝ := shortCubicDeriv A B e / 2
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos hderiv (by norm_num)
  have hxpos : 0 < t - e := sub_pos.mpr ht_left
  have hlinpos : 0 < c * (t - e) := mul_pos hcpos hxpos
  have hlin_lt : c * (t - e) < shortCubic A B t := by
    dsimp [c]
    exact hnear ht_left ht_right
  have hshortpos : 0 < shortCubic A B t := hlinpos.trans hlin_lt
  calc
    rightIntegrand A B t
        = (shortCubic A B t) ^ (-(1 / 2 : ℝ)) := by
          unfold rightIntegrand
          rw [inv_sqrt_eq_rpow_neg_half hshortpos.le]
    _ ≤ (c * (t - e)) ^ (-(1 / 2 : ℝ)) := by
          exact rpow_le_rpow_of_nonpos hlinpos
            (le_of_lt hlin_lt)
            (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    _ = c ^ (-(1 / 2 : ℝ)) * (t - e) ^ (-(1 / 2 : ℝ)) := by
          rw [mul_rpow hcpos.le hxpos.le]

theorem rightIntegrand_integrableOn_near_root
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    ∃ δ > 0, IntegrableOn (rightIntegrand A B) (Ioo e (e + δ)) := by
  classical
  rcases exists_shortCubic_lower_bound_near_root
      (A := A) (B := B) (e := e) hroot hderiv with
    ⟨δ0, hδ0, hnear⟩
  let δ : ℝ := min δ0 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ0 zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  let c : ℝ := shortCubicDeriv A B e / 2
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos hderiv (by norm_num)
  have hmodel :
      IntegrableOn
        (fun t : ℝ => c ^ (-(1 / 2 : ℝ)) * (t - e) ^ (-(1 / 2 : ℝ)))
        (Ioo e (e + δ)) := by
    exact (integrableOn_Ioo_sub_rpow_neg_half (e := e) hδ).const_mul _
  refine hmodel.mono' ?hmeas ?hbound
  · exact rightIntegrand_aestronglyMeasurable_restrict_Ioo A B e (e + δ)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht_left : e < t := ht.1
    have ht_delta : t < e + δ := ht.2
    have hδ_le_δ0 : δ ≤ δ0 := by
      dsimp [δ]
      exact min_le_left _ _
    have ht_right0 : t < e + δ0 := by linarith
    have hle := rightIntegrand_le_root_model_near
      (A := A) (B := B) (e := e) (δ := δ0) (t := t)
      hderiv hnear ht_left ht_right0
    have hxpos : 0 < t - e := sub_pos.mpr ht_left
    have hri_nonneg : 0 ≤ rightIntegrand A B t := by
      unfold rightIntegrand
      exact inv_nonneg.mpr (sqrt_nonneg _)
    have hmodel_nonneg :
        0 ≤ c ^ (-(1 / 2 : ℝ)) * (t - e) ^ (-(1 / 2 : ℝ)) := by
      exact mul_nonneg (rpow_nonneg hcpos.le _) (rpow_nonneg hxpos.le _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hri_nonneg, abs_of_nonneg hmodel_nonneg, c]
      using hle

theorem shortCubic_nonneg_of_sq_eq
    {A B x y : ℝ} (hxy : y ^ 2 = shortCubic A B x) :
    0 ≤ shortCubic A B x := by
  rw [← hxy]
  exact sq_nonneg y

theorem y_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_shortCubic
    {A B x y : ℝ} (hxy : y ^ 2 = shortCubic A B x) :
    y = √(shortCubic A B x) ∨ y = -√(shortCubic A B x) := by
  have hnonneg : 0 ≤ shortCubic A B x := shortCubic_nonneg_of_sq_eq hxy
  have hsq : y ^ 2 = (√(shortCubic A B x)) ^ 2 := by
    rw [hxy, sq_sqrt hnonneg]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

theorem shortW_y_eq_sqrt_or_eq_neg_sqrt
    {A B x y : ℝ}
    (h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y) :
    y = √(shortCubic A B x) ∨ y = -√(shortCubic A B x) :=
  y_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_shortCubic (shortW_equation_iff.mp h.1)

theorem rightIntegrand_pos_of_right
    {A B e x : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    0 < rightIntegrand A B x := by
  unfold rightIntegrand
  exact inv_pos.mpr (sqrt_pos_of_pos (hposRight hx))

theorem rightIntegrand_ne_zero_of_right
    {A B e x : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    rightIntegrand A B x ≠ 0 :=
  (rightIntegrand_pos_of_right hposRight hx).ne'

theorem rightIntegrand_pos_of_gt_root
    {A B r s e x : ℝ}
    (hfactor : ∀ u : ℝ, shortCubic A B u = (u - r) * (u - s) * (u - e))
    (hr : r < e) (hs : s < e) (hx : e < x) :
    0 < rightIntegrand A B x := by
  unfold rightIntegrand
  exact inv_pos.mpr
    (sqrt_pos_of_pos (shortCubic_pos_right_of_ordered_roots hfactor hr hs hx))

theorem rightIntegrand_nonneg (A B x : ℝ) :
    0 ≤ rightIntegrand A B x := by
  unfold rightIntegrand
  exact inv_nonneg.mpr (sqrt_nonneg _)

theorem shortCubic_hasDerivAt (A B x : ℝ) :
    HasDerivAt (shortCubic A B) (shortCubicDeriv A B x) x := by
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x)
  have h2 : HasDerivAt (fun u : ℝ => A * u ^ 2) (2 * A * x) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.const_mul A (hasDerivAt_pow 2 x))
  have h1 : HasDerivAt (fun u : ℝ => B * u) B x := by
    simpa using (HasDerivAt.const_mul B (hasDerivAt_id x))
  rw [show shortCubic A B =
      (fun u : ℝ => u ^ 3) + ((fun u : ℝ => A * u ^ 2) + fun u : ℝ => B * u) by
    funext u
    simp [shortCubic, add_assoc]]
  exact (h3.add (h2.add h1)).congr_deriv (by
    simp [shortCubicDeriv]
    ring)

theorem sqrt_shortCubic_hasDerivAt_of_pos
    {A B x : ℝ}
    (hpos : 0 < shortCubic A B x) :
    HasDerivAt (fun u : ℝ => √(shortCubic A B u))
      (shortCubicDeriv A B x / (2 * √(shortCubic A B x))) x := by
  simpa using (shortCubic_hasDerivAt A B x).sqrt hpos.ne'

theorem rightIntegrand_continuousOn_Ioi_of_right
    {A B e : ℝ}
    (hposRight : ∀ ⦃x : ℝ⦄, e < x → 0 < shortCubic A B x) :
    ContinuousOn (rightIntegrand A B) (Ioi e) := by
  unfold rightIntegrand
  apply ContinuousOn.inv₀
  · have hpoly : Continuous (fun t : ℝ => shortCubic A B t) := by
      unfold shortCubic
      fun_prop
    exact (continuous_sqrt.comp hpoly).continuousOn
  · intro x hx
    exact (sqrt_pos_of_pos (hposRight hx)).ne'

theorem rightIntegrand_continuousOn_Ioi_of_ordered_roots
    {A B r s e : ℝ}
    (hfactor : ∀ u : ℝ, shortCubic A B u = (u - r) * (u - s) * (u - e))
    (hr : r < e) (hs : s < e) :
    ContinuousOn (rightIntegrand A B) (Ioi e) := by
  unfold rightIntegrand
  apply ContinuousOn.inv₀
  · have hpoly : Continuous (fun t : ℝ => shortCubic A B t) := by
      unfold shortCubic
      fun_prop
    exact (continuous_sqrt.comp hpoly).continuousOn
  · intro x hx
    exact (sqrt_pos_of_pos
      (shortCubic_pos_right_of_ordered_roots hfactor hr hs hx)).ne'

theorem rightIntegrand_continuousAt_of_gt_root
    {A B r s e x : ℝ}
    (hfactor : ∀ u : ℝ, shortCubic A B u = (u - r) * (u - s) * (u - e))
    (hr : r < e) (hs : s < e) (hx : e < x) :
    ContinuousAt (rightIntegrand A B) x :=
  (rightIntegrand_continuousOn_Ioi_of_ordered_roots hfactor hr hs).continuousAt
    (IsOpen.mem_nhds isOpen_Ioi hx)

theorem rightIntegrand_continuousAt_of_right
    {A B e x : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    ContinuousAt (rightIntegrand A B) x :=
  (rightIntegrand_continuousOn_Ioi_of_right hposRight).continuousAt
    (IsOpen.mem_nhds isOpen_Ioi hx)

theorem rightIntegrand_intervalIntegrable_of_ordered_roots_of_le
    {A B r s e a b : ℝ}
    (hfactor : ∀ u : ℝ, shortCubic A B u = (u - r) * (u - s) * (u - e))
    (hr : r < e) (hs : s < e) (ha : e < a) (hab : a ≤ b) :
    IntervalIntegrable (rightIntegrand A B) volume a b := by
  have hcont_Icc :
      ContinuousOn (rightIntegrand A B) (Icc a b) :=
    (rightIntegrand_continuousOn_Ioi_of_ordered_roots hfactor hr hs).mono
      (by
        intro x hx
        exact lt_of_lt_of_le ha hx.1)
  exact hcont_Icc.intervalIntegrable_of_Icc hab

theorem rightIntegrand_intervalIntegrable_of_right_of_le
    {A B e a b : ℝ}
    (hposRight : ∀ ⦃x : ℝ⦄, e < x → 0 < shortCubic A B x)
    (ha : e < a) (hab : a ≤ b) :
    IntervalIntegrable (rightIntegrand A B) volume a b := by
  have hcont_Icc :
      ContinuousOn (rightIntegrand A B) (Icc a b) :=
    (rightIntegrand_continuousOn_Ioi_of_right hposRight).mono
      (by
        intro x hx
        exact lt_of_lt_of_le ha hx.1)
  exact hcont_Icc.intervalIntegrable_of_Icc hab

theorem rightIntegrand_integrableOn_Ioi_root
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃x : ℝ⦄, e < x → 0 < shortCubic A B x) :
    IntegrableOn (rightIntegrand A B) (Ioi e) := by
  rcases rightIntegrand_integrableOn_near_root
      (A := A) (B := B) (e := e) hroot hderiv with
    ⟨δ, hδ, hnearInt⟩
  let a : ℝ := e + δ / 2
  let R : ℝ := max a (tailThreshold A B)
  have ha : e < a := by
    dsimp [a]
    linarith
  have haδ : a < e + δ := by
    dsimp [a]
    linarith
  have haR : a ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have htailR : tailThreshold A B ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  have hfinite : IntervalIntegrable (rightIntegrand A B) volume a R :=
    rightIntegrand_intervalIntegrable_of_right_of_le hposRight ha haR
  have hmiddle : IntegrableOn (rightIntegrand A B) (Ioc a R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haR).1 hfinite
  have htail : IntegrableOn (rightIntegrand A B) (Ioi R) :=
    rightIntegrand_integrableOn_Ioi_of_tailThreshold_le htailR
  have hIoi_a : IntegrableOn (rightIntegrand A B) (Ioi a) :=
    (Ioc_union_Ioi_eq_Ioi haR) ▸ hmiddle.union htail
  have hcover : Ioo e (e + δ) ∪ Ioi a = Ioi e := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact lt_trans ha hx
    · intro hx
      by_cases hx_upper : x < e + δ
      · exact Or.inl ⟨hx, hx_upper⟩
      · have hx_ge : e + δ ≤ x := le_of_not_gt hx_upper
        exact Or.inr (lt_of_lt_of_le haδ hx_ge)
  simpa [hcover] using hnearInt.union hIoi_a

theorem halfPeriod_pos
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃x : ℝ⦄, e < x → 0 < shortCubic A B x) :
    0 < halfPeriod A B e := by
  have hint : IntegrableOn (rightIntegrand A B) (Ioi e) :=
    rightIntegrand_integrableOn_Ioi_root hroot hderiv hposRight
  have hnonneg_ae : 0 ≤ᵐ[volume.restrict (Ioi e)] rightIntegrand A B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (rightIntegrand_pos_of_right hposRight hx).le
  have hsupport_pos :
      0 < volume (Function.support (rightIntegrand A B) ∩ Ioi e) := by
    have hsub : Ioo e (e + 1) ⊆ Function.support (rightIntegrand A B) ∩ Ioi e := by
      intro x hx
      constructor
      · rw [Function.mem_support]
        exact (rightIntegrand_pos_of_right hposRight hx.1).ne'
      · exact hx.1
    have hIoo_pos : 0 < volume (Ioo e (e + 1)) :=
      (Measure.measure_Ioo_pos volume).2 (by linarith)
    exact lt_of_lt_of_le hIoo_pos (measure_mono hsub)
  have hpos :
      0 < ∫ t in Ioi e, rightIntegrand A B t :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg_ae hint).2 hsupport_pos
  simpa [halfPeriod, sigma] using hpos

theorem sigma_pos_of_right
    {A B e x : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    0 < sigma A B x := by
  have hint_e : IntegrableOn (rightIntegrand A B) (Ioi e) :=
    rightIntegrand_integrableOn_Ioi_root hroot hderiv hposRight
  have hint_x : IntegrableOn (rightIntegrand A B) (Ioi x) :=
    hint_e.mono_set (Ioi_subset_Ioi hx.le)
  have hnonneg_ae : 0 ≤ᵐ[volume.restrict (Ioi x)] rightIntegrand A B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (rightIntegrand_pos_of_right hposRight (lt_trans hx hy)).le
  have hsupport_pos :
      0 < volume (Function.support (rightIntegrand A B) ∩ Ioi x) := by
    have hsub : Ioo x (x + 1) ⊆ Function.support (rightIntegrand A B) ∩ Ioi x := by
      intro y hy
      constructor
      · rw [Function.mem_support]
        exact (rightIntegrand_pos_of_right hposRight (lt_trans hx hy.1)).ne'
      · exact hy.1
    have hIoo_pos : 0 < volume (Ioo x (x + 1)) :=
      (Measure.measure_Ioo_pos volume).2 (by linarith)
    exact lt_of_lt_of_le hIoo_pos (measure_mono hsub)
  have hpos :
      0 < ∫ t in Ioi x, rightIntegrand A B t :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg_ae hint_x).2 hsupport_pos
  simpa [sigma] using hpos

theorem sigma_lt_halfPeriod_of_right
    {A B e x : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    sigma A B x < halfPeriod A B e := by
  have hint_e : IntegrableOn (rightIntegrand A B) (Ioi e) :=
    rightIntegrand_integrableOn_Ioi_root hroot hderiv hposRight
  have hint_x : IntegrableOn (rightIntegrand A B) (Ioi x) :=
    hint_e.mono_set (Ioi_subset_Ioi hx.le)
  have hfi : IntervalIntegrable (rightIntegrand A B) volume e x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact hint_e.mono_set Ioc_subset_Ioi_self
  have hinterval_pos : 0 < ∫ t in e..x, rightIntegrand A B t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hfi
      (fun y hy => rightIntegrand_pos_of_right hposRight hy.1) hx
  have hsum :=
    intervalIntegral.integral_interval_add_Ioi
      (a := e) (b := x) (f := rightIntegrand A B) hint_e hint_x
  have hlt :
      ∫ t in Ioi x, rightIntegrand A B t <
        ∫ t in Ioi e, rightIntegrand A B t := by
    linarith
  simpa [sigma, halfPeriod] using hlt

theorem strictAntiOn_sigma_Ioi
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    StrictAntiOn (sigma A B) (Ioi e) := by
  intro x hx y hy hxy
  have hint_e : IntegrableOn (rightIntegrand A B) (Ioi e) :=
    rightIntegrand_integrableOn_Ioi_root hroot hderiv hposRight
  have hint_x : IntegrableOn (rightIntegrand A B) (Ioi x) :=
    hint_e.mono_set (Ioi_subset_Ioi hx.le)
  have hint_y : IntegrableOn (rightIntegrand A B) (Ioi y) :=
    hint_e.mono_set (Ioi_subset_Ioi hy.le)
  have hfi : IntervalIntegrable (rightIntegrand A B) volume x y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy.le]
    exact hint_x.mono_set Ioc_subset_Ioi_self
  have hinterval_pos : 0 < ∫ t in x..y, rightIntegrand A B t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hfi
      (fun z hz => rightIntegrand_pos_of_right hposRight (lt_trans hx hz.1)) hxy
  have hsum :=
    intervalIntegral.integral_interval_add_Ioi
      (a := x) (b := y) (f := rightIntegrand A B) hint_x hint_y
  have hlt :
      ∫ t in Ioi y, rightIntegrand A B t <
        ∫ t in Ioi x, rightIntegrand A B t := by
    linarith
  simpa [sigma] using hlt

theorem sigma_hasDerivAt_of_right
    {A B e x : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    HasDerivAt (sigma A B) (-(rightIntegrand A B x)) x := by
  let b : ℝ := x + 1
  have hxb : x ≤ b := by
    dsimp [b]
    linarith
  have hxb_lt : x < b := by
    dsimp [b]
    linarith
  have heb : e < b := lt_trans hx hxb_lt
  have hint_e : IntegrableOn (rightIntegrand A B) (Ioi e) :=
    rightIntegrand_integrableOn_Ioi_root hroot hderiv hposRight
  have hfi : IntervalIntegrable (rightIntegrand A B) volume x b :=
    rightIntegrand_intervalIntegrable_of_right_of_le hposRight hx hxb
  have hcont : ContinuousAt (rightIntegrand A B) x :=
    rightIntegrand_continuousAt_of_right hposRight hx
  have hderiv_interval :
      HasDerivAt (fun u : ℝ => ∫ t in u..b, rightIntegrand A B t)
        (-(rightIntegrand A B x)) x :=
    intervalIntegral.integral_hasDerivAt_left hfi
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        (rightIntegrand_continuousOn_Ioi_of_right hposRight) x hx) hcont
  have hderiv_tail :
      HasDerivAt
        (fun u : ℝ =>
          (∫ t in u..b, rightIntegrand A B t) +
            ∫ t in Ioi b, rightIntegrand A B t)
        (-(rightIntegrand A B x)) x :=
    hderiv_interval.add_const _
  have hev :
      (fun u : ℝ =>
          (∫ t in u..b, rightIntegrand A B t) +
            ∫ t in Ioi b, rightIntegrand A B t) =ᶠ[𝓝 x]
        sigma A B := by
    filter_upwards [Ioo_mem_nhds hx hxb_lt] with u hu
    have heu : e < u := hu.1
    have hint_u : IntegrableOn (rightIntegrand A B) (Ioi u) :=
      hint_e.mono_set (Ioi_subset_Ioi heu.le)
    have hint_b : IntegrableOn (rightIntegrand A B) (Ioi b) :=
      hint_e.mono_set (Ioi_subset_Ioi heb.le)
    have hsum :=
      intervalIntegral.integral_interval_add_Ioi
        (a := u) (b := b) (f := rightIntegrand A B) hint_u hint_b
    simpa [sigma] using hsum
  exact hderiv_tail.congr_of_eventuallyEq hev.symm

theorem neg_sigma_hasDerivAt_of_right
    {A B e x : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    HasDerivAt (fun u : ℝ => -sigma A B u) (rightIntegrand A B x) x := by
  change HasDerivAt (-sigma A B) (rightIntegrand A B x) x
  simpa using (sigma_hasDerivAt_of_right hroot hderiv hposRight hx).neg

theorem tendsto_sigma_atTop
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (sigma A B) atTop (𝓝 0) := by
  have _hint : IntegrableOn (rightIntegrand A B) (Ioi e) :=
    rightIntegrand_integrableOn_Ioi_root hroot hderiv hposRight
  change Tendsto
    (fun x : ℝ => ∫ t in Ioi x, rightIntegrand A B t) atTop (𝓝 0)
  exact tendsto_integral_Ioi_zero
    (f := rightIntegrand A B) (μ := volume)
    (b := fun x : ℝ => x) (l := atTop) tendsto_id

theorem tendsto_sigma_nhdsGT_root
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (sigma A B) (𝓝[>] e) (𝓝 (halfPeriod A B e)) := by
  have hint_e : IntegrableOn (rightIntegrand A B) (Ioi e) :=
    rightIntegrand_integrableOn_Ioi_root hroot hderiv hposRight
  let primitive : ℝ → ℝ := fun x => ∫ t in e..x, rightIntegrand A B t
  have hprimitive_ioc : ContinuousWithinAt primitive (Icc e (e + 1)) e := by
    dsimp [primitive]
    refine intervalIntegral.continuousWithinAt_primitive
      (μ := volume) (f := rightIntegrand A B) (a := e) (b₀ := e)
      (b₁ := e) (b₂ := e + 1) (measure_singleton e) ?_
    rw [min_self, max_eq_right (by linarith : e ≤ e + 1)]
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : e ≤ e + 1)]
    exact hint_e.mono_set Ioc_subset_Ioi_self
  have hIcc_mem : Icc e (e + 1) ∈ 𝓝[>] e :=
    mem_of_superset (Ioo_mem_nhdsGT (by linarith : e < e + 1)) Ioo_subset_Icc_self
  have hprimitive : Tendsto primitive (𝓝[>] e) (𝓝 0) := by
    have hcont : ContinuousWithinAt primitive (Ioi e) e :=
      hprimitive_ioc.mono_of_mem_nhdsWithin hIcc_mem
    simpa [ContinuousWithinAt, primitive] using hcont
  have heq :
      (fun x : ℝ => sigma A B x) =ᶠ[𝓝[>] e]
        fun x : ℝ => halfPeriod A B e - primitive x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hint_x : IntegrableOn (rightIntegrand A B) (Ioi x) :=
      hint_e.mono_set (Ioi_subset_Ioi hx.le)
    have hsum := intervalIntegral.integral_interval_add_Ioi
      (a := e) (b := x) (f := rightIntegrand A B) hint_e hint_x
    dsimp [sigma, halfPeriod, primitive]
    linarith
  refine Tendsto.congr' heq.symm ?_
  simpa using Tendsto.const_sub (halfPeriod A B e) hprimitive

end

end MazurProof.RealTopology
