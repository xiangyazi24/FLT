ANSWER Q3554 e2f8efde

# Q3554: tail comparison API for `rightIntegrand`

## Short verdict

Use an `rpow` bridge rather than fighting directly with inverse square roots. The pointwise comparison should be proved as

```lean
rightIntegrand A B t
  = (shortCubic A B t) ^ (-(1 / 2 : ℝ))
  ≤ ((1 / 2 : ℝ) * t ^ 3) ^ (-(1 / 2 : ℝ))
  = Real.sqrt 2 * t ^ (-(3 / 2 : ℝ))
```

The key Mathlib APIs are:

```lean
Real.sqrt_eq_iff_mul_self_eq
Real.rpow_add'
Real.rpow_neg
Real.rpow_le_rpow_of_nonpos
Real.mul_rpow
Real.rpow_mul
integrableOn_Ioi_rpow_of_lt
IntegrableOn.const_mul
IntegrableOn.mono'
ae_restrict_mem measurableSet_Ioi
```

A direct sqrt proof is also possible via `Real.sqrt_le_sqrt` followed by `inv_le_inv₀`, but the `rpow` route gives the final comparison function in exactly the form needed by `integrableOn_Ioi_rpow_of_lt`.

## Local helper lemmas to add first

```lean
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import FLT.Assumptions.MazurProof.RealTopologyS4

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace MazurProof.RealTopology

lemma one_le_tailThreshold (A B : ℝ) :
    1 ≤ tailThreshold A B := by
  unfold tailThreshold
  exact le_max_left _ _

lemma tailThreshold_pos (A B : ℝ) :
    0 < tailThreshold A B :=
  zero_lt_one.trans_le (one_le_tailThreshold A B)

/-- Bridge from `sqrt` to `rpow`. This is the first small lemma to close. -/
lemma sqrt_eq_rpow_half {x : ℝ} (hx : 0 ≤ x) :
    √x = x ^ ((1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_iff_mul_self_eq hx (Real.rpow_nonneg hx _)]
  calc
    x = x ^ (1 : ℝ) := by simp
    _ = x ^ ((1 : ℝ) / 2 + (1 : ℝ) / 2) := by norm_num
    _ = x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_add' hx]
      norm_num

lemma inv_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    (√x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [sqrt_eq_rpow_half hx, Real.rpow_neg hx]

/-- Algebraic normalization of the model tail. This is the second small lemma to close. -/
lemma half_mul_cube_rpow_neg_half {t : ℝ} (ht : 0 < t) :
    ((1 / 2 : ℝ) * t ^ 3) ^ (-(1 / 2 : ℝ)) =
      Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 ≤ t := ht.le
  have hconst : (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 := by
    have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
    calc
      (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))
          = ((1 / 2 : ℝ) ^ ((1 / 2 : ℝ)))⁻¹ := by
            rw [Real.rpow_neg hhalf]
      _ = (√(1 / 2 : ℝ))⁻¹ := by
            rw [← sqrt_eq_rpow_half hhalf]
      _ = (√((2 : ℝ)⁻¹))⁻¹ := by norm_num [one_div]
      _ = ((√(2 : ℝ))⁻¹)⁻¹ := by rw [Real.sqrt_inv]
      _ = Real.sqrt 2 := by rw [inv_inv]
  have htpart : (t ^ 3 : ℝ) ^ (-(1 / 2 : ℝ)) = t ^ (-(3 / 2 : ℝ)) := by
    calc
      (t ^ 3 : ℝ) ^ (-(1 / 2 : ℝ))
          = (t ^ (3 : ℝ)) ^ (-(1 / 2 : ℝ)) := by norm_num
      _ = t ^ ((3 : ℝ) * (-(1 / 2 : ℝ))) := by
            rw [← Real.rpow_mul ht0]
      _ = t ^ (-(3 / 2 : ℝ)) := by ring_nf
  calc
    ((1 / 2 : ℝ) * t ^ 3) ^ (-(1 / 2 : ℝ))
        = (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (t ^ 3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ)) (pow_nonneg ht0 3)]
    _ = Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
          rw [hconst, htpart]

end MazurProof.RealTopology
```

If anything in the block above needs adjustment in your pinned Mathlib, the most likely fragile line is the `rw [Real.rpow_add' hx]` call in `sqrt_eq_rpow_half`; in that case, explicitly supply the nonzero side condition:

```lean
rw [Real.rpow_add' hx (by norm_num : (1 : ℝ) / 2 + (1 : ℝ) / 2 ≠ 0)]
```

## Pointwise comparison theorem

```lean
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import FLT.Assumptions.MazurProof.RealTopologyS4

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace MazurProof.RealTopology

theorem rightIntegrand_le_const_mul_rpow_tail
    {A B t : ℝ} (ht : tailThreshold A B ≤ t) :
    rightIntegrand A B t ≤ Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
  have ht1 : 1 ≤ t := (one_le_tailThreshold A B).trans ht
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hbasepos : 0 < (1 / 2 : ℝ) * t ^ 3 := by
    exact mul_pos (by norm_num) (pow_pos htpos 3)
  have hshortpos : 0 < shortCubic A B t :=
    shortCubic_pos_of_tailThreshold_le (A := A) (B := B) ht
  calc
    rightIntegrand A B t
        = (shortCubic A B t) ^ (-(1 / 2 : ℝ)) := by
            unfold rightIntegrand
            rw [inv_sqrt_eq_rpow_neg_half hshortpos.le]
    _ ≤ ((1 / 2 : ℝ) * t ^ 3) ^ (-(1 / 2 : ℝ)) := by
            exact Real.rpow_le_rpow_of_nonpos hbasepos
              (half_cube_le_shortCubic_of_tailThreshold_le (A := A) (B := B) ht)
              (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    _ = Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) :=
            half_mul_cube_rpow_neg_half htpos

end MazurProof.RealTopology
```

This avoids proving a separate inequality for `√((1/2) * t^3)`. If you prefer the direct sqrt route, the exact mathematical step is:

```lean
have hsqrt_le :
    √((1 / 2 : ℝ) * t ^ 3) ≤ √(shortCubic A B t) :=
  Real.sqrt_le_sqrt (half_cube_le_shortCubic_of_tailThreshold_le (A := A) (B := B) ht)

-- Then use `inv_le_inv₀` with positivity of `√((1/2) * t^3)`.
```

But for the final integrability theorem, the `rpow` route is cleaner.

## Tail integrability theorem

```lean
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import FLT.Assumptions.MazurProof.RealTopologyS4

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace MazurProof.RealTopology

theorem rightIntegrand_integrableOn_Ioi_tailThreshold (A B : ℝ) :
    IntegrableOn (rightIntegrand A B) (Ioi (tailThreshold A B)) := by
  classical
  have hRpos : 0 < tailThreshold A B := tailThreshold_pos A B
  have hmodel :
      IntegrableOn
        (fun t : ℝ => Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)))
        (Ioi (tailThreshold A B)) := by
    exact (integrableOn_Ioi_rpow_of_lt
      (show (-(3 / 2 : ℝ)) < -1 by norm_num) hRpos).const_mul _
  refine hmodel.mono' ?hmeas ?hbound
  · unfold rightIntegrand
    -- `sqrt` is measurable and inversion is measurable; `fun_prop` usually closes this.
    exact (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => (√(shortCubic A B x))⁻¹)
      (volume.restrict (Ioi (tailThreshold A B))))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hle : tailThreshold A B ≤ t := le_of_lt ht
    have htpos : 0 < t := (tailThreshold_pos A B).trans_le hle
    have hri_nonneg : 0 ≤ rightIntegrand A B t :=
      (rightIntegrand_pos_of_tailThreshold_le (A := A) (B := B) hle).le
    have hmodel_nonneg : 0 ≤ Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg htpos.le _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hri_nonneg, abs_of_nonneg hmodel_nonneg]
      using rightIntegrand_le_const_mul_rpow_tail (A := A) (B := B) hle

end MazurProof.RealTopology
```

If `fun_prop` does not close the measurability subgoal, split it into a named lemma first:

```lean
theorem rightIntegrand_aestronglyMeasurable_restrict_Ioi (A B R : ℝ) :
    AEStronglyMeasurable (rightIntegrand A B) (volume.restrict (Ioi R)) := by
  unfold rightIntegrand
  exact (by fun_prop : AEStronglyMeasurable
    (fun x : ℝ => (√(shortCubic A B x))⁻¹) (volume.restrict (Ioi R)))
```

Then use that lemma as `?hmeas` in `IntegrableOn.mono'`.

## Recommended next Lean task

First close `sqrt_eq_rpow_half` and `inv_sqrt_eq_rpow_neg_half`. They are independent of the elliptic cubic and confirm the exact `rpow` API in your pinned build. Then close `half_mul_cube_rpow_neg_half`; after those, the pointwise comparison is a short `calc`, and the final integrability theorem is a standard `IntegrableOn.mono'` domination proof.
