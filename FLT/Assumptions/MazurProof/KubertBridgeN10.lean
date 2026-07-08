import Mathlib
import FLT.Assumptions.MazurProof.DescentBridgeDefs
import scratch.TateZ2xZ10Reduction

/-!
# Kubert bridge: Z/2Z × Z/10Z torsion → point on w² = u³ + u² - u

Reduces the theorem `Z2xZ10_gives_non_degenerate_E20_point` from the Tate
normal-form bridge to the Kubert square condition, with the final polynomial
identities proved by `ring`.

## The cyclic-10 Kubert family

For parameter `t ∈ ℚ`, define:
* `F₁₀(t) = 1 + 2t - 5t² - 5t⁴ - 2t⁵ + t⁶`
* `A₁₀(t) = -2F₁₀(t)`
* `B₁₀(t) = (t²-1)⁵(t²-4t-1)`
* `E₁₀(t) : y² = x³ + A₁₀(t)x² + B₁₀(t)x`

The discriminant of E₁₀(t) vanishes exactly when `t ∈ {-1, 0, 1}` or
`t²+t-1 = 0` or `t²-4t-1 = 0` (the latter two are irrational).

## Key identity (PROVED by ring)

`A₁₀(t)² - 4B₁₀(t) = 256t⁵(t²+t-1)`

If this is a square `s²`, then `w = s/(16t²)` satisfies `w² = t³+t²-t`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN10

noncomputable section

def F10 (t : ℚ) : ℚ :=
  1 + 2 * t - 5 * t ^ 2 - 5 * t ^ 4 - 2 * t ^ 5 + t ^ 6

def A10 (t : ℚ) : ℚ := -2 * F10 t

def B10 (t : ℚ) : ℚ := (t ^ 2 - 1) ^ 5 * (t ^ 2 - 4 * t - 1)

def Delta10 (t : ℚ) : ℚ :=
  4096 * t ^ 5 * (t ^ 2 + t - 1) * (t ^ 2 - 1) ^ 10 * (t ^ 2 - 4 * t - 1) ^ 2

/-! ## Polynomial identities — all proved by ring/norm_num -/

theorem quad_disc_identity (t : ℚ) :
    A10 t ^ 2 - 4 * B10 t = 256 * t ^ 5 * (t ^ 2 + t - 1) := by
  unfold A10 B10 F10; ring

theorem delta10_zero_at_neg1 : Delta10 (-1) = 0 := by norm_num [Delta10]
theorem delta10_zero_at_0 : Delta10 0 = 0 := by norm_num [Delta10]
theorem delta10_zero_at_1 : Delta10 1 = 0 := by norm_num [Delta10]

theorem delta10_zero_of_degenerate {t : ℚ}
    (h : t = -1 ∨ t = 0 ∨ t = 1) : Delta10 t = 0 := by
  rcases h with rfl | rfl | rfl
  · exact delta10_zero_at_neg1
  · exact delta10_zero_at_0
  · exact delta10_zero_at_1

/-! ## Square condition → obstruction curve point -/

theorem obstruction_point_of_square {t s : ℚ} (ht : t ≠ 0)
    (hs : s ^ 2 = A10 t ^ 2 - 4 * B10 t) :
    ∃ w : ℚ, w ^ 2 = t ^ 3 + t ^ 2 - t := by
  refine ⟨s / (16 * t ^ 2), ?_⟩
  have h16t2 : (16 : ℚ) * t ^ 2 ≠ 0 := by positivity
  have := quad_disc_identity t
  field_simp
  nlinarith [this, hs]

theorem non_degenerate_of_square {t s : ℚ}
    (hΔ : Delta10 t ≠ 0)
    (hs : s ^ 2 = A10 t ^ 2 - 4 * B10 t) :
    ∃ u w : ℚ, E20AffineEquation u w ∧ ¬ E20DegenerateParameter u := by
  have ht : t ≠ 0 := by
    intro h; exact hΔ (by rw [h]; exact delta10_zero_at_0)
  have hnotdeg : ¬ E20DegenerateParameter t := by
    intro h; exact hΔ (delta10_zero_of_degenerate h)
  obtain ⟨w, hw⟩ := obstruction_point_of_square ht hs
  exact ⟨t, w, by unfold E20AffineEquation; linarith, hnotdeg⟩

/-! ## Obstruction curve point → Kubert square condition -/

private theorem rat_sq_ne_five (r : ℚ) : r ^ 2 ≠ 5 := by
  intro h
  have hsq : IsSquare (5 : ℚ) := ⟨r, by simpa [pow_two] using h.symm⟩
  have hnot : ¬ IsSquare (5 : ℚ) := by norm_num
  exact hnot hsq

private theorem t_sq_add_t_sub_one_ne_zero (t : ℚ) : t ^ 2 + t - 1 ≠ 0 := by
  intro h
  exact rat_sq_ne_five (2 * t + 1) (by nlinarith)

private theorem t_sq_sub_four_mul_t_sub_one_ne_zero (t : ℚ) :
    t ^ 2 - 4 * t - 1 ≠ 0 := by
  intro h
  exact rat_sq_ne_five (t - 2) (by nlinarith)

private theorem t_sq_sub_one_ne_zero_of_nondegenerate {t : ℚ}
    (hndeg : ¬ E20DegenerateParameter t) : t ^ 2 - 1 ≠ 0 := by
  intro h
  have hprod : (t - 1) * (t + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with ht1 | htneg1
  · exact hndeg (by
      unfold E20DegenerateParameter
      right; right
      linarith)
  · exact hndeg (by
      unfold E20DegenerateParameter
      left
      linarith)

theorem delta10_ne_zero_of_nondegenerate {t : ℚ}
    (hndeg : ¬ E20DegenerateParameter t) : Delta10 t ≠ 0 := by
  have ht0 : t ≠ 0 := by
    intro ht
    exact hndeg (by
      unfold E20DegenerateParameter
      right; left
      exact ht)
  unfold Delta10
  repeat' apply mul_ne_zero
  · norm_num
  · exact pow_ne_zero 5 ht0
  · exact t_sq_add_t_sub_one_ne_zero t
  · exact pow_ne_zero 10 (t_sq_sub_one_ne_zero_of_nondegenerate hndeg)
  · exact pow_ne_zero 2 (t_sq_sub_four_mul_t_sub_one_ne_zero t)

theorem square_condition_of_obstruction_point {t w : ℚ}
    (hcurve : E20AffineEquation t w)
    (hndeg : ¬ E20DegenerateParameter t) :
    ∃ s : ℚ, Delta10 t ≠ 0 ∧ s ^ 2 = A10 t ^ 2 - 4 * B10 t := by
  refine ⟨16 * t ^ 2 * w, delta10_ne_zero_of_nondegenerate hndeg, ?_⟩
  unfold E20AffineEquation at hcurve
  calc
    (16 * t ^ 2 * w) ^ 2 = 256 * t ^ 4 * w ^ 2 := by ring
    _ = 256 * t ^ 4 * (t ^ 3 + t ^ 2 - t) := by rw [hcurve]
    _ = 256 * t ^ 5 * (t ^ 2 + t - 1) := by ring
    _ = A10 t ^ 2 - 4 * B10 t := (quad_disc_identity t).symm

/-- If `E/ℚ` has a subgroup isomorphic to `ℤ/2ℤ × ℤ/10ℤ`, then `E` arises
from the cyclic-10 Kubert family with non-degenerate parameter, making the
quadratic factor of the 2-torsion polynomial have square discriminant. -/
theorem kubert_C10_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta10 t ≠ 0 ∧ s ^ 2 = A10 t ^ 2 - 4 * B10 t := by
  obtain ⟨t, w, hcurve, hndeg⟩ :=
    Scratch.TateZ2xZ10Reduction.Z2xZ10_gives_non_degenerate_E20_point E hE
  obtain ⟨s, hΔ, hs⟩ := square_condition_of_obstruction_point hcurve hndeg
  exact ⟨t, s, hΔ, hs⟩

/-- Discharge `Z2xZ10_gives_non_degenerate_E20_point` from the Kubert bridge. -/
theorem bridge_N10 (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E20AffineEquation u w ∧ ¬ E20DegenerateParameter u := by
  obtain ⟨t, s, hΔ, hs⟩ := kubert_C10_square E hE
  exact non_degenerate_of_square hΔ hs

end

end MazurProof.KubertBridgeN10
