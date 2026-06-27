import Mathlib
import FLT.Assumptions.MazurProof.DescentBridge

/-!
# Kubert bridge: Z/2Z × Z/10Z torsion → point on w² = u³ + u² - u

Reduces the axiom `Z2xZ10_gives_non_degenerate_E20_point` to a single
Kubert moduli input, with all polynomial identities proved by `ring`.

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

/-! ## The single Kubert axiom -/

/-- If `E/ℚ` has a subgroup isomorphic to `ℤ/2ℤ × ℤ/10ℤ`, then `E` arises
from the cyclic-10 Kubert family with non-degenerate parameter, making the
quadratic factor of the 2-torsion polynomial have square discriminant. -/
axiom kubert_C10_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta10 t ≠ 0 ∧ s ^ 2 = A10 t ^ 2 - 4 * B10 t

/-- Discharge `Z2xZ10_gives_non_degenerate_E20_point` from the Kubert axiom. -/
theorem bridge_N10 (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E20AffineEquation u w ∧ ¬ E20DegenerateParameter u := by
  obtain ⟨t, s, hΔ, hs⟩ := kubert_C10_square E hE
  exact non_degenerate_of_square hΔ hs

end

end MazurProof.KubertBridgeN10
