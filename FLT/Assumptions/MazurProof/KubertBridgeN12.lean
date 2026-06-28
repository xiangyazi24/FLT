import Mathlib
import FLT.Assumptions.MazurProof.DescentBridgeN12

/-!
# Kubert bridge: Z/2Z × Z/12Z torsion → point on w² = u³ - u² - 4u + 4

Reduces the axiom `Z2xZ12_gives_non_degenerate_N12_point` to a single
Kubert moduli input, with all polynomial identities proved by `ring`.

## The cyclic-12 Kubert family

For parameter `t ∈ ℚ`, define:
* `A₁₂(t) = 6t⁸ + 48t⁶ + 12t⁴ - 2`
* `B₁₂(t) = (t²-1)⁶(1+3t²)²`
* `E₁₂(t) : y² = x³ + A₁₂(t)x² + B₁₂(t)x`

## Key identity (PROVED by ring)

`A₁₂(t)² - 4B₁₂(t) = 256t⁶(t²+1)³(3t²-1)`

If this is a square `s²`, then removing the square factor `(16t²(t²+1))²`
gives `q² = (t²+1)(3t²-1)`, and setting `u = 3t²+1`, `w = 3tq` yields
`w² = u³ - u² - 4u + 4`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN12

noncomputable section

def A12 (t : ℚ) : ℚ :=
  6 * t ^ 8 + 48 * t ^ 6 + 12 * t ^ 4 - 2

def B12 (t : ℚ) : ℚ := (t ^ 2 - 1) ^ 6 * (1 + 3 * t ^ 2) ^ 2

def Delta12 (t : ℚ) : ℚ :=
  256 * (t ^ 2 - 1) ^ 12 * (1 + 3 * t ^ 2) ^ 4 * t ^ 6 *
    (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1)

/-! ## Polynomial identities — all proved by ring/norm_num -/

theorem quad_disc_identity_12 (t : ℚ) :
    A12 t ^ 2 - 4 * B12 t = 256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1) := by
  unfold A12 B12; ring

theorem delta12_zero_at_neg1 : Delta12 (-1) = 0 := by norm_num [Delta12]
theorem delta12_zero_at_0 : Delta12 0 = 0 := by norm_num [Delta12]
theorem delta12_zero_at_1 : Delta12 1 = 0 := by norm_num [Delta12]

/-! ## Square condition → obstruction curve point -/

theorem obstruction_point_of_square_12 {t s : ℚ} (ht : t ≠ 0)
    (hs : s ^ 2 = A12 t ^ 2 - 4 * B12 t) :
    ∃ w : ℚ, w ^ 2 = (3 * t ^ 2 + 1) ^ 3 - (3 * t ^ 2 + 1) ^ 2
                      - 4 * (3 * t ^ 2 + 1) + 4 := by
  refine ⟨3 * s / (16 * t ^ 2 * (t ^ 2 + 1)), ?_⟩
  have hdenom : (16 : ℚ) * t ^ 2 * (t ^ 2 + 1) ≠ 0 := by positivity
  have hdisc := quad_disc_identity_12 t
  have hs2 : s ^ 2 = 256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1) :=
    hs.trans hdisc
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hdenom)]
  calc (3 * s) ^ 2
      = 9 * s ^ 2 := by ring
    _ = 9 * (256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1)) := by rw [hs2]
    _ = ((3 * t ^ 2 + 1) ^ 3 - (3 * t ^ 2 + 1) ^ 2 - 4 * (3 * t ^ 2 + 1) + 4) *
        (16 * t ^ 2 * (t ^ 2 + 1)) ^ 2 := by ring

theorem non_degenerate_of_square_12 {t s : ℚ}
    (hΔ : Delta12 t ≠ 0)
    (hs : s ^ 2 = A12 t ^ 2 - 4 * B12 t) :
    ∃ u w : ℚ, E_N12_AffineEquation u w ∧ ¬ E_N12_DegenerateParameter u := by
  have ht : t ≠ 0 := by
    intro h; exact hΔ (by rw [h]; exact delta12_zero_at_0)
  obtain ⟨w, hw⟩ := obstruction_point_of_square_12 ht hs
  refine ⟨3 * t ^ 2 + 1, w, by unfold E_N12_AffineEquation; linarith, ?_⟩
  intro hdeg
  unfold E_N12_DegenerateParameter at hdeg
  rcases hdeg with h | h | h | h | h
  · -- u = -2: 3t²+1 = -2 impossible since t² ≥ 0
    nlinarith [sq_nonneg t]
  · -- u = 0: 3t²+1 = 0 impossible since t² ≥ 0
    nlinarith [sq_nonneg t]
  · -- u = 1: 3t²+1 = 1 ⇒ t = 0, contradicting Delta12 t ≠ 0
    have h1 : t ^ 2 = 0 := by linarith
    exact ht ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1)
  · -- u = 2: 3t²+1 = 2 ⇒ 3t²-1 = 0 ⇒ Delta12 t = 0
    exact hΔ (by
      have h3t : 3 * t ^ 2 - 1 = 0 := by linarith
      unfold Delta12; rw [h3t, mul_zero])
  · -- u = 4: 3t²+1 = 4 ⇒ t²-1 = 0 ⇒ Delta12 t = 0
    exact hΔ (by
      have ht1 : t ^ 2 - 1 = 0 := by linarith
      unfold Delta12; rw [ht1]; ring)

/-! ## The single Kubert axiom -/

/-- If `E/ℚ` has a subgroup isomorphic to `ℤ/2ℤ × ℤ/12ℤ`, then `E` arises
from the cyclic-12 Kubert family with non-degenerate parameter, making the
quadratic factor of the 2-torsion polynomial have square discriminant. -/
axiom kubert_C12_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t

/-- Discharge `Z2xZ12_gives_non_degenerate_N12_point` from the Kubert axiom. -/
theorem bridge_N12 (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N12_AffineEquation u w ∧ ¬ E_N12_DegenerateParameter u := by
  obtain ⟨t, s, hΔ, hs⟩ := kubert_C12_square E hE
  exact non_degenerate_of_square_12 hΔ hs

end

end MazurProof.KubertBridgeN12
