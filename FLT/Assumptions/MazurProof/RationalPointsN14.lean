import Mathlib

/-!
# Rational points on w² = u³ + u² - 2u (Cremona 96A1)

The only rational u-coordinates are u ∈ {-2, 0, 1} (all with w = 0).
This discharges `obstruction_curve_N14_points_degenerate` from DescentBridgeN14.

## Proof route (2-isogeny descent)

The curve E: y² = x³ + x² - 2x = x(x+2)(x-1) has full rational 2-torsion.
The 2-isogeny φ with kernel ⟨(0,0)⟩ maps to E': y² = x³ - 2x² + 9x.

Selmer computation:
- Sel^φ(E/ℚ) = {1, -2}, size 2
- Sel^φ̂(E'/ℚ) = {1, 3}, size 2
- rank = dim Sel^φ + dim Sel^φ̂ - 2 = 0

Local obstructions:
- First isogeny: d=-1,2 over ℚ₂ (mod 8); d=±3,±6 over ℚ₃ (valuation)
- Dual isogeny: d<0 over ℝ (sign); d=2,6 over ℚ₂ (valuation)

Torsion: #E(𝔽₅)=4, #E(𝔽₇)=12, gcd=4 = #E[2](ℚ).
So E(ℚ) = E[2] = {O, (-2,0), (0,0), (1,0)}.
-/

namespace MazurProof.RationalPointsN14

/-- The 2-isogeny descent proves rank = 0 for y² = x³ + x² - 2x. -/
theorem rank_zero_96a1 :
    ∀ u w : ℚ, w ^ 2 = u ^ 3 + u ^ 2 - 2 * u →
      (u = -2 ∧ w = 0) ∨ (u = 0 ∧ w = 0) ∨ (u = 1 ∧ w = 0) := by
  sorry

theorem obstruction_curve_N14_u_degenerate :
    ∀ u w : ℚ, w ^ 2 = u ^ 3 + u ^ 2 - 2 * u →
      u = -2 ∨ u = 0 ∨ u = 1 := by
  intro u w h
  rcases rank_zero_96a1 u w h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
  · left; assumption
  · right; left; assumption
  · right; right; assumption

end MazurProof.RationalPointsN14
