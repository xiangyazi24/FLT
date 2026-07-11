import Mathlib
import scratch.ObstructionN14

/-!
# Rational points on w² = u³ + u² - 2u (Cremona 96A1)

The only rational u-coordinates are u ∈ {-2, 0, 1} (all with w = 0).
This discharges `obstruction_curve_N14_points_degenerate` from DescentBridgeN14.

Proof via scratch/ObstructionN14.lean (1924 lines, 0 sorry):
denominator normalization + coprime-factor splitting + Diophantine descent.
-/

namespace MazurProof.RationalPointsN14

/-- The full 2-isogeny descent proves w² = u³ + u² - 2u has only degenerate
rational points. -/
theorem rank_zero_96a1 :
    ∀ u w : ℚ, w ^ 2 = u ^ 3 + u ^ 2 - 2 * u →
      (u = -2 ∧ w = 0) ∨ (u = 0 ∧ w = 0) ∨ (u = 1 ∧ w = 0) := by
  intro u w h
  rcases obstruction_N14 u w h with hu | hu | hu
  · left; exact ⟨hu, by nlinarith [sq_nonneg w, hu]⟩
  · right; left; exact ⟨hu, by nlinarith [sq_nonneg w, hu]⟩
  · right; right; exact ⟨hu, by nlinarith [sq_nonneg w, hu]⟩

theorem obstruction_curve_N14_u_degenerate :
    ∀ u w : ℚ, w ^ 2 = u ^ 3 + u ^ 2 - 2 * u →
      u = -2 ∨ u = 0 ∨ u = 1 := by
  intro u w h
  rcases rank_zero_96a1 u w h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
  · left; assumption
  · right; left; assumption
  · right; right; assumption

end MazurProof.RationalPointsN14
