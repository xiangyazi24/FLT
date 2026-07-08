import Mathlib

/-!
# Rational points on x³ + y³ = 1 (Fermat cubic)

The only rational solutions are (1,0) and (0,1), by FLT for exponent 3.
-/

namespace MazurProof.CyclicExclusion27

private lemma rat_cube_eq_one_iff (z : ℚ) : z ^ 3 = 1 ↔ z = 1 := by
  constructor
  · intro hz
    have hz' : z ^ 3 = (1 : ℚ) ^ 3 := by simpa using hz
    exact ((show Odd 3 by decide).pow_inj).mp hz'
  · intro hz; simp [hz]

theorem fermat_cubic_rational_points (x y : ℚ) (h : x ^ 3 + y ^ 3 = 1) :
    (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) := by
  have hFLTQ : FermatLastTheoremWith ℚ 3 :=
    (fermatLastTheoremFor_iff_rat (n := 3)).mp fermatLastTheoremThree
  by_cases hx : x = 0
  · right
    exact ⟨hx, (rat_cube_eq_one_iff y).mp (by simpa [hx] using h)⟩
  · by_cases hy : y = 0
    · left
      exact ⟨(rat_cube_eq_one_iff x).mp (by simpa [hy] using h), hy⟩
    · exfalso
      exact hFLTQ x y 1 hx hy (by norm_num) (by simpa using h)

end MazurProof.CyclicExclusion27
