import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSolubility

namespace MazurProof.N18RouteC.LocalThree

set_option maxRecDepth 4000

/-- Certificate for the chart `D = 1`.  The class of `W` is the square of the
class of `2`: from `W * 2 = U ^ 3`, multiplication by `2⁻¹ = 5 = -4` gives
`W = 4 * (-U) ^ 3`. -/
theorem large_scaled_d_one :
    ∀ W : R5, IsUnit5 W →
      (∃ U : R5, IsUnit5 U ∧ W * 2 = U ^ 3) → InDualLine W := by
  intro W _ ⟨U, hU, hWU⟩
  refine ⟨2, -U, ?_, ?_⟩
  · have hnegOne : IsUnit5 (-1 : R5) := by
      change (-1 : ZMod 9).val % 3 ≠ 0
      norm_num
    simpa using isUnit5_mul hnegOne hU
  · change W = mul (pow two5 2) (pow (-U) 3)
    have hpowTwo : pow two5 2 = (4 : R5) := by
      ext <;> with_unfolding_all rfl
    rw [hpowTwo, pow_eq_ring_pow]
    have htwo : IsUnit5 (2 : R5) := by
      change 2 % 3 ≠ 0
      norm_num
    have hinv := mul_inv5_of_isUnit5 (2 : R5) htwo
    have hinvTwo : inv5 (2 : R5) = (5 : R5) := by
      ext <;> with_unfolding_all rfl
    have hfive : (5 : R5) = -(4 : R5) := by
      ext <;> with_unfolding_all rfl
    calc
      W = W * 1 := by ring
      _ = W * (2 * inv5 (2 : R5)) := by rw [hinv]
      _ = (W * 2) * inv5 (2 : R5) := by ring
      _ = U ^ 3 * inv5 (2 : R5) := by rw [hWU]
      _ = U ^ 3 * 5 := by rw [hinvTwo]
      _ = 4 * (-U) ^ 3 := by rw [hfive]; ring

end MazurProof.N18RouteC.LocalThree
