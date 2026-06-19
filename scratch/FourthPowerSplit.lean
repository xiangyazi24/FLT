import Mathlib

namespace DenominatorQuartic

private theorem fourth_power_split_of_roots_product
    (x y m γ β : ℤ)
    (hx : x = γ ^ 2)
    (hy : y = β ^ 2)
    (hcop : IsCoprime γ β)
    (hprod : γ * β = m ^ 2) :
    ∃ c d : ℤ,
      x = c ^ 4 ∧
      y = d ^ 4 ∧
      (c * d) ^ 2 = m ^ 2 := by
  have hprod_swap : β * γ = m ^ 2 := by nlinarith
  obtain ⟨c, hc | hc⟩ := Int.sq_of_isCoprime hcop hprod
  · obtain ⟨d, hd | hd⟩ := Int.sq_of_isCoprime hcop.symm hprod_swap
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;> nlinarith
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;>
        nlinarith [sq_nonneg c, sq_nonneg d, sq_nonneg m, sq_nonneg (c * d)]
  · obtain ⟨d, hd | hd⟩ := Int.sq_of_isCoprime hcop.symm hprod_swap
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;>
        nlinarith [sq_nonneg c, sq_nonneg d, sq_nonneg m, sq_nonneg (c * d)]
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;> nlinarith

theorem fourth_power_split_without_abs
    (x y m : ℤ)
    (hxpos : 0 < x)
    (hypos : 0 < y)
    (hcop : IsCoprime x y)
    (hmul_sq : x * y = (m ^ 2) ^ 2) :
    ∃ c d : ℤ,
      x = c ^ 4 ∧
      y = d ^ 4 ∧
      (c * d) ^ 2 = m ^ 2 := by
  obtain ⟨α, hα | hα⟩ := Int.sq_of_isCoprime hcop hmul_sq
  · obtain ⟨β, hβ | hβ⟩ := Int.sq_of_isCoprime hcop.symm (show y * x = (m ^ 2) ^ 2 by linarith)
    · have hcop_αβ : IsCoprime α β := by
        rwa [hα, hβ, IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)] at hcop
      have hprod_sq : (α * β) ^ 2 = (m ^ 2) ^ 2 := by nlinarith
      have hm_sq_pos : 0 < m ^ 2 := by nlinarith [mul_pos hxpos hypos]
      by_cases hsign : 0 ≤ α * β
      · have hzero : (α * β - m ^ 2) * (α * β + m ^ 2) = 0 := by nlinarith
        have hleft : α * β - m ^ 2 = 0 := by
          rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with h | h
          · exact h
          · nlinarith
        exact fourth_power_split_of_roots_product x y m α β hα hβ hcop_αβ (by linarith)
      · have hlt : α * β < 0 := by omega
        have hsign' : 0 ≤ (-α) * β := by nlinarith
        have hzero : ((-α) * β - m ^ 2) * ((-α) * β + m ^ 2) = 0 := by nlinarith
        have hleft : (-α) * β - m ^ 2 = 0 := by
          rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with h | h
          · exact h
          · nlinarith
        have hcop_negαβ : IsCoprime (-α) β := by
          rcases hcop_αβ with ⟨u, v, huv⟩
          refine ⟨-u, v, ?_⟩
          nlinarith
        exact fourth_power_split_of_roots_product x y m (-α) β (by nlinarith) hβ hcop_negαβ (by linarith)
    · nlinarith [sq_nonneg β]
  · nlinarith [sq_nonneg α]

theorem fourth_power_split
    (p r m : ℤ)
    (hleft_pos : 0 < p - r)
    (hright_pos : 0 < p + r)
    (hcop : IsCoprime (p - r) (p + r))
    (htriple : p ^ 2 = m ^ 4 + r ^ 2) :
    ∃ c d : ℤ,
      p - r = c ^ 4 ∧
      p + r = d ^ 4 ∧
      (c * d) ^ 2 = m ^ 2 := by
  exact fourth_power_split_without_abs (p - r) (p + r) m hleft_pos hright_pos hcop (by nlinarith)

end DenominatorQuartic
