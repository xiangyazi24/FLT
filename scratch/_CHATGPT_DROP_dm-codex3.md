# Q2442 nat_square_factor_balance Lean code

```lean
import Mathlib

theorem nat_square_factor_balance
    {b c M N : ℕ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : Nat.Coprime b c)
    (hMN : Nat.Coprime M N)
    (h : b^2 * M = c^2 * N) :
    M = c^2 ∧ N = b^2 := by
  have hcb_sq : Nat.Coprime (c^2) (b^2) := by
    exact (hbc.symm.pow_left 2).pow_right 2
  have hc2_dvd_M : c^2 ∣ M := by
    exact (hcb_sq.dvd_mul_left).mp (by
      rw [h]
      exact dvd_mul_right (c^2) N)
  have hb2_dvd_N : b^2 ∣ N := by
    exact (hcb_sq.symm.dvd_mul_left).mp (by
      rw [← h]
      exact dvd_mul_right (b^2) M)
  rcases hc2_dvd_M with ⟨k, rfl⟩
  rcases hb2_dvd_N with ⟨l, rfl⟩
  have hkl : k = l := by
    have h' : (b^2 * c^2) * k = (b^2 * c^2) * l := by
      calc
        (b^2 * c^2) * k = b^2 * (c^2 * k) := by
          rw [Nat.mul_assoc]
        _ = c^2 * (b^2 * l) := h
        _ = (b^2 * c^2) * l := by
          ac_rfl
    have hbc2_ne : b^2 * c^2 ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hc)
    exact mul_left_cancel₀ hbc2_ne h'
  subst l
  have hk_one : k = 1 := by
    exact Nat.eq_one_of_dvd_coprimes hMN
      (dvd_mul_left k (c^2))
      (dvd_mul_left k (b^2))
  subst k
  simp
```
