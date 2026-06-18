import Mathlib

theorem not_sq_three : ∀ n : ℤ, n ^ 2 ≠ 3 := by
  intro n hn
  have hupper : n ≤ 2 := by
    by_contra h
    have h3 : (3 : ℤ) ≤ n := by omega
    have hn0 : (0 : ℤ) ≤ n := by omega
    have hsq : (9 : ℤ) ≤ n * n := by
      simpa using (mul_le_mul h3 h3 (by norm_num : (0 : ℤ) ≤ 3) hn0)
    have hbad : (9 : ℤ) ≤ 3 := by
      calc
        (9 : ℤ) ≤ n * n := hsq
        _ = n ^ 2 := by ring
        _ = 3 := hn
    norm_num at hbad
  have hlower : -2 ≤ n := by
    by_contra h
    have h3 : (3 : ℤ) ≤ -n := by omega
    have hn0 : (0 : ℤ) ≤ -n := by omega
    have hsq : (9 : ℤ) ≤ (-n) * (-n) := by
      simpa using (mul_le_mul h3 h3 (by norm_num : (0 : ℤ) ≤ 3) hn0)
    have hbad : (9 : ℤ) ≤ 3 := by
      calc
        (9 : ℤ) ≤ (-n) * (-n) := hsq
        _ = n ^ 2 := by ring
        _ = 3 := hn
    norm_num at hbad
  interval_cases n <;> norm_num at hn
