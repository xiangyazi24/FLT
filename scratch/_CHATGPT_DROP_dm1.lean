import Mathlib

/-!
# Two is not an integer square

A direct bounds proof: if `n ≤ -2` or `2 ≤ n`, then `n² ≥ 4`; otherwise
`n ∈ {-1,0,1}` and the equality is checked directly.
-/

/-- There is no integer whose square is `2`. -/
theorem not_sq_two : ∀ n : ℤ, n ^ 2 ≠ 2 := by
  intro n hn
  have hcases : n ≤ -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ 2 ≤ n := by
    omega
  rcases hcases with hle | hnegone | hzero | hone | hge
  · have hsq : (4 : ℤ) ≤ n ^ 2 := by
      have hnonneg : (0 : ℤ) ≤ (n + 2) ^ 2 := sq_nonneg (n + 2)
      nlinarith
    rw [hn] at hsq
    norm_num at hsq
  · subst n
    norm_num at hn
  · subst n
    norm_num at hn
  · subst n
    norm_num at hn
  · have hsq : (4 : ℤ) ≤ n ^ 2 := by
      have hnonneg : (0 : ℤ) ≤ (n - 2) ^ 2 := sq_nonneg (n - 2)
      nlinarith
    rw [hn] at hsq
    norm_num at hsq
