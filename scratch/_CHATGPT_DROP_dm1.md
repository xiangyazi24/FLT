# Q1338 (dm1): `n^3` square implies `n` square

```lean
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-- If `n ≠ 0` and `n^3` is a square, then `n` is a square. -/
theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases (isSquare_iff_exists_sq (n ^ 3)).1 h with ⟨c, hc⟩

  -- From `n^3 = c^2`, get `n^2 ∣ c^2`.
  have hndvd : n ^ 2 ∣ c ^ 2 := by
    rw [← hc]
    exact ⟨n, by ring⟩

  -- `ceilRoot 2 (n^2) = n`.
  have hceil : Nat.ceilRoot 2 (n ^ 2) = n := by
    simpa using
      (Nat.ceilRoot_pow_self (n := 2) (a := n)
        (by norm_num : (2 : ℕ) ≠ 0))

  -- By the ceil-root divisibility adjunction, `n^2 ∣ c^2` implies `n ∣ c`.
  have hn_dvd_c : n ∣ c := by
    have hraw : Nat.ceilRoot 2 (n ^ 2) ∣ c :=
      ((Nat.dvd_pow_iff_ceilRoot_dvd
        (a := n ^ 2) (b := c) (n := 2)
        (by norm_num : (2 : ℕ) ≠ 0)).1 hndvd)
    simpa [hceil] using hraw

  rcases hn_dvd_c with ⟨d, rfl⟩

  -- Cancel `n^2` from `n^3 = (n*d)^2`.
  refine (isSquare_iff_exists_sq n).2 ⟨d, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.pos_of_ne_zero hn) 2)
  calc
    n ^ 2 * n = n ^ 3 := by ring
    _ = (n * d) ^ 2 := hc
    _ = n ^ 2 * d ^ 2 := by ring
```

Key APIs used:

```lean
Nat.ceilRoot_pow_self
Nat.dvd_pow_iff_ceilRoot_dvd
isSquare_iff_exists_sq
```
