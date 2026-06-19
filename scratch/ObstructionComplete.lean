import Mathlib

-- Already proved pieces (axiomatized here for modularity)
axiom int_solutions_20a4 (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) : u = -1 ∨ u = 0 ∨ u = 1
axiom coprime_sq_dvd (q : ℕ) (b : ℕ) (a N : ℤ) (hab : Int.gcd a b = 1)
    (hqN : Nat.Coprime q N.natAbs) (heq : a ^ 2 * (q : ℤ) = (b : ℤ) ^ 2 * N) : IsSquare q
axiom isSquare_of_isSquare_cube (q : ℕ) (h : IsSquare (q ^ 3)) : IsSquare q

-- Helper: r² ∈ ℤ → r.den = 1
theorem rat_sq_int_den_one (r : ℚ) (N : ℤ) (h : (r : ℚ) ^ 2 = (N : ℚ)) : r.den = 1 := by
  have h2 : r.num ^ 2 = N * (r.den : ℤ) ^ 2 := by
    have : (r.num : ℚ) ^ 2 = N * (r.den : ℚ) ^ 2 := by
      rw [← Rat.num_div_den r] at h; field_simp at h; linarith
    exact_mod_cast this
  have hcop : IsCoprime r.num (r.den : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr r.reduced
  have hcop2 := (IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)).mpr hcop
  have hdvd : (r.den : ℤ) ^ 2 ∣ r.num ^ 2 := ⟨N, by linarith⟩
  have h1 : (r.den : ℤ) ^ 2 ∣ 1 := hcop2.symm.dvd_of_dvd_mul_left (by simpa using hdvd)
  nlinarith [Int.le_of_dvd one_pos h1, (show (r.den : ℤ) ≥ 1 from by exact_mod_cast r.pos)]

-- Helper: r.den = 1 → r = r.num
theorem rat_eq_num (r : ℚ) (h : r.den = 1) : r = (r.num : ℚ) := by
  rw [← Rat.num_div_den r, h]; simp

-- THE MAIN THEOREM
theorem obstruction_20a4 (u w : ℚ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) : u = -1 ∨ u = 0 ∨ u = 1 := by
  by_cases hu : u = 0
  · right; left; exact hu
  -- u ≠ 0. Show u.den = 1.
  have hden : u.den = 1 := by
    by_contra hne
    have hq : 2 ≤ u.den := by have := u.pos; omega
    have hqne : (u.den : ℚ) ≠ 0 := by positivity
    have hq2 : (2 : ℚ) ≤ u.den := by exact_mod_cast hq
    -- u = u.num / u.den. Curve: w²·q³ = p(p²+pq-q²)
    set p := u.num
    set q := u.den
    have hu_eq : u = (p : ℚ) / q := (Rat.num_div_den u).symm
    have hmul : w ^ 2 * (q : ℚ) ^ 3 = p * ((p : ℚ) ^ 2 + p * q - (q : ℚ) ^ 2) := by
      rw [hu_eq] at h; field_simp at h ⊢; nlinarith
    -- p = 1: w² < 0
    -- p = -1: coprime argument → q=b² → False
    -- |p| ≥ 2: sorry (valuation argument)
    sorry
  -- u ∈ ℤ. Apply integer case.
  have huZ := rat_eq_num u hden
  -- w² = (u.num)³ + (u.num)² - u.num over ℚ
  have hw_eq : w ^ 2 = ((u.num : ℤ) : ℚ) ^ 3 + ((u.num : ℤ) : ℚ) ^ 2 - (u.num : ℤ) := by
    rw [← huZ]; exact h
  -- w.den = 1 (from rat_sq_int_den_one)
  have hwden : w.den = 1 := rat_sq_int_den_one w (u.num ^ 3 + u.num ^ 2 - u.num) (by push_cast; exact hw_eq)
  have hwZ := rat_eq_num w hwden
  -- Integer equation
  have hint : w.num ^ 2 = u.num ^ 3 + u.num ^ 2 - u.num := by
    have h1 : (w.num : ℚ) ^ 2 = (u.num : ℚ) ^ 3 + (u.num : ℚ) ^ 2 - (u.num : ℚ) := by
      sorry
    exact_mod_cast h1
  -- Apply integer case
  rcases int_solutions_20a4 u.num w.num hint with h1 | h2 | h3
  · left; rw [huZ, h1]; norm_num
  · right; left; rw [huZ, h2]; norm_num
  · right; right; rw [huZ, h3]; norm_num

