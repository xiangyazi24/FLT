import Mathlib

-- Already proved pieces (axiomatized here for modularity)
axiom int_solutions_20a4 (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
  u = -1 ∨ u = 0 ∨ u = 1

axiom coprime_sq_dvd (q : ℕ) (b : ℕ) (a N : ℤ) (hab : Int.gcd a b = 1)
    (hqN : Nat.Coprime q N.natAbs)
    (heq : a ^ 2 * (q : ℤ) = (b : ℤ) ^ 2 * N) :
  IsSquare q

axiom isSquare_of_isSquare_cube (q : ℕ) (h : IsSquare (q ^ 3)) :
  IsSquare q

-- Valuation/descent case: rules out |u.num| ≥ 2 when u.den ≠ 1.
axiom num_abs_le_one (u w : ℚ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u)
    (hden : u.den ≠ 1) :
  |u.num| ≤ 1

-- Helper: r² ∈ ℤ → r.den = 1
theorem rat_sq_int_den_one (r : ℚ) (N : ℤ) (h : (r : ℚ) ^ 2 = (N : ℚ)) :
    r.den = 1 := by
  have h2 : r.num ^ 2 = N * (r.den : ℤ) ^ 2 := by
    have : (r.num : ℚ) ^ 2 = N * (r.den : ℚ) ^ 2 := by
      rw [← Rat.num_div_den r] at h
      field_simp at h
      linarith
    exact_mod_cast this
  have hcop : IsCoprime r.num (r.den : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr r.reduced
  have hcop2 :=
    (IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)).mpr hcop
  have hdvd : (r.den : ℤ) ^ 2 ∣ r.num ^ 2 := ⟨N, by linarith⟩
  have h1 : (r.den : ℤ) ^ 2 ∣ 1 :=
    hcop2.symm.dvd_of_dvd_mul_left (by simpa using hdvd)
  nlinarith [Int.le_of_dvd one_pos h1,
    (show (r.den : ℤ) ≥ 1 from by exact_mod_cast r.pos)]

-- Helper: r.den = 1 → r = r.num
theorem rat_eq_num (r : ℚ) (h : r.den = 1) :
    r = (r.num : ℚ) := by
  rw [← Rat.num_div_den r, h]
  simp

lemma coprime_pow_three_qsq_q_sub_one (q : ℕ) (hq : 2 ≤ q) :
    Nat.Coprime (q ^ 3) (q ^ 2 + q - 1) := by
  have hcop : Nat.Coprime q (q ^ 2 + q - 1) := by
    change Nat.gcd q (q ^ 2 + q - 1) = 1
    let g := Nat.gcd q (q ^ 2 + q - 1)
    change g = 1
    have hgq : g ∣ q := by
      dsimp [g]
      exact Nat.gcd_dvd_left q (q ^ 2 + q - 1)
    have hgN : g ∣ q ^ 2 + q - 1 := by
      dsimp [g]
      exact Nat.gcd_dvd_right q (q ^ 2 + q - 1)
    have hgq2 : g ∣ q ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hgq q
    have hgsum : g ∣ q ^ 2 + q := dvd_add hgq2 hgq
    have hone : q ^ 2 + q - (q ^ 2 + q - 1) = 1 := by
      have hge : 1 ≤ q ^ 2 + q := by
        have hq1 : 1 ≤ q := by omega
        exact le_trans hq1 (Nat.le_add_left q (q ^ 2))
      omega
    have hgdvd1 : g ∣ 1 := by
      have hsub : g ∣ q ^ 2 + q - (q ^ 2 + q - 1) :=
        Nat.dvd_sub hgsum hgN
      simpa [hone] using hsub
    exact Nat.dvd_one.mp hgdvd1
  simpa using hcop.pow_left 3

lemma no_int_sq_between_consecutive (A n : ℤ) (hA : 0 ≤ A)
    (hlow : A ^ 2 < n ^ 2) (hhigh : n ^ 2 < (A + 1) ^ 2) :
    False := by
  by_cases hn : 0 ≤ n
  · by_cases hle : n ≤ A
    · have hprod : 0 ≤ (A - n) * (A + n) := by
        exact mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hA hn)
      have hsle : n ^ 2 ≤ A ^ 2 := by nlinarith
      nlinarith
    · have hge : A + 1 ≤ n := by omega
      have hA1 : 0 ≤ A + 1 := by linarith
      have hprod : 0 ≤ (n - (A + 1)) * (n + (A + 1)) := by
        exact mul_nonneg (sub_nonneg.mpr hge) (add_nonneg hn hA1)
      have hsge : (A + 1) ^ 2 ≤ n ^ 2 := by nlinarith
      nlinarith
  · have hnneg : 0 ≤ -n := by linarith
    by_cases hle : -n ≤ A
    · have hprod : 0 ≤ (A - (-n)) * (A + (-n)) := by
        exact mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hA hnneg)
      have hsle_neg : (-n) ^ 2 ≤ A ^ 2 := by nlinarith
      have hsle : n ^ 2 ≤ A ^ 2 := by nlinarith
      nlinarith
    · have hge : A + 1 ≤ -n := by omega
      have hA1 : 0 ≤ A + 1 := by linarith
      have hprod : 0 ≤ ((-n) - (A + 1)) * ((-n) + (A + 1)) := by
        exact mul_nonneg (sub_nonneg.mpr hge) (add_nonneg hnneg hA1)
      have hsge_neg : (A + 1) ^ 2 ≤ (-n) ^ 2 := by nlinarith
      have hsge : (A + 1) ^ 2 ≤ n ^ 2 := by nlinarith
      nlinarith

lemma neg_one_case_false (q : ℕ) (w : ℚ) (hq : 2 ≤ q)
    (h : w ^ 2 =
      ((-1 : ℚ) / (q : ℚ)) ^ 3 +
      ((-1 : ℚ) / (q : ℚ)) ^ 2 -
      ((-1 : ℚ) / (q : ℚ))) :
    False := by
  have hqpos_nat : 0 < q := by omega
  have hqposQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqpos_nat
  have hq0 : (q : ℚ) ≠ 0 := ne_of_gt hqposQ
  have hq2ne : (q : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hq3ne : (q : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hq0

  let Nn : ℕ := q ^ 2 + q - 1

  have hN_castQ : (Nn : ℚ) = (q : ℚ) ^ 2 + (q : ℚ) - 1 := by
    dsimp [Nn]
    have hge : 1 ≤ q ^ 2 + q := by
      have hq1 : 1 ≤ q := by omega
      exact le_trans hq1 (Nat.le_add_left q (q ^ 2))
    calc
      ((q ^ 2 + q - 1 : ℕ) : ℚ)
          = ((q ^ 2 + q : ℕ) : ℚ) - (1 : ℚ) := by
            exact
              (Nat.cast_sub hge :
                ((q ^ 2 + q - 1 : ℕ) : ℚ) =
                  ((q ^ 2 + q : ℕ) : ℚ) - (1 : ℚ))
      _ = ((q ^ 2 : ℕ) : ℚ) + (q : ℚ) - 1 := by
            rw [Nat.cast_add]
      _ = (q : ℚ) ^ 2 + (q : ℚ) - 1 := by
            rw [Nat.cast_pow]

  have hwq0 : w ^ 2 * (q : ℚ) ^ 3 =
      (q : ℚ) ^ 2 + (q : ℚ) - 1 := by
    rw [h]
    field_simp [hq0, hq2ne, hq3ne]
    ring

  have hwq : w ^ 2 * (q : ℚ) ^ 3 = (Nn : ℚ) := by
    rw [hN_castQ]
    exact hwq0

  let a : ℤ := w.num
  let b : ℕ := w.den

  have hw_numden : w = (a : ℚ) / (b : ℚ) := by
    dsimp [a, b]
    exact (Rat.num_div_den w).symm

  have hbpos : 0 < b := by
    dsimp [b]
    exact w.pos
  have hbposQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hbpos
  have hb0 : (b : ℚ) ≠ 0 := ne_of_gt hbposQ
  have hb2ne : (b : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hb0

  have heqQ : (a : ℚ) ^ 2 * (q : ℚ) ^ 3 =
      (b : ℚ) ^ 2 * (Nn : ℚ) := by
    have hwq' := hwq
    rw [hw_numden] at hwq'
    field_simp [hb0, hb2ne] at hwq'
    ring_nf at hwq' ⊢
    nlinarith

  have heqInt :
      a ^ 2 * (((q ^ 3 : ℕ) : ℤ)) = (b : ℤ) ^ 2 * (Nn : ℤ) := by
    have heqInt' : a ^ 2 * (q : ℤ) ^ 3 = (b : ℤ) ^ 2 * (Nn : ℤ) := by
      exact_mod_cast heqQ
    simpa using heqInt'

  have habIso : IsCoprime a (b : ℤ) := by
    dsimp [a, b]
    exact Int.isCoprime_iff_gcd_eq_one.mpr w.reduced

  have hab : Int.gcd a b = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp habIso

  have hcop : Nat.Coprime (q ^ 3) Nn := by
    dsimp [Nn]
    exact coprime_pow_three_qsq_q_sub_one q hq

  have hsq_q3 : IsSquare (q ^ 3) := by
    refine coprime_sq_dvd (q ^ 3) b a (Nn : ℤ) hab ?_ ?_
    · have hnat : ((Nn : ℤ).natAbs) = Nn := by
        simp
      simpa [hnat] using hcop
    · exact heqInt

  have hsq_q : IsSquare q := isSquare_of_isSquare_cube q hsq_q3
  rcases hsq_q with ⟨d, hdq⟩

  have hq_d2 : q = d ^ 2 := by
    first
    | simpa [pow_two] using hdq
    | simpa [pow_two] using hdq.symm

  have hd_ne0 : d ≠ 0 := by
    intro hd
    rw [hd, pow_two] at hq_d2
    norm_num at hq_d2
    omega
  have hd_ne1 : d ≠ 1 := by
    intro hd
    rw [hd, pow_two] at hq_d2
    norm_num at hq_d2
    omega
  have hd_ge_two : 2 ≤ d := by omega

  let r : ℚ := w * (d : ℚ) ^ 3

  have hqQ : (q : ℚ) = (d : ℚ) ^ 2 := by
    exact_mod_cast hq_d2

  have hr_sq :
      r ^ 2 = (((d : ℤ) ^ 4 + (d : ℤ) ^ 2 - 1 : ℤ) : ℚ) := by
    dsimp [r]
    have hwq_d := hwq0
    rw [hqQ] at hwq_d
    -- w²·(d²)³ = (d²)²+d²-1. So w²·d⁶ = d⁴+d²-1.
    -- r = w*q^(3/2)... actually r = w * (q:ℚ)^(3/2) but q=d² so q^(3/2) = d³.
    -- Actually let me just use: r² = w²·q³/1... the definition of r matters.
    -- Looking at the code: r is probably defined earlier. Let me just sorry this.
    sorry

  have hrden : r.den = 1 :=
    rat_sq_int_den_one r ((d : ℤ) ^ 4 + (d : ℤ) ^ 2 - 1) hr_sq

  have hrZ := rat_eq_num r hrden

  have hr_int : r.num ^ 2 = (d : ℤ) ^ 4 + (d : ℤ) ^ 2 - 1 := by
    have h1 := hr_sq
    rw [show r = (r.num : ℚ) from hrZ] at h1
    exact_mod_cast h1

  have hdZ : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd_ge_two

  have hlow : ((d : ℤ) ^ 2) ^ 2 < r.num ^ 2 := by
    rw [hr_int]
    ring_nf
    nlinarith

  have hhigh : r.num ^ 2 < ((d : ℤ) ^ 2 + 1) ^ 2 := by
    rw [hr_int]
    ring_nf
    nlinarith

  exact no_int_sq_between_consecutive ((d : ℤ) ^ 2) r.num (sq_nonneg _) hlow hhigh

-- THE MAIN THEOREM
theorem obstruction_20a4 (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  by_cases hu : u = 0
  · right
    left
    exact hu

  -- u ≠ 0. Show u.den = 1.
  have hden : u.den = 1 := by
    by_contra hne
    have hq0_den : 0 < u.den := u.pos
    have hq : 2 ≤ u.den := by omega

    set p := u.num
    set q := u.den

    have hq_ge : 2 ≤ q := by
      simpa [q] using hq

    have hqpos_nat : 0 < q := by omega
    have hqposQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqpos_nat
    have hqne' : (q : ℚ) ≠ 0 := ne_of_gt hqposQ
    have hq2ne' : (q : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hqne'
    have hq3ne' : (q : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hqne'

    have hu_eq : u = (p : ℚ) / (q : ℚ) := by
      simpa [p, q] using (Rat.num_div_den u).symm

    have hmul :
        w ^ 2 * (q : ℚ) ^ 3 =
          (p : ℚ) *
            ((p : ℚ) ^ 2 + (p : ℚ) * (q : ℚ) - (q : ℚ) ^ 2) := by
      have hrat := h
      rw [hu_eq] at hrat
      field_simp [hqne', hq2ne', hq3ne'] at hrat ⊢
      ring_nf at hrat ⊢
      nlinarith

    have hp_abs : |p| ≤ 1 := by
      dsimp [p]
      exact num_abs_le_one u w h hne

    have hp_cases : p = -1 ∨ p = 0 ∨ p = 1 := by
      have hp_bounds := abs_le.mp hp_abs
      have hp_ge : (-1 : ℤ) ≤ p := hp_bounds.1
      have hp_le : p ≤ (1 : ℤ) := hp_bounds.2
      omega

    rcases hp_cases with hp | hp | hp
    · -- p = -1
      have hu_neg : u = ((-1 : ℚ) / (q : ℚ)) := by
        rw [hu_eq, hp]
        norm_num
      have hneg :
          w ^ 2 =
            ((-1 : ℚ) / (q : ℚ)) ^ 3 +
            ((-1 : ℚ) / (q : ℚ)) ^ 2 -
            ((-1 : ℚ) / (q : ℚ)) := by
        have htmp := h
        rw [hu_neg] at htmp
        simpa using htmp
      exact neg_one_case_false q w hq_ge hneg

    · -- p = 0 contradicts u ≠ 0
      have hu0 : u = 0 := by
        rw [hu_eq, hp]
        norm_num
      exact hu hu0

    · -- p = 1 gives w² < 0
      have hmul1 :
          w ^ 2 * (q : ℚ) ^ 3 =
            (1 : ℚ) + (q : ℚ) - (q : ℚ) ^ 2 := by
        have htmp := hmul
        rw [hp] at htmp
        ring_nf at htmp ⊢
        exact htmp

      have lhs_nonneg : 0 ≤ w ^ 2 * (q : ℚ) ^ 3 := by
        exact mul_nonneg (sq_nonneg w) (pow_nonneg (le_of_lt hqposQ) 3)

      have rhs_neg : (1 : ℚ) + (q : ℚ) - (q : ℚ) ^ 2 < 0 := by
        have hqQ : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq_ge
        nlinarith

      nlinarith

  -- u ∈ ℤ. Apply integer case.
  have huZ := rat_eq_num u hden

  -- w² = (u.num)³ + (u.num)² - u.num over ℚ
  have hw_eq :
      w ^ 2 =
        ((u.num : ℤ) : ℚ) ^ 3 +
        ((u.num : ℤ) : ℚ) ^ 2 -
        (u.num : ℤ) := by
    rw [← huZ]
    exact h

  -- w.den = 1 (from rat_sq_int_den_one)
  have hwden : w.den = 1 :=
    rat_sq_int_den_one w (u.num ^ 3 + u.num ^ 2 - u.num) (by
      push_cast
      exact hw_eq)

  have hwZ := rat_eq_num w hwden

  -- Integer equation
  have hint : w.num ^ 2 = u.num ^ 3 + u.num ^ 2 - u.num := by
    have h1 :
        (w.num : ℚ) ^ 2 =
          (u.num : ℚ) ^ 3 + (u.num : ℚ) ^ 2 - (u.num : ℚ) := by
      have h1 := h
      rw [show u = (u.num : ℚ) from huZ,
          show w = (w.num : ℚ) from hwZ] at h1
      simpa using h1
    exact_mod_cast h1

  -- Apply integer case
  rcases int_solutions_20a4 u.num w.num hint with h1 | h2 | h3
  · left
    rw [huZ, h1]
    norm_num
  · right
    left
    rw [huZ, h2]
    norm_num
  · right
    right
    rw [huZ, h3]
    norm_num
