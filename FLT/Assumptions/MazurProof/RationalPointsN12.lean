import Mathlib
import FLT.Assumptions.MazurProof.DescentBridgeN12Defs

/-!
# Denominator normalization for the N=12 obstruction curve

This file proves the elementary reduction from a rational point on
`w² = u³ - u² - 4u + 4` to an integral square equation after writing
`u = A / B²` in lowest terms.  It is the rational-to-integral front end for
closing `obstruction_curve_N12_points_degenerate`.
-/

namespace MazurProof.RationalPointsN12

/-- If `n ≠ 0` and `n³` is a square, then `n` is a square. -/
private theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
         Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

/-- The denominator of `u³-u²-4u+4` equals `u.den³`. -/
private theorem den_cubic (u : ℚ) :
    ((u ^ 3 - u ^ 2 - 4 * u + 4).den : ℤ) = (u.den : ℤ) ^ 3 := by
  set a : ℤ := u.num
  set d : ℤ := (u.den : ℤ)
  have hdpos : (0 : ℤ) < d := by positivity
  have hdne : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hdpos)
  have hred : IsCoprime a d := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [a, d, Int.natAbs_natCast]
    exact u.reduced
  set N : ℤ := a ^ 3 - a ^ 2 * d - 4 * a * d ^ 2 + 4 * d ^ 3
  have hNd : IsCoprime N d := by
    have h1 : IsCoprime (a ^ 3) d := hred.pow_left
    have h2 : IsCoprime (a ^ 3 + d * (-(a ^ 2) - 4 * a * d + 4 * d ^ 2)) d :=
      h1.add_mul_left_left _
    convert h2 using 1
    ring
  have hNd3 : IsCoprime N (d ^ 3) := hNd.pow_right
  have hNd3_nat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hNd3
  have hrepr : u ^ 3 - u ^ 2 - 4 * u + 4 = (N : ℚ) / (d ^ 3 : ℚ) := by
    have hu : u = (a : ℚ) / (d : ℚ) := by
      simp only [a, d]
      push_cast
      exact (Rat.num_div_den u).symm
    rw [hu]
    field_simp [hdne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hNd3_nat

/-- Rational points on the N=12 obstruction curve have square denominator. -/
theorem rat_denom_square (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧ u = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare (u ^ 3 - u ^ 2 - 4 * u + 4) := ⟨w, by rw [← h]; ring⟩
  have hden_sq : IsSquare (u ^ 3 - u ^ 2 - 4 * u + 4).den := (Rat.isSquare_iff.mp hsq).2
  have hden_eq : (u ^ 3 - u ^ 2 - 4 * u + 4).den = u.den ^ 3 := by
    exact_mod_cast den_cubic u
  have hden3_sq : IsSquare (u.den ^ 3) := hden_eq ▸ hden_sq
  have hden_sq' : IsSquare u.den := nat_isSquare_of_isSquare_cube u.den_ne_zero hden3_sq
  obtain ⟨B₀, hB₀⟩ := hden_sq'
  have hB₀_pos : 0 < B₀ := by
    rcases Nat.eq_zero_or_pos B₀ with h | h
    · simp [h] at hB₀
    · exact h
  refine ⟨u.num, (B₀ : ℤ), by exact_mod_cast hB₀_pos, ?_, ?_⟩
  · have hBdvd : B₀ ∣ u.den := ⟨B₀, hB₀⟩
    have := u.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc u = (u.num : ℚ) / (u.den : ℚ) := by simpa using (Rat.num_div_den u).symm
      _ = (u.num : ℚ) / ((B₀ : ℚ) ^ 2) := by rw [hB₀]; push_cast; ring

/-- Integral square equation obtained from a rational point on the N=12 curve. -/
theorem integral_model_of_rational_point (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧ u = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) := by
  obtain ⟨A, B, hBpos, hcop, hu⟩ := rat_denom_square u w h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  rw [hu] at h
  have hinteg : ∃ C : ℤ, C ^ 2 = A ^ 3 - A ^ 2 * B ^ 2 - 4 * A * B ^ 4 + 4 * B ^ 6 := by
    set n : ℤ := A ^ 3 - A ^ 2 * B ^ 2 - 4 * A * B ^ 4 + 4 * B ^ 6
    have hrat : (w * (B : ℚ) ^ 3) ^ 2 = (n : ℚ) := by
      have := h
      push_cast [n] at this ⊢
      field_simp [hBne] at this ⊢
      nlinarith
    have hn_sq : IsSquare (n : ℚ) := ⟨w * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
    rw [Rat.isSquare_intCast_iff] at hn_sq
    obtain ⟨c, hc⟩ := hn_sq
    exact ⟨c, by rw [sq]; linarith⟩
  obtain ⟨C, hC⟩ := hinteg
  refine ⟨A, B, C, hBpos, hcop, hu, ?_⟩
  calc
    C ^ 2 = A ^ 3 - A ^ 2 * B ^ 2 - 4 * A * B ^ 4 + 4 * B ^ 6 := hC
    _ = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) := by ring

/-- Same reduction stated with the shared obstruction-curve predicate. -/
theorem integral_model_of_curve_point (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧ u = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) := by
  exact integral_model_of_rational_point u w (by
    simpa [MazurProof.E_N12_AffineEquation] using h)

/-! ## Coprimality of the integral factors -/

theorem gcd_linear_factor_with_denominator (A B k : ℤ)
    (hcop : Int.gcd A B = 1) :
    Int.gcd (A - k * B ^ 2) B = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have h : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have h' : IsCoprime (A + B * (-k * B)) B := h.add_mul_left_left _
  convert h' using 1
  ring

theorem coprime_linear_factor_with_denominator_sq (A B k : ℤ)
    (hcop : Int.gcd A B = 1) :
    IsCoprime (A - k * B ^ 2) (B ^ 2) := by
  have hB : IsCoprime (A - k * B ^ 2) B := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact gcd_linear_factor_with_denominator A B k hcop
  exact hB.pow_right

private theorem coprime_of_dvd_left {a b d : ℤ} (hab : IsCoprime a b)
    (hd : d ∣ a) :
    IsCoprime d b := by
  rcases hab with ⟨u, v, huv⟩
  rcases hd with ⟨k, rfl⟩
  exact ⟨u * k, v, by rw [← huv]; ring⟩

theorem coprime_factor_A_sub_B2_A_sub_2B2 (A B : ℤ)
    (hcop : Int.gcd A B = 1) :
    IsCoprime (A - B ^ 2) (A - 2 * B ^ 2) := by
  have hB : IsCoprime (A - B ^ 2) B := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using gcd_linear_factor_with_denominator A B 1 hcop
  have hB2 : IsCoprime (A - B ^ 2) (B ^ 2) := hB.pow_right
  obtain ⟨u, v, huv⟩ := hB2
  refine ⟨u + v, -v, ?_⟩
  rw [← huv]
  ring

theorem gcd_factor_A_sub_B2_A_sub_2B2 (A B : ℤ)
    (hcop : Int.gcd A B = 1) :
    Int.gcd (A - B ^ 2) (A - 2 * B ^ 2) = 1 := by
  exact Int.isCoprime_iff_gcd_eq_one.mp
    (coprime_factor_A_sub_B2_A_sub_2B2 A B hcop)

theorem gcd_factor_A_sub_B2_A_add_2B2_dvd_three (A B : ℤ)
    (hcop : Int.gcd A B = 1) :
    ((Int.gcd (A - B ^ 2) (A + 2 * B ^ 2) : ℕ) : ℤ) ∣ (3 : ℤ) := by
  let d : ℤ := (Int.gcd (A - B ^ 2) (A + 2 * B ^ 2) : ℤ)
  have hdf1 : d ∣ A - B ^ 2 := Int.gcd_dvd_left _ _
  have hdf3 : d ∣ A + 2 * B ^ 2 := Int.gcd_dvd_right _ _
  have hd3B2 : d ∣ 3 * B ^ 2 := by
    have hsub : d ∣ (A + 2 * B ^ 2) - (A - B ^ 2) := dvd_sub hdf3 hdf1
    convert hsub using 1
    ring
  have hcopdB2 : Int.gcd d (B ^ 2) = 1 := by
    have hcopf1B2 := coprime_linear_factor_with_denominator_sq A B 1 hcop
    have hcopd : IsCoprime d (B ^ 2) :=
      coprime_of_dvd_left hcopf1B2 (by simpa using hdf1)
    exact Int.isCoprime_iff_gcd_eq_one.mp hcopd
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hd3B2 hcopdB2

theorem gcd_factor_A_sub_2B2_A_add_2B2_dvd_four (A B : ℤ)
    (hcop : Int.gcd A B = 1) :
    ((Int.gcd (A - 2 * B ^ 2) (A + 2 * B ^ 2) : ℕ) : ℤ) ∣ (4 : ℤ) := by
  let d : ℤ := (Int.gcd (A - 2 * B ^ 2) (A + 2 * B ^ 2) : ℤ)
  have hdf2 : d ∣ A - 2 * B ^ 2 := Int.gcd_dvd_left _ _
  have hdf3 : d ∣ A + 2 * B ^ 2 := Int.gcd_dvd_right _ _
  have hd4B2 : d ∣ 4 * B ^ 2 := by
    have hsub : d ∣ (A + 2 * B ^ 2) - (A - 2 * B ^ 2) := dvd_sub hdf3 hdf2
    convert hsub using 1
    ring
  have hcopdB2 : Int.gcd d (B ^ 2) = 1 := by
    have hcopf2B2 := coprime_linear_factor_with_denominator_sq A B 2 hcop
    have hcopd : IsCoprime d (B ^ 2) :=
      coprime_of_dvd_left hcopf2B2 (by simpa using hdf2)
    exact Int.isCoprime_iff_gcd_eq_one.mp hcopd
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hd4B2 hcopdB2

/-! ## Elementary denominator-region facts -/

theorem square_denominator_one_of_A_eq_mul_B_sq (A B k : ℤ)
    (hBpos : 0 < B) (hcop : Int.gcd A B = 1)
    (hA : A = k * B ^ 2) :
    B = 1 := by
  have hBdvdA : B ∣ A := by
    rw [hA]
    exact ⟨k * B, by ring⟩
  have hBdvdG : B ∣ ((Int.gcd A B : ℕ) : ℤ) :=
    Int.dvd_coe_gcd hBdvdA dvd_rfl
  have hBdvd1 : B ∣ (1 : ℤ) := by
    simpa [hcop] using hBdvdG
  have hunit : IsUnit B := isUnit_iff_dvd_one.mpr hBdvd1
  rw [Int.isUnit_iff_abs_eq] at hunit
  rwa [abs_of_pos hBpos] at hunit

theorem square_denominator_one_of_factor_zero (A B : ℤ)
    (hBpos : 0 < B) (hcop : Int.gcd A B = 1)
    (hzero : A - B ^ 2 = 0 ∨ A - 2 * B ^ 2 = 0 ∨ A + 2 * B ^ 2 = 0) :
    B = 1 := by
  rcases hzero with hzero | hzero | hzero
  · exact square_denominator_one_of_A_eq_mul_B_sq A B 1 hBpos hcop (by nlinarith)
  · exact square_denominator_one_of_A_eq_mul_B_sq A B 2 hBpos hcop (by nlinarith)
  · exact square_denominator_one_of_A_eq_mul_B_sq A B (-2) hBpos hcop (by nlinarith)

theorem square_denominator_not_below_neg_two (A B C : ℤ)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ¬ A < -2 * B ^ 2 := by
  intro hA
  let f₁ : ℤ := A - B ^ 2
  let f₂ : ℤ := A - 2 * B ^ 2
  let f₃ : ℤ := A + 2 * B ^ 2
  have hf₁ : f₁ < 0 := by
    dsimp [f₁]
    nlinarith [sq_nonneg B]
  have hf₂ : f₂ < 0 := by
    dsimp [f₂]
    nlinarith [sq_nonneg B]
  have hf₃ : f₃ < 0 := by
    dsimp [f₃]
    nlinarith
  have h12 : 0 < f₁ * f₂ := mul_pos_of_neg_of_neg hf₁ hf₂
  have hprodneg : f₁ * f₂ * f₃ < 0 := mul_neg_of_pos_of_neg h12 hf₃
  have hprod : C ^ 2 = f₁ * f₂ * f₃ := by
    simpa [f₁, f₂, f₃] using hC
  nlinarith [sq_nonneg C]

theorem square_denominator_not_between_B2_and_2B2 (A B C : ℤ)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2))
    (hlo : B ^ 2 < A) :
    ¬ A < 2 * B ^ 2 := by
  intro hhi
  let f₁ : ℤ := A - B ^ 2
  let f₂ : ℤ := A - 2 * B ^ 2
  let f₃ : ℤ := A + 2 * B ^ 2
  have hf₁ : 0 < f₁ := by
    dsimp [f₁]
    nlinarith
  have hf₂ : f₂ < 0 := by
    dsimp [f₂]
    nlinarith
  have hf₃ : 0 < f₃ := by
    dsimp [f₃]
    nlinarith [sq_nonneg B]
  have h12 : f₁ * f₂ < 0 := mul_neg_of_pos_of_neg hf₁ hf₂
  have hprodneg : f₁ * f₂ * f₃ < 0 := mul_neg_of_neg_of_pos h12 hf₃
  have hprod : C ^ 2 = f₁ * f₂ * f₃ := by
    simpa [f₁, f₂, f₃] using hC
  nlinarith [sq_nonneg C]

theorem square_denominator_A_region (A B C : ℤ)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    (-2 * B ^ 2 ≤ A ∧ A ≤ B ^ 2) ∨ 2 * B ^ 2 ≤ A := by
  have hlow : -2 * B ^ 2 ≤ A := by
    by_contra h
    have hlt : A < -2 * B ^ 2 := by nlinarith
    exact square_denominator_not_below_neg_two A B C hC hlt
  by_cases hmid : A ≤ B ^ 2
  · exact Or.inl ⟨hlow, hmid⟩
  · right
    by_contra h
    have hlo : B ^ 2 < A := by nlinarith
    have hhi : A < 2 * B ^ 2 := by nlinarith
    exact square_denominator_not_between_B2_and_2B2 A B C hC hlo hhi

theorem square_denominator_nontrivial_factors_ne_zero (A B : ℤ)
    (hBgt : 1 < B) (hcop : Int.gcd A B = 1) :
    (A - B ^ 2 ≠ 0) ∧ (A - 2 * B ^ 2 ≠ 0) ∧ (A + 2 * B ^ 2 ≠ 0) := by
  have hBpos : 0 < B := by omega
  constructor
  · intro hzero
    have hB1 := square_denominator_one_of_factor_zero A B hBpos hcop (Or.inl hzero)
    omega
  constructor
  · intro hzero
    have hB1 := square_denominator_one_of_factor_zero A B hBpos hcop (Or.inr (Or.inl hzero))
    omega
  · intro hzero
    have hB1 := square_denominator_one_of_factor_zero A B hBpos hcop (Or.inr (Or.inr hzero))
    omega

theorem square_denominator_nontrivial_A_strict_region (A B C : ℤ)
    (hBgt : 1 < B) (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    (-2 * B ^ 2 < A ∧ A < B ^ 2) ∨ 2 * B ^ 2 < A := by
  obtain ⟨hf₁, hf₂, hf₃⟩ :=
    square_denominator_nontrivial_factors_ne_zero A B hBgt hcop
  rcases square_denominator_A_region A B C hC with hleft | hright
  · left
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hleft.1 (by
        intro hEq
        exact hf₃ (by nlinarith))
    · exact lt_of_le_of_ne hleft.2 (by
        intro hEq
        exact hf₁ (by nlinarith))
  · right
    exact lt_of_le_of_ne hright (by
      intro hEq
      exact hf₂ (by nlinarith))

theorem square_denominator_nontrivial_C_ne_zero (A B C : ℤ)
    (hBgt : 1 < B) (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    C ≠ 0 := by
  obtain ⟨hf₁, hf₂, hf₃⟩ :=
    square_denominator_nontrivial_factors_ne_zero A B hBgt hcop
  have hprod_ne :
      (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃
  intro hC0
  exact hprod_ne (by
    rw [← hC, hC0]
    norm_num)

theorem square_denominator_nontrivial_product_pos (A B C : ℤ)
    (hBgt : 1 < B) (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    0 < (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) := by
  have hCne := square_denominator_nontrivial_C_ne_zero A B C hBgt hcop hC
  rw [← hC]
  exact sq_pos_of_ne_zero hCne

theorem square_denominator_prime_not_dvd_A (A B : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpB : (p : ℤ) ∣ B)
    (hcop : Int.gcd A B = 1) :
    ¬ (p : ℤ) ∣ A := by
  intro hpA
  have hpg : (p : ℤ) ∣ ((Int.gcd A B : ℕ) : ℤ) := Int.dvd_coe_gcd hpA hpB
  have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
    simpa [hcop] using hpg
  have hpnat : p ∣ 1 := by
    exact_mod_cast hp1
  exact hp.not_dvd_one hpnat

theorem square_denominator_prime_dvd_A_of_dvd_B_and_C
    (A B C : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpB : (p : ℤ) ∣ B)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2))
    (hpC : (p : ℤ) ∣ C) :
    (p : ℤ) ∣ A := by
  have hpD : (p : ℤ) ∣ B ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hpB B
  have hpC2 : (p : ℤ) ∣ C ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hpC C
  have hpRHS : (p : ℤ) ∣ (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) := by
    rwa [hC] at hpC2
  have hdiff : (p : ℤ) ∣
      (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) - A ^ 3 := by
    refine hpD.trans ?_
    refine ⟨-A ^ 2 - 4 * A * B ^ 2 + 4 * (B ^ 2) ^ 2, ?_⟩
    ring
  have hA3' : (p : ℤ) ∣
      (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) -
        ((A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) - A ^ 3) :=
    dvd_sub hpRHS hdiff
  have hA3 : (p : ℤ) ∣ A ^ 3 := by
    convert hA3' using 1
    ring
  have hpz : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  exact hpz.dvd_of_dvd_pow hA3

theorem square_denominator_prime_not_dvd_C (A B C : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpB : (p : ℤ) ∣ B)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ¬ (p : ℤ) ∣ C := by
  intro hpC
  exact square_denominator_prime_not_dvd_A A B hp hpB hcop
    (square_denominator_prime_dvd_A_of_dvd_B_and_C A B C hp hpB hC hpC)

theorem square_denominator_C_coprime_B (A B C : ℤ)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    Int.gcd C B = 1 := by
  by_contra h
  obtain ⟨p, hp, hpG_nat⟩ := Nat.exists_prime_and_dvd h
  have hpG : (p : ℤ) ∣ ((Int.gcd C B : ℕ) : ℤ) := by
    exact_mod_cast hpG_nat
  have hpC : (p : ℤ) ∣ C := hpG.trans (Int.gcd_dvd_left C B)
  have hpB : (p : ℤ) ∣ B := hpG.trans (Int.gcd_dvd_right C B)
  exact (square_denominator_prime_not_dvd_C A B C hp hpB hcop hC) hpC

theorem square_denominator_C_coprime_B_sq (A B C : ℤ)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    IsCoprime C (B ^ 2) := by
  have hCB : IsCoprime C B := Int.isCoprime_iff_gcd_eq_one.mpr
    (square_denominator_C_coprime_B A B C hcop hC)
  exact hCB.pow_right

theorem square_denominator_A_square_mod_prime_of_prime_dvd_B
    (A B C : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpB : (p : ℤ) ∣ B)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ∃ z : ZMod p, z ^ 2 = (A : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBz : (B : ZMod p) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd B p).mpr hpB
  have hAz : (A : ZMod p) ≠ 0 := by
    intro h0
    exact (square_denominator_prime_not_dvd_A A B hp hpB hcop)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp h0)
  have hcast0 : ((C ^ 2 : ℤ) : ZMod p) =
      (((A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) : ℤ) : ZMod p) := by
    rw [hC]
  have hCz : (C : ZMod p) ^ 2 = (A : ZMod p) ^ 3 := by
    simpa [hBz, pow_succ, pow_two, mul_assoc] using hcast0
  refine ⟨(C : ZMod p) / (A : ZMod p), ?_⟩
  field_simp [hAz]
  exact hCz

theorem square_denominator_A_eq_primitive_square_mod_B_sq (A B C : ℤ)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ∃ z k : ℤ, Int.gcd z B = 1 ∧ A = z ^ 2 + k * B ^ 2 := by
  have hAB2 : IsCoprime A (B ^ 2) := by
    have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    exact hAB.pow_right
  obtain ⟨u, v, huv⟩ := hAB2
  have huB : IsCoprime u B := by
    refine ⟨A, v * B, ?_⟩
    rw [← huv]
    ring
  have hCuB : IsCoprime (C * u) B :=
    (Int.isCoprime_iff_gcd_eq_one.mpr
      (square_denominator_C_coprime_B A B C hcop hC)).mul_left huB
  have hAu : B ^ 2 ∣ A * u - 1 := by
    refine ⟨-v, ?_⟩
    nlinarith
  have hdiff : B ^ 2 ∣ C ^ 2 - A ^ 3 := by
    rw [hC]
    refine ⟨-A ^ 2 - 4 * A * B ^ 2 + 4 * (B ^ 2) ^ 2, ?_⟩
    ring
  have hmain : B ^ 2 ∣ (C * u) ^ 2 - A := by
    rcases hdiff with ⟨r, hr⟩
    rcases hAu with ⟨s, hs⟩
    refine ⟨r * u ^ 2 + A * s * (A * u + 1), ?_⟩
    calc
      (C * u) ^ 2 - A =
          (C ^ 2 - A ^ 3) * u ^ 2 + A * (A * u - 1) * (A * u + 1) := by ring
      _ = (B ^ 2 * r) * u ^ 2 + A * (B ^ 2 * s) * (A * u + 1) := by
          rw [hr, hs]
      _ = B ^ 2 * (r * u ^ 2 + A * s * (A * u + 1)) := by ring
  rcases hmain with ⟨k, hk⟩
  refine ⟨C * u, -k, Int.isCoprime_iff_gcd_eq_one.mp hCuB, ?_⟩
  nlinarith

theorem square_denominator_A_eq_square_mod_B_sq (A B C : ℤ)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ∃ z k : ℤ, A = z ^ 2 + k * B ^ 2 := by
  obtain ⟨z, k, _, hA⟩ :=
    square_denominator_A_eq_primitive_square_mod_B_sq A B C hcop hC
  exact ⟨z, k, hA⟩

theorem square_denominator_primitive_square_model (A B C : ℤ)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ∃ z k : ℤ,
      Int.gcd z B = 1 ∧
      A = z ^ 2 + k * B ^ 2 ∧
      C ^ 2 =
        (z ^ 2 + (k - 1) * B ^ 2) *
          (z ^ 2 + (k - 2) * B ^ 2) *
          (z ^ 2 + (k + 2) * B ^ 2) := by
  obtain ⟨z, k, hcopz, hA⟩ :=
    square_denominator_A_eq_primitive_square_mod_B_sq A B C hcop hC
  refine ⟨z, k, hcopz, hA, ?_⟩
  rw [hA] at hC
  convert hC using 1
  ring

theorem square_denominator_nontrivial_primitive_square_model (A B C : ℤ)
    (hBgt : 1 < B)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ∃ z k : ℤ,
      Int.gcd z B = 1 ∧
      A = z ^ 2 + k * B ^ 2 ∧
      C ^ 2 =
        (z ^ 2 + (k - 1) * B ^ 2) *
          (z ^ 2 + (k - 2) * B ^ 2) *
          (z ^ 2 + (k + 2) * B ^ 2) ∧
      ((-2 * B ^ 2 < z ^ 2 + k * B ^ 2 ∧
          z ^ 2 + k * B ^ 2 < B ^ 2) ∨
        2 * B ^ 2 < z ^ 2 + k * B ^ 2) ∧
      0 <
        (z ^ 2 + (k - 1) * B ^ 2) *
          (z ^ 2 + (k - 2) * B ^ 2) *
          (z ^ 2 + (k + 2) * B ^ 2) := by
  obtain ⟨z, k, hcopz, hA, hCzk⟩ :=
    square_denominator_primitive_square_model A B C hcop hC
  have hregion :=
    square_denominator_nontrivial_A_strict_region A B C hBgt hcop hC
  have hregion_z :
      ((-2 * B ^ 2 < z ^ 2 + k * B ^ 2 ∧
          z ^ 2 + k * B ^ 2 < B ^ 2) ∨
        2 * B ^ 2 < z ^ 2 + k * B ^ 2) := by
    simpa [hA] using hregion
  have hprod :=
    square_denominator_nontrivial_product_pos A B C hBgt hcop hC
  have hprod_z :
      0 <
        (z ^ 2 + (k - 1) * B ^ 2) *
          (z ^ 2 + (k - 2) * B ^ 2) *
          (z ^ 2 + (k + 2) * B ^ 2) := by
    rw [hA] at hprod
    convert hprod using 1
    ring
  exact ⟨z, k, hcopz, hA, hCzk, hregion_z, hprod_z⟩

theorem square_denominator_C_sq_eq_z_six_mod_B_sq (A B C z k : ℤ)
    (hA : A = z ^ 2 + k * B ^ 2)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    B ^ 2 ∣ C ^ 2 - z ^ 6 := by
  refine ⟨(3 * k - 1) * z ^ 4 +
      (3 * k ^ 2 - 2 * k - 4) * z ^ 2 * B ^ 2 +
      (k ^ 3 - k ^ 2 - 4 * k + 4) * B ^ 4, ?_⟩
  rw [hA] at hC
  rw [hC]
  ring

theorem square_denominator_z_cube_factor_divisible (A B C z k : ℤ)
    (hA : A = z ^ 2 + k * B ^ 2)
    (hC : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3) := by
  have hdiv := square_denominator_C_sq_eq_z_six_mod_B_sq A B C z k hA hC
  convert hdiv using 1
  ring

private theorem odd_nat_prime_int_not_dvd_two {p : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) :
    ¬ (p : ℤ) ∣ (2 : ℤ) := by
  intro hp2
  have hp2nat : p ∣ 2 := by exact_mod_cast hp2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2nat with hp1 | hp2'
  · exact hp.ne_one hp1
  · exact hpodd hp2'

theorem square_denominator_odd_prime_not_common_z_cube_factors
    (B C z : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1) :
    ¬ ((p : ℤ) ∣ C - z ^ 3 ∧ (p : ℤ) ∣ C + z ^ 3) := by
  intro hcommon
  have hsum : (p : ℤ) ∣ (C - z ^ 3) + (C + z ^ 3) :=
    dvd_add hcommon.1 hcommon.2
  have hp2C : (p : ℤ) ∣ 2 * C := by
    convert hsum using 1
    ring
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  rcases hpZ.dvd_or_dvd hp2C with hp2 | hpC
  · exact (odd_nat_prime_int_not_dvd_two hp hpodd) hp2
  · have hpG : (p : ℤ) ∣ ((Int.gcd C B : ℕ) : ℤ) := Int.dvd_coe_gcd hpC hpB
    rw [hcopC] at hpG
    exact hpZ.not_dvd_one hpG

theorem square_denominator_prime_dvd_sub_or_add_of_dvd_B_sq_product
    (B C z : ℤ) {p : ℕ}
    (hp : Nat.Prime p)
    (hpB : (p : ℤ) ∣ B)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    (p : ℤ) ∣ C - z ^ 3 ∨ (p : ℤ) ∣ C + z ^ 3 := by
  have hpB2 : (p : ℤ) ∣ B ^ 2 := dvd_pow hpB (by norm_num : 2 ≠ 0)
  have hprod : (p : ℤ) ∣ (C - z ^ 3) * (C + z ^ 3) :=
    dvd_trans hpB2 hdiv
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  exact hpZ.dvd_or_dvd hprod

theorem square_denominator_odd_prime_dvd_exactly_one_z_cube_factor
    (B C z : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ((p : ℤ) ∣ C - z ^ 3 ∧ ¬ (p : ℤ) ∣ C + z ^ 3) ∨
      ((p : ℤ) ∣ C + z ^ 3 ∧ ¬ (p : ℤ) ∣ C - z ^ 3) := by
  have hchoice :=
    square_denominator_prime_dvd_sub_or_add_of_dvd_B_sq_product
      B C z hp hpB hdiv
  have hnotboth :=
    square_denominator_odd_prime_not_common_z_cube_factors
      B C z hp hpodd hpB hcopC
  rcases hchoice with hminus | hplus
  · refine Or.inl ⟨hminus, ?_⟩
    intro hplus
    exact hnotboth ⟨hminus, hplus⟩
  · refine Or.inr ⟨hplus, ?_⟩
    intro hminus
    exact hnotboth ⟨hminus, hplus⟩

private theorem int_nat_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
    {a b : ℤ} {p n : ℕ}
    (hp : Nat.Prime p)
    (hprod : (p : ℤ) ^ n ∣ a * b)
    (hnotb : ¬ (p : ℤ) ∣ b) :
    (p : ℤ) ^ n ∣ a := by
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hprod' : (p : ℤ) ^ n ∣ b * a := by
    simpa [mul_comm] using hprod
  exact hpZ.pow_dvd_of_dvd_mul_left n hnotb hprod'

theorem square_denominator_prime_pow_dvd_one_factor_of_not_common
    (x y : ℤ) {p e : ℕ}
    (hp : Nat.Prime p)
    (hpProd : (p : ℤ) ∣ x * y)
    (hpowProd : (p : ℤ) ^ e ∣ x * y)
    (hnotCommon : ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y)) :
    (((p : ℤ) ^ e ∣ x ∧ ¬ (p : ℤ) ∣ y) ∨
      ((p : ℤ) ^ e ∣ y ∧ ¬ (p : ℤ) ∣ x)) := by
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  rcases hpZ.dvd_or_dvd hpProd with hx | hy
  · have hny : ¬ (p : ℤ) ∣ y := by
      intro hy
      exact hnotCommon ⟨hx, hy⟩
    refine Or.inl ⟨?_, hny⟩
    exact int_nat_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
      (a := x) (b := y) hp hpowProd hny
  · have hnx : ¬ (p : ℤ) ∣ x := by
      intro hx
      exact hnotCommon ⟨hx, hy⟩
    refine Or.inr ⟨?_, hnx⟩
    have hpowProd' : (p : ℤ) ^ e ∣ y * x := by
      simpa [mul_comm] using hpowProd
    exact int_nat_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
      (a := y) (b := x) hp hpowProd' hnx

theorem square_denominator_odd_prime_pow_dvd_one_z_cube_factor_of_B_sq
    (B C z : ℤ) {p e : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hpowBsq : (p : ℤ) ^ e ∣ B ^ 2)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    (((p : ℤ) ^ e ∣ C - z ^ 3 ∧ ¬ (p : ℤ) ∣ C + z ^ 3) ∨
      ((p : ℤ) ^ e ∣ C + z ^ 3 ∧ ¬ (p : ℤ) ∣ C - z ^ 3)) := by
  have hpB2 : (p : ℤ) ∣ B ^ 2 := dvd_pow hpB (by norm_num : 2 ≠ 0)
  have hpProd : (p : ℤ) ∣ (C - z ^ 3) * (C + z ^ 3) :=
    dvd_trans hpB2 hdiv
  have hpowProd : (p : ℤ) ^ e ∣ (C - z ^ 3) * (C + z ^ 3) :=
    dvd_trans hpowBsq hdiv
  exact square_denominator_prime_pow_dvd_one_factor_of_not_common
    (x := C - z ^ 3) (y := C + z ^ 3) hp hpProd hpowProd
    (square_denominator_odd_prime_not_common_z_cube_factors
      B C z hp hpodd hpB hcopC)

theorem square_denominator_odd_prime_pow_dvd_exactly_one_z_cube_factor
    (B C z : ℤ) {p e : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) (he : 0 < e)
    (hpBe : (p : ℤ) ^ e ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ((p : ℤ) ^ (2 * e) ∣ C - z ^ 3 ∧ ¬ (p : ℤ) ∣ C + z ^ 3) ∨
      ((p : ℤ) ^ (2 * e) ∣ C + z ^ 3 ∧ ¬ (p : ℤ) ∣ C - z ^ 3) := by
  have hpB : (p : ℤ) ∣ B := by
    have hpdvd : (p : ℤ) ∣ (p : ℤ) ^ e :=
      dvd_pow_self (p : ℤ) (Nat.ne_of_gt he)
    exact dvd_trans hpdvd hpBe
  have hsign :=
    square_denominator_odd_prime_dvd_exactly_one_z_cube_factor
      B C z hp hpodd hpB hcopC hdiv
  have hpowprod : (p : ℤ) ^ (2 * e) ∣ (C - z ^ 3) * (C + z ^ 3) := by
    have hB2 : ((p : ℤ) ^ e) ^ 2 ∣ B ^ 2 := pow_dvd_pow_of_dvd hpBe 2
    have hB2' : (p : ℤ) ^ (2 * e) ∣ B ^ 2 := by
      simpa [pow_mul, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hB2
    exact dvd_trans hB2' hdiv
  rcases hsign with ⟨hminus, hnotplus⟩ | ⟨hplus, hnotminus⟩
  · refine Or.inl ⟨?_, hnotplus⟩
    exact int_nat_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
      (a := C - z ^ 3) (b := C + z ^ 3) hp hpowprod hnotplus
  · refine Or.inr ⟨?_, hnotminus⟩
    have hpowprod' : (p : ℤ) ^ (2 * e) ∣ (C + z ^ 3) * (C - z ^ 3) := by
      simpa [mul_comm] using hpowprod
    exact int_nat_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
      (a := C + z ^ 3) (b := C - z ^ 3) hp hpowprod' hnotminus

inductive LocalSign where
  | minus
  | plus
deriving DecidableEq, Repr

namespace LocalSign

def Holds (s : LocalSign) (C z : ℤ) (p e : ℕ) : Prop :=
  match s with
  | minus => (p : ℤ) ^ e ∣ C - z ^ 3 ∧ ¬ (p : ℤ) ∣ C + z ^ 3
  | plus => (p : ℤ) ^ e ∣ C + z ^ 3 ∧ ¬ (p : ℤ) ∣ C - z ^ 3

end LocalSign

theorem square_denominator_odd_prime_pow_exists_local_sign
    (B C z : ℤ) {p e : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hpowBsq : (p : ℤ) ^ e ∣ B ^ 2)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ∃ s : LocalSign, s.Holds C z p e := by
  rcases square_denominator_odd_prime_pow_dvd_one_z_cube_factor_of_B_sq
      B C z hp hpodd hpB hcopC hpowBsq hdiv with hminus | hplus
  · exact ⟨LocalSign.minus, hminus⟩
  · exact ⟨LocalSign.plus, hplus⟩

theorem square_denominator_odd_prime_pow_signs
    (B C z : ℤ)
    (hcopC : Int.gcd C B = 1)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ∀ {p e : ℕ},
      Nat.Prime p →
      p ≠ 2 →
      (p : ℤ) ∣ B →
      (p : ℤ) ^ e ∣ B ^ 2 →
      ∃ s : LocalSign, s.Holds C z p e := by
  intro p e hp hpodd hpB hpowBsq
  exact square_denominator_odd_prime_pow_exists_local_sign
    B C z hp hpodd hpB hcopC hpowBsq hdiv

theorem square_denominator_two_not_dvd_of_gcd
    {x B : ℤ}
    (h2B : (2 : ℤ) ∣ B)
    (hxB : Int.gcd x B = 1) :
    ¬ (2 : ℤ) ∣ x := by
  intro h2x
  have h2gcd : (2 : ℤ) ∣ ((Int.gcd x B : ℕ) : ℤ) :=
    Int.dvd_coe_gcd h2x h2B
  rw [hxB] at h2gcd
  norm_num at h2gcd

theorem square_denominator_two_not_dvd_C_and_z
    (B C z : ℤ)
    (h2B : (2 : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hcopz : Int.gcd z B = 1) :
    ¬ (2 : ℤ) ∣ C ∧ ¬ (2 : ℤ) ∣ z :=
  ⟨square_denominator_two_not_dvd_of_gcd (x := C) (B := B) h2B hcopC,
    square_denominator_two_not_dvd_of_gcd (x := z) (B := B) h2B hcopz⟩

private theorem int_odd_of_not_two_dvd {x : ℤ}
    (hx : ¬ (2 : ℤ) ∣ x) :
    Odd x := by
  exact Int.not_even_iff_odd.mp (by
    intro hxEven
    exact hx (Even.two_dvd hxEven))

private theorem int_not_two_dvd_of_odd {x : ℤ}
    (hx : Odd x) :
    ¬ (2 : ℤ) ∣ x := by
  intro h2x
  have hxEven : Even x := even_iff_two_dvd.mpr h2x
  exact (Int.not_even_iff_odd.mpr hx) hxEven

theorem square_denominator_two_dvd_both_z_cube_factors_of_odd
    (C z : ℤ)
    (hCodd : Odd C)
    (hzodd : Odd z) :
    ((2 : ℤ) ∣ C - z ^ 3) ∧ ((2 : ℤ) ∣ C + z ^ 3) := by
  have hz3odd : Odd (z ^ 3) := hzodd.pow
  exact
    ⟨Even.two_dvd (hCodd.sub_odd hz3odd),
      Even.two_dvd (hCodd.add_odd hz3odd)⟩

theorem square_denominator_two_dvd_both_z_cube_factors
    (B C z : ℤ)
    (h2B : (2 : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hcopz : Int.gcd z B = 1) :
    ((2 : ℤ) ∣ C - z ^ 3) ∧ ((2 : ℤ) ∣ C + z ^ 3) := by
  have hnot := square_denominator_two_not_dvd_C_and_z
    (B := B) (C := C) (z := z) h2B hcopC hcopz
  exact square_denominator_two_dvd_both_z_cube_factors_of_odd
    (C := C) (z := z)
    (int_odd_of_not_two_dvd hnot.1)
    (int_odd_of_not_two_dvd hnot.2)

private theorem two_dvd_of_four_dvd_two_mul {x : ℤ}
    (h : (4 : ℤ) ∣ 2 * x) :
    (2 : ℤ) ∣ x := by
  rcases h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  nlinarith

theorem square_denominator_not_four_dvd_both_z_cube_factors_of_odd
    (C z : ℤ)
    (hCodd : Odd C) :
    ¬ (((4 : ℤ) ∣ C - z ^ 3) ∧ ((4 : ℤ) ∣ C + z ^ 3)) := by
  intro hboth
  have hsum : (4 : ℤ) ∣ (C - z ^ 3) + (C + z ^ 3) :=
    dvd_add hboth.1 hboth.2
  have h4_2C : (4 : ℤ) ∣ 2 * C := by
    convert hsum using 1
    ring
  have h2C : (2 : ℤ) ∣ C := two_dvd_of_four_dvd_two_mul h4_2C
  exact (int_not_two_dvd_of_odd hCodd) h2C

theorem square_denominator_two_dvd_both_and_not_four_dvd_both
    (B C z : ℤ)
    (h2B : (2 : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hcopz : Int.gcd z B = 1) :
    ((2 : ℤ) ∣ C - z ^ 3) ∧
      ((2 : ℤ) ∣ C + z ^ 3) ∧
        ¬ (((4 : ℤ) ∣ C - z ^ 3) ∧ ((4 : ℤ) ∣ C + z ^ 3)) := by
  have hnot := square_denominator_two_not_dvd_C_and_z
    (B := B) (C := C) (z := z) h2B hcopC hcopz
  have hCodd : Odd C := int_odd_of_not_two_dvd hnot.1
  have hzodd : Odd z := int_odd_of_not_two_dvd hnot.2
  have htwo := square_denominator_two_dvd_both_z_cube_factors_of_odd
    (C := C) (z := z) hCodd hzodd
  exact ⟨htwo.1, htwo.2,
    square_denominator_not_four_dvd_both_z_cube_factors_of_odd
      (C := C) (z := z) hCodd⟩

/-! ## The odd quartic branch -/

/--
The hard residual branch in the integral N=12 descent is the quartic
`b² = 3a⁴ + 2a² - 1` with `a` odd.  Its right hand side factors as
`(a²+1)(3a²-1)`.  For `a = 2k+1`, those two even factors have coprime
halves, so any square value forces both halves to be squares.
-/
theorem quartic_odd_param_factorization (k b : ℤ)
    (h : b ^ 2 = 3 * (2 * k + 1) ^ 4 + 2 * (2 * k + 1) ^ 2 - 1) :
    ∃ c u v : ℤ,
      b = 2 * c ∧
      2 * k ^ 2 + 2 * k + 1 = u ^ 2 ∧
      6 * k ^ 2 + 6 * k + 1 = v ^ 2 := by
  set F : ℤ := 2 * k ^ 2 + 2 * k + 1
  set G : ℤ := 6 * k ^ 2 + 6 * k + 1
  have hrhs : 3 * (2 * k + 1) ^ 4 + 2 * (2 * k + 1) ^ 2 - 1 = 4 * F * G := by
    dsimp [F, G]
    ring
  have h2b2 : (2 : ℤ) ∣ b ^ 2 := by
    refine ⟨2 * F * G, ?_⟩
    rw [h, hrhs]
    ring
  have h2b : (2 : ℤ) ∣ b := by
    exact (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (2 : ℤ)).dvd_of_dvd_pow h2b2
  obtain ⟨c, hc⟩ := h2b
  have hFG : c ^ 2 = F * G := by
    rw [hc] at h
    rw [hrhs] at h
    nlinarith
  have hcop : IsCoprime F G := by
    refine ⟨1 - 3 * (k ^ 2 + k), k ^ 2 + k, ?_⟩
    dsimp [F, G]
    ring
  have hFpos : 0 < F := by
    dsimp [F]
    nlinarith [sq_nonneg k, sq_nonneg (k + 1)]
  have hGpos : 0 < G := by
    dsimp [F, G] at hFpos ⊢
    nlinarith
  obtain ⟨u, hu | hu⟩ := Int.sq_of_isCoprime hcop hFG.symm
  · obtain ⟨v, hv | hv⟩ :=
      Int.sq_of_isCoprime hcop.symm (by rw [mul_comm]; exact hFG.symm)
    · exact ⟨c, u, v, hc, by simpa [F] using hu, by simpa [G] using hv⟩
    · nlinarith [sq_nonneg v]
  · nlinarith [sq_nonneg u]

/--
Conditional closure of the N=12 quartic residual.  After the elementary parity
split and the coprime factorization above, the only remaining input is the
Pell-type assertion that the two square conditions force `k = 0` or `k = -1`.
-/
theorem quartic_square_only_pm_one_of_pell
    (hpell : ∀ k u v : ℤ,
      2 * k ^ 2 + 2 * k + 1 = u ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = v ^ 2 →
      k = 0 ∨ k = -1)
    (a b : ℤ)
    (h : b ^ 2 = 3 * a ^ 4 + 2 * a ^ 2 - 1) :
    a ^ 2 = 1 := by
  rcases Int.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases Int.even_or_odd b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have : 4 * c ^ 2 = 48 * k ^ 4 + 8 * k ^ 2 - 1 := by nlinarith
    omega
  · have : 4 * c ^ 2 + 4 * c + 1 = 48 * k ^ 4 + 8 * k ^ 2 - 1 := by nlinarith
    omega
  · obtain ⟨_, u, v, _, hF, hG⟩ :=
      quartic_odd_param_factorization k (2 * c) (by simpa [two_mul] using h)
    rcases hpell k u v hF hG with hk | hk <;> rw [hk] <;> norm_num
  · have :
        4 * c ^ 2 + 4 * c + 1 =
          3 * (16 * k ^ 4 + 32 * k ^ 3 + 24 * k ^ 2 + 8 * k + 1) +
            2 * (4 * k ^ 2 + 4 * k + 1) - 1 := by
      nlinarith
    omega

/-! ### Congruence reductions for the Pell residual -/

private lemma pell_square_mod3_product_zero (K U V : ZMod 3)
    (hF : 2 * K ^ 2 + 2 * K + 1 = U ^ 2)
    (hG : 6 * K ^ 2 + 6 * K + 1 = V ^ 2) :
    K * (K + 1) = 0 := by
  decide +revert

/--
The simultaneous Pell residual forces `k ≡ 0` or `k ≡ -1` modulo `3`.
-/
theorem pell_square_mod3_product_dvd (k u v : ℤ)
    (hF : 2 * k ^ 2 + 2 * k + 1 = u ^ 2)
    (hG : 6 * k ^ 2 + 6 * k + 1 = v ^ 2) :
    (3 : ℤ) ∣ k * (k + 1) := by
  have hF3 : 2 * (k : ZMod 3) ^ 2 + 2 * (k : ZMod 3) + 1 = (u : ZMod 3) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hF
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  have hG3 : 6 * (k : ZMod 3) ^ 2 + 6 * (k : ZMod 3) + 1 = (v : ZMod 3) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hG
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k * (k + 1)) 3).mp (by
    simpa [Int.cast_mul, Int.cast_add] using
      pell_square_mod3_product_zero (k : ZMod 3) (u : ZMod 3) (v : ZMod 3) hF3 hG3)

private lemma pell_square_mod5_product_zero (K U V : ZMod 5)
    (hF : 2 * K ^ 2 + 2 * K + 1 = U ^ 2)
    (hG : 6 * K ^ 2 + 6 * K + 1 = V ^ 2) :
    K * (K + 1) = 0 := by
  decide +revert

/--
The simultaneous Pell residual forces `k ≡ 0` or `k ≡ -1` modulo `5`.
Stated divisibly, this is the form needed for later descent steps.
-/
theorem pell_square_mod5_product_dvd (k u v : ℤ)
    (hF : 2 * k ^ 2 + 2 * k + 1 = u ^ 2)
    (hG : 6 * k ^ 2 + 6 * k + 1 = v ^ 2) :
    (5 : ℤ) ∣ k * (k + 1) := by
  have hF5 : 2 * (k : ZMod 5) ^ 2 + 2 * (k : ZMod 5) + 1 = (u : ZMod 5) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 5)) hF
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  have hG5 : 6 * (k : ZMod 5) ^ 2 + 6 * (k : ZMod 5) + 1 = (v : ZMod 5) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 5)) hG
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k * (k + 1)) 5).mp (by
    simpa [Int.cast_mul, Int.cast_add] using
      pell_square_mod5_product_zero (k : ZMod 5) (u : ZMod 5) (v : ZMod 5) hF5 hG5)

private lemma pell_square_mod7_product_zero (K U V : ZMod 7)
    (hF : 2 * K ^ 2 + 2 * K + 1 = U ^ 2)
    (hG : 6 * K ^ 2 + 6 * K + 1 = V ^ 2) :
    K * (K + 1) = 0 := by
  decide +revert

/--
The same Pell residual also forces `k ≡ 0` or `k ≡ -1` modulo `7`.
-/
theorem pell_square_mod7_product_dvd (k u v : ℤ)
    (hF : 2 * k ^ 2 + 2 * k + 1 = u ^ 2)
    (hG : 6 * k ^ 2 + 6 * k + 1 = v ^ 2) :
    (7 : ℤ) ∣ k * (k + 1) := by
  have hF7 : 2 * (k : ZMod 7) ^ 2 + 2 * (k : ZMod 7) + 1 = (u : ZMod 7) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 7)) hF
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  have hG7 : 6 * (k : ZMod 7) ^ 2 + 6 * (k : ZMod 7) + 1 = (v : ZMod 7) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 7)) hG
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k * (k + 1)) 7).mp (by
    simpa [Int.cast_mul, Int.cast_add] using
      pell_square_mod7_product_zero (k : ZMod 7) (u : ZMod 7) (v : ZMod 7) hF7 hG7)

private lemma pell_square_mod11_product_zero (K U V : ZMod 11)
    (hF : 2 * K ^ 2 + 2 * K + 1 = U ^ 2)
    (hG : 6 * K ^ 2 + 6 * K + 1 = V ^ 2) :
    K * (K + 1) = 0 := by
  decide +revert

/--
The same Pell residual also forces `k ≡ 0` or `k ≡ -1` modulo `11`.
-/
theorem pell_square_mod11_product_dvd (k u v : ℤ)
    (hF : 2 * k ^ 2 + 2 * k + 1 = u ^ 2)
    (hG : 6 * k ^ 2 + 6 * k + 1 = v ^ 2) :
    (11 : ℤ) ∣ k * (k + 1) := by
  have hF11 : 2 * (k : ZMod 11) ^ 2 + 2 * (k : ZMod 11) + 1 = (u : ZMod 11) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 11)) hF
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  have hG11 : 6 * (k : ZMod 11) ^ 2 + 6 * (k : ZMod 11) + 1 = (v : ZMod 11) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 11)) hG
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k * (k + 1)) 11).mp (by
    simpa [Int.cast_mul, Int.cast_add] using
      pell_square_mod11_product_zero (k : ZMod 11) (u : ZMod 11) (v : ZMod 11) hF11 hG11)

/-- Combined small-prime congruence obstruction for the Pell residual. -/
theorem pell_square_mod1155_product_dvd (k u v : ℤ)
    (hF : 2 * k ^ 2 + 2 * k + 1 = u ^ 2)
    (hG : 6 * k ^ 2 + 6 * k + 1 = v ^ 2) :
    (1155 : ℤ) ∣ k * (k + 1) := by
  have h3 := pell_square_mod3_product_dvd k u v hF hG
  have h5 := pell_square_mod5_product_dvd k u v hF hG
  have h7 := pell_square_mod7_product_dvd k u v hF hG
  have h11 := pell_square_mod11_product_dvd k u v hF hG
  have h15 : (15 : ℤ) ∣ k * (k + 1) := by
    have hcop : IsCoprime (3 : ℤ) (5 : ℤ) := by norm_num
    simpa using hcop.mul_dvd h3 h5
  have h105 : (105 : ℤ) ∣ k * (k + 1) := by
    have hcop : IsCoprime (15 : ℤ) (7 : ℤ) := by norm_num
    simpa using hcop.mul_dvd h15 h7
  have h1155 : (1155 : ℤ) ∣ k * (k + 1) := by
    have hcop : IsCoprime (105 : ℤ) (11 : ℤ) := by norm_num
    simpa using hcop.mul_dvd h105 h11
  exact h1155

private lemma pell_square_mod13_residue_zmod (K U V : ZMod 13)
    (hF : 2 * K ^ 2 + 2 * K + 1 = U ^ 2)
    (hG : 6 * K ^ 2 + 6 * K + 1 = V ^ 2) :
    K = 0 ∨ K = 5 ∨ K = 7 ∨ K = -1 := by
  decide +revert

/-- Exact residue set modulo `13` for the Pell residual. -/
theorem pell_square_mod13_residue (k u v : ℤ)
    (hF : 2 * k ^ 2 + 2 * k + 1 = u ^ 2)
    (hG : 6 * k ^ 2 + 6 * k + 1 = v ^ 2) :
    (k : ZMod 13) = 0 ∨ (k : ZMod 13) = 5 ∨
      (k : ZMod 13) = 7 ∨ (k : ZMod 13) = -1 := by
  have hF13 : 2 * (k : ZMod 13) ^ 2 + 2 * (k : ZMod 13) + 1 = (u : ZMod 13) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 13)) hF
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  have hG13 : 6 * (k : ZMod 13) ^ 2 + 6 * (k : ZMod 13) + 1 = (v : ZMod 13) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod 13)) hG
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast
  exact pell_square_mod13_residue_zmod (k : ZMod 13) (u : ZMod 13) (v : ZMod 13) hF13 hG13

/-! ## Rational points on the N=12 Kubert cover -/

/--
Clearing denominators on the N=12 Kubert cover
`q² = (t²+1)(3t²-1)`.

Writing `t = T/D` in lowest terms gives the primitive integral quartic
`Y² = (T²+D²)(3T²-D²)`.
-/
theorem kubert_cover_integral_model (t q : ℚ)
    (h : q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1)) :
    ∃ T D Y : ℤ,
      0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
      Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) := by
  let T : ℤ := t.num
  let D : ℤ := (t.den : ℤ)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hcop : Int.gcd T D = 1 := by
    dsimp [T, D]
    simpa [Int.gcd, Int.natAbs_natCast] using t.reduced
  have ht : t = (T : ℚ) / (D : ℚ) := by
    dsimp [T, D]
    push_cast
    exact (Rat.num_div_den t).symm
  set N : ℤ := (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)
  have hrat : (q * (D : ℚ) ^ 2) ^ 2 = (N : ℚ) := by
    have hscaled : q ^ 2 * (D : ℚ) ^ 4 = (N : ℚ) := by
      rw [h, ht]
      field_simp [hDne]
      push_cast [N]
      ring
    calc
      (q * (D : ℚ) ^ 2) ^ 2 = q ^ 2 * (D : ℚ) ^ 4 := by ring
      _ = (N : ℚ) := hscaled
  have hn_sq : IsSquare (N : ℚ) :=
    ⟨q * (D : ℚ) ^ 2, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hn_sq
  obtain ⟨Y, hY⟩ := hn_sq
  refine ⟨T, D, Y, hDpos, hcop, ht, ?_⟩
  rw [sq]
  change Y * Y = N
  exact hY.symm

theorem kubert_cover_factor_gcd_dvd_four (T D : ℤ)
    (hcop : Int.gcd T D = 1) :
    ((Int.gcd (T ^ 2 + D ^ 2) (3 * T ^ 2 - D ^ 2) : ℕ) : ℤ) ∣ (4 : ℤ) := by
  let g : ℤ := (Int.gcd (T ^ 2 + D ^ 2) (3 * T ^ 2 - D ^ 2) : ℤ)
  have hgA : g ∣ T ^ 2 + D ^ 2 := Int.gcd_dvd_left _ _
  have hgB : g ∣ 3 * T ^ 2 - D ^ 2 := Int.gcd_dvd_right _ _
  have hg4T2 : g ∣ 4 * T ^ 2 := by
    have hsum : g ∣ (T ^ 2 + D ^ 2) + (3 * T ^ 2 - D ^ 2) := dvd_add hgA hgB
    convert hsum using 1
    ring
  have hDT : IsCoprime D T := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_comm] using hcop
  have hA_T2 : IsCoprime (T ^ 2 + D ^ 2) (T ^ 2) := by
    have hD2T2 : IsCoprime (D ^ 2) (T ^ 2) := (hDT.pow_left).pow_right
    have h' : IsCoprime (D ^ 2 + T ^ 2 * 1) (T ^ 2) := hD2T2.add_mul_left_left 1
    convert h' using 1
    ring
  have hgT2 : Int.gcd g (T ^ 2) = 1 := by
    have hg_coprime : IsCoprime g (T ^ 2) :=
      coprime_of_dvd_left hA_T2 (by simpa using hgA)
    exact Int.isCoprime_iff_gcd_eq_one.mp hg_coprime
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hg4T2 hgT2

theorem kubert_cover_second_factor_nonnegative (T D Y : ℤ)
    (hD : 0 < D)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    0 ≤ 3 * T ^ 2 - D ^ 2 := by
  have hApos : 0 < T ^ 2 + D ^ 2 := by nlinarith [sq_nonneg T, sq_pos_of_ne_zero hD.ne']
  have hsq : 0 ≤ Y ^ 2 := sq_nonneg Y
  nlinarith

theorem kubert_cover_split_of_coprime (T D Y : ℤ)
    (hD : 0 < D)
    (hcopf : Int.gcd (T ^ 2 + D ^ 2) (3 * T ^ 2 - D ^ 2) = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ a b : ℤ, T ^ 2 + D ^ 2 = a ^ 2 ∧ 3 * T ^ 2 - D ^ 2 = b ^ 2 := by
  have hApos : 0 < T ^ 2 + D ^ 2 := by nlinarith [sq_nonneg T, sq_pos_of_ne_zero hD.ne']
  have hBnonneg := kubert_cover_second_factor_nonnegative T D Y hD h
  obtain ⟨a, ha | ha⟩ := Int.sq_of_gcd_eq_one hcopf h.symm
  · have hcopf' : Int.gcd (3 * T ^ 2 - D ^ 2) (T ^ 2 + D ^ 2) = 1 := by
      rw [Int.gcd_comm]
      exact hcopf
    have h' : (3 * T ^ 2 - D ^ 2) * (T ^ 2 + D ^ 2) = Y ^ 2 := by
      rw [h]
      ring
    obtain ⟨b, hb | hb⟩ := Int.sq_of_gcd_eq_one hcopf' h'
    · exact ⟨a, b, ha, hb⟩
    · have hb0 : b = 0 := by nlinarith [sq_nonneg b]
      exact ⟨a, b, ha, by rw [hb0] at hb ⊢; simpa using hb⟩
  · nlinarith [sq_nonneg a]

private theorem gcd_eq_one_of_dvd_four_of_odd_left {A B : ℤ}
    (hdvd4 : ((Int.gcd A B : ℕ) : ℤ) ∣ (4 : ℤ))
    (hAodd : ¬ (2 : ℤ) ∣ A) :
    Int.gcd A B = 1 := by
  have hdvd4Nat : Int.gcd A B ∣ 4 := by
    exact_mod_cast hdvd4
  have hnot2g : ¬ 2 ∣ Int.gcd A B := by
    intro h2g
    have h2gZ : (2 : ℤ) ∣ ((Int.gcd A B : ℕ) : ℤ) := by exact_mod_cast h2g
    exact hAodd (h2gZ.trans (by simpa using Int.gcd_dvd_left A B))
  have hg_le : Int.gcd A B ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4Nat
  interval_cases h : Int.gcd A B
  · exfalso
    exact hnot2g (by norm_num)
  · rfl
  · exfalso
    exact hnot2g (by norm_num)
  · norm_num at hdvd4Nat
  · exfalso
    exact hnot2g (by norm_num)

theorem kubert_cover_factor_gcd_eq_one_of_even_odd (T D : ℤ)
    (hcop : Int.gcd T D = 1) (hT : Even T) (hD : Odd D) :
    Int.gcd (T ^ 2 + D ^ 2) (3 * T ^ 2 - D ^ 2) = 1 := by
  apply gcd_eq_one_of_dvd_four_of_odd_left (kubert_cover_factor_gcd_dvd_four T D hcop)
  rintro ⟨c, hc⟩
  rcases hT with ⟨t, rfl⟩
  rcases hD with ⟨d, rfl⟩
  ring_nf at hc
  omega

theorem kubert_cover_factor_gcd_eq_one_of_odd_even (T D : ℤ)
    (hcop : Int.gcd T D = 1) (hT : Odd T) (hD : Even D) :
    Int.gcd (T ^ 2 + D ^ 2) (3 * T ^ 2 - D ^ 2) = 1 := by
  apply gcd_eq_one_of_dvd_four_of_odd_left (kubert_cover_factor_gcd_dvd_four T D hcop)
  rintro ⟨c, hc⟩
  rcases hT with ⟨t, rfl⟩
  rcases hD with ⟨d, rfl⟩
  ring_nf at hc
  omega

theorem kubert_cover_no_even_odd (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (hT : Even T) (hD : Odd D)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    False := by
  have hcopf := kubert_cover_factor_gcd_eq_one_of_even_odd T D hcop hT hD
  obtain ⟨a, b, hA, hB⟩ := kubert_cover_split_of_coprime T D Y hDpos hcopf h
  have hsum : a ^ 2 + b ^ 2 = 4 * T ^ 2 := by nlinarith
  rcases hT with ⟨t, rfl⟩
  rcases hD with ⟨d, rfl⟩
  rcases Int.even_or_odd a with ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [hx] at hA
    ring_nf at hA
    omega
  · rcases Int.even_or_odd b with ⟨y, hy⟩ | ⟨y, hy⟩
    · rw [hy] at hB
      ring_nf at hB
      omega
    · rw [hx, hy] at hsum
      ring_nf at hsum
      omega

theorem kubert_cover_no_odd_even (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (hT : Odd T) (hD : Even D)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    False := by
  have hcopf := kubert_cover_factor_gcd_eq_one_of_odd_even T D hcop hT hD
  obtain ⟨a, b, hA, hB⟩ := kubert_cover_split_of_coprime T D Y hDpos hcopf h
  have hsum : a ^ 2 + b ^ 2 = 4 * T ^ 2 := by nlinarith
  rcases hT with ⟨t, rfl⟩
  rcases hD with ⟨d, rfl⟩
  rcases Int.even_or_odd a with ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [hx] at hA
    ring_nf at hA
    omega
  · rcases Int.even_or_odd b with ⟨y, hy⟩ | ⟨y, hy⟩
    · rw [hy] at hB
      ring_nf at hB
      omega
    · rw [hx, hy] at hsum
      ring_nf at hsum
      omega

theorem kubert_cover_odd_odd (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    Odd T ∧ Odd D := by
  rcases Int.even_or_odd T with hTeven | hTodd
  · rcases Int.even_or_odd D with hDeven | hDodd
    · exfalso
      rcases hTeven with ⟨t, ht⟩
      rcases hDeven with ⟨d, hd⟩
      have h2T : (2 : ℤ) ∣ T := ⟨t, by rw [ht]; ring⟩
      have h2D : (2 : ℤ) ∣ D := ⟨d, by rw [hd]; ring⟩
      have h2g : (2 : ℤ) ∣ ((Int.gcd T D : ℕ) : ℤ) := Int.dvd_coe_gcd h2T h2D
      have h21 : (2 : ℤ) ∣ 1 := by
        simp [hcop] at h2g
      norm_num at h21
    · exact False.elim (kubert_cover_no_even_odd T D Y hDpos hcop hTeven hDodd h)
  · rcases Int.even_or_odd D with hDeven | hDodd
    · exact False.elim (kubert_cover_no_odd_even T D Y hDpos hcop hTodd hDeven h)
    · exact ⟨hTodd, hDodd⟩

theorem kubert_cover_split_odd_odd (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (hT : Odd T) (hD : Odd D)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ a b : ℤ, T ^ 2 + D ^ 2 = 2 * a ^ 2 ∧
      3 * T ^ 2 - D ^ 2 = 2 * b ^ 2 := by
  rcases hT with ⟨t, rfl⟩
  rcases hD with ⟨d, rfl⟩
  let T0 : ℤ := 2 * t + 1
  let D0 : ℤ := 2 * d + 1
  let A1 : ℤ := 2 * t ^ 2 + 2 * t + 2 * d ^ 2 + 2 * d + 1
  let B1 : ℤ := 6 * t ^ 2 + 6 * t - 2 * d ^ 2 - 2 * d + 1
  have hA : T0 ^ 2 + D0 ^ 2 = 2 * A1 := by
    dsimp [T0, D0, A1]
    ring
  have hB : 3 * T0 ^ 2 - D0 ^ 2 = 2 * B1 := by
    dsimp [T0, D0, B1]
    ring
  have hA1pos : 0 < A1 := by
    dsimp [A1]
    nlinarith [sq_nonneg t, sq_nonneg (t + 1), sq_nonneg d, sq_nonneg (d + 1)]
  have hB1nonneg : 0 ≤ B1 := by
    have hBnonneg := kubert_cover_second_factor_nonnegative T0 D0 Y hDpos h
    nlinarith
  have hYeven : (2 : ℤ) ∣ Y := by
    have h2Y2 : (2 : ℤ) ∣ Y ^ 2 := by
      rw [h, hA, hB]
      exact ⟨2 * A1 * B1, by ring⟩
    exact (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (2 : ℤ)).dvd_of_dvd_pow h2Y2
  rcases hYeven with ⟨C, hC⟩
  have hCeq : C ^ 2 = A1 * B1 := by
    rw [hC, hA, hB] at h
    ring_nf at h
    nlinarith
  have hA1odd : ¬ (2 : ℤ) ∣ A1 := by
    rintro ⟨c, hc⟩
    dsimp [A1] at hc
    omega
  have hcopA1B1 : Int.gcd A1 B1 = 1 := by
    let gN : ℕ := Int.gcd A1 B1
    let g : ℤ := (gN : ℤ)
    have hgA : g ∣ A1 := by simpa [g, gN] using Int.gcd_dvd_left A1 B1
    have hgB : g ∣ B1 := by simpa [g, gN] using Int.gcd_dvd_right A1 B1
    have hgOdd : ¬ (2 : ℤ) ∣ g := by
      intro h2g
      exact hA1odd (h2g.trans hgA)
    have hgcdg2 : Int.gcd g 2 = 1 := by
      apply gcd_eq_one_of_dvd_four_of_odd_left
      · exact (Int.gcd_dvd_right g 2).trans (show ((2 : ℕ) : ℤ) ∣ (4 : ℤ) by norm_num)
      · exact hgOdd
    have hg2T : g ∣ 2 * T0 ^ 2 := by
      have hsum : g ∣ A1 + B1 := dvd_add hgA hgB
      convert hsum using 1
      dsimp [T0, A1, B1]
      ring
    have hgT : g ∣ T0 ^ 2 := by
      have hprod : g ∣ T0 ^ 2 * 2 := by
        convert hg2T using 1
        ring
      exact Int.dvd_of_dvd_mul_left_of_gcd_one hprod hgcdg2
    have hg2D : g ∣ 2 * D0 ^ 2 := by
      have h3A : g ∣ 3 * A1 := dvd_mul_of_dvd_right hgA 3
      have hsub : g ∣ 3 * A1 - B1 := dvd_sub h3A hgB
      convert hsub using 1
      dsimp [D0, A1, B1]
      ring
    have hgD : g ∣ D0 ^ 2 := by
      have hprod : g ∣ D0 ^ 2 * 2 := by
        convert hg2D using 1
        ring
      exact Int.dvd_of_dvd_mul_left_of_gcd_one hprod hgcdg2
    have hT0D0 : IsCoprime T0 D0 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [T0, D0] using hcop
    have hT2D2 : Int.gcd (T0 ^ 2) (D0 ^ 2) = 1 := by
      exact Int.isCoprime_iff_gcd_eq_one.mp ((hT0D0.pow_left).pow_right)
    have hg1 : g ∣ (1 : ℤ) := by
      have hg_gcd : g ∣ ((Int.gcd (T0 ^ 2) (D0 ^ 2) : ℕ) : ℤ) :=
        Int.dvd_coe_gcd hgT hgD
      simpa [hT2D2] using hg_gcd
    have hgN1 : gN = 1 := by
      have hg1' : ((gN : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa [g] using hg1
      have hgNdiv1 : gN ∣ 1 := by exact_mod_cast hg1'
      exact Nat.dvd_one.mp hgNdiv1
    simpa [gN] using hgN1
  obtain ⟨a, ha | ha⟩ := Int.sq_of_gcd_eq_one hcopA1B1 hCeq.symm
  · have hcop' : Int.gcd B1 A1 = 1 := by rw [Int.gcd_comm]; exact hcopA1B1
    have hCeq' : B1 * A1 = C ^ 2 := by rw [hCeq]; ring
    obtain ⟨b, hb | hb⟩ := Int.sq_of_gcd_eq_one hcop' hCeq'
    · refine ⟨a, b, ?_, ?_⟩
      · rw [hA, ha]
      · rw [hB, hb]
    · have hb0 : b = 0 := by nlinarith [sq_nonneg b]
      refine ⟨a, b, ?_, ?_⟩
      · rw [hA, ha]
      · rw [hB]
        have hB10 : B1 = 0 := by
          rw [hb0] at hb
          simpa using hb
        rw [hB10, hb0]
        ring
  · nlinarith [sq_nonneg a]

theorem kubert_cover_split_primitive (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ a b : ℤ, T ^ 2 + D ^ 2 = 2 * a ^ 2 ∧
      3 * T ^ 2 - D ^ 2 = 2 * b ^ 2 := by
  obtain ⟨hT, hD⟩ := kubert_cover_odd_odd T D Y hDpos hcop h
  exact kubert_cover_split_odd_odd T D Y hDpos hcop hT hD h

theorem kubert_cover_pq_model (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ p q a b : ℤ,
      T = p + q ∧ D = p - q ∧
      p ^ 2 + q ^ 2 = a ^ 2 ∧
      p ^ 2 + 4 * p * q + q ^ 2 = b ^ 2 := by
  obtain ⟨hT, hD⟩ := kubert_cover_odd_odd T D Y hDpos hcop h
  obtain ⟨a, b, hA, hB⟩ := kubert_cover_split_odd_odd T D Y hDpos hcop hT hD h
  rcases hT with ⟨t, ht⟩
  rcases hD with ⟨d, hd⟩
  refine ⟨t + d + 1, t - d, a, b, ?_, ?_, ?_, ?_⟩
  · rw [ht]
    ring
  · rw [hd]
    ring
  · rw [ht, hd] at hA
    have hidentity :
        2 * ((t + d + 1) ^ 2 + (t - d) ^ 2) =
          (2 * t + 1) ^ 2 + (2 * d + 1) ^ 2 := by ring
    nlinarith
  · rw [ht, hd] at hB
    have hidentity :
        2 * ((t + d + 1) ^ 2 + 4 * (t + d + 1) * (t - d) + (t - d) ^ 2) =
          3 * (2 * t + 1) ^ 2 - (2 * d + 1) ^ 2 := by ring
    nlinarith

theorem kubert_cover_pq_model_primitive (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ p q a b : ℤ,
      T = p + q ∧ D = p - q ∧
      p ^ 2 + q ^ 2 = a ^ 2 ∧
      p ^ 2 + 4 * p * q + q ^ 2 = b ^ 2 ∧
      Int.gcd p q = 1 ∧
      ((Even p ∧ Odd q) ∨ (Odd p ∧ Even q)) := by
  obtain ⟨hT, hD⟩ := kubert_cover_odd_odd T D Y hDpos hcop h
  obtain ⟨a, b, hA, hB⟩ := kubert_cover_split_odd_odd T D Y hDpos hcop hT hD h
  rcases hT with ⟨t, ht⟩
  rcases hD with ⟨d, hd⟩
  let p : ℤ := t + d + 1
  let q : ℤ := t - d
  have hpq_gcd : Int.gcd p q = 1 := by
    let gN : ℕ := Int.gcd p q
    let g : ℤ := (gN : ℤ)
    have hgp : g ∣ p := by simpa [g, gN] using Int.gcd_dvd_left p q
    have hgq : g ∣ q := by simpa [g, gN] using Int.gcd_dvd_right p q
    have hgT : g ∣ T := by
      have hsum : g ∣ p + q := dvd_add hgp hgq
      rw [ht]
      convert hsum using 1
      dsimp [p, q]
      ring
    have hgD : g ∣ D := by
      have hsub : g ∣ p - q := dvd_sub hgp hgq
      rw [hd]
      convert hsub using 1
      dsimp [p, q]
      ring
    have hg1 : g ∣ (1 : ℤ) := by
      have hg_gcd : g ∣ ((Int.gcd T D : ℕ) : ℤ) := Int.dvd_coe_gcd hgT hgD
      simpa [hcop] using hg_gcd
    have hgN1 : gN = 1 := by
      have hg1' : ((gN : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa [g] using hg1
      have hgNdiv1 : gN ∣ 1 := by exact_mod_cast hg1'
      exact Nat.dvd_one.mp hgNdiv1
    simpa [gN] using hgN1
  have hpq_parity : (Even p ∧ Odd q) ∨ (Odd p ∧ Even q) := by
    rcases Int.even_or_odd p with hp_even | hp_odd
    · rcases Int.even_or_odd q with hq_even | hq_odd
      · exfalso
        rcases hp_even with ⟨p0, hp0⟩
        rcases hq_even with ⟨q0, hq0⟩
        rw [ht] at *
        dsimp [p, q] at hp0 hq0
        have : 2 * t + 1 = 2 * (p0 + q0) := by
          calc
            2 * t + 1 = p + q := by dsimp [p, q]; ring
            _ = 2 * (p0 + q0) := by
              dsimp [p, q]
              rw [hp0, hq0]
              ring
        omega
      · exact Or.inl ⟨hp_even, hq_odd⟩
    · rcases Int.even_or_odd q with hq_even | hq_odd
      · exact Or.inr ⟨hp_odd, hq_even⟩
      · exfalso
        rcases hp_odd with ⟨p0, hp0⟩
        rcases hq_odd with ⟨q0, hq0⟩
        rw [ht] at *
        dsimp [p, q] at hp0 hq0
        have : 2 * t + 1 = 2 * (p0 + q0 + 1) := by
          calc
            2 * t + 1 = p + q := by dsimp [p, q]; ring
            _ = 2 * (p0 + q0 + 1) := by
              dsimp [p, q]
              rw [hp0, hq0]
              ring
        omega
  refine ⟨p, q, a, b, ?_, ?_, ?_, ?_, hpq_gcd, hpq_parity⟩
  · rw [ht]
    dsimp [p, q]
    ring
  · rw [hd]
    dsimp [p, q]
    ring
  · rw [ht, hd] at hA
    have hidentity :
        2 * (p ^ 2 + q ^ 2) =
          (2 * t + 1) ^ 2 + (2 * d + 1) ^ 2 := by
      dsimp [p, q]
      ring
    nlinarith
  · rw [ht, hd] at hB
    have hidentity :
        2 * (p ^ 2 + 4 * p * q + q ^ 2) =
          3 * (2 * t + 1) ^ 2 - (2 * d + 1) ^ 2 := by
      dsimp [p, q]
      ring
    nlinarith

def pythagoreanQuarticRhs (m n : ℤ) : ℤ :=
  m ^ 4 + 8 * m ^ 3 * n + 2 * m ^ 2 * n ^ 2 - 8 * m * n ^ 3 + n ^ 4

def pythagoreanQuarticCenter (m n : ℤ) : ℤ :=
  m ^ 2 + 4 * m * n - n ^ 2

theorem pythagorean_quartic_difference (m n : ℤ) :
    pythagoreanQuarticCenter m n ^ 2 - pythagoreanQuarticRhs m n =
      12 * m ^ 2 * n ^ 2 := by
  dsimp [pythagoreanQuarticCenter, pythagoreanQuarticRhs]
  ring

theorem pythagorean_quartic_center_square_sub (m n : ℤ) :
    pythagoreanQuarticCenter m n ^ 2 - 12 * (m * n) ^ 2 =
      pythagoreanQuarticRhs m n := by
  dsimp [pythagoreanQuarticCenter, pythagoreanQuarticRhs]
  ring

theorem pythagorean_quartic_factorization (m n b : ℤ)
    (hb : b ^ 2 = pythagoreanQuarticRhs m n) :
    (pythagoreanQuarticCenter m n - b) *
      (pythagoreanQuarticCenter m n + b) = 12 * m ^ 2 * n ^ 2 := by
  calc
    (pythagoreanQuarticCenter m n - b) *
        (pythagoreanQuarticCenter m n + b) =
          pythagoreanQuarticCenter m n ^ 2 - b ^ 2 := by ring
    _ = pythagoreanQuarticCenter m n ^ 2 - pythagoreanQuarticRhs m n := by rw [hb]
    _ = 12 * m ^ 2 * n ^ 2 := pythagorean_quartic_difference m n

private theorem even_of_mod_two_eq_zero {z : ℤ} (hz : z % 2 = 0) : Even z := by
  refine ⟨z / 2, ?_⟩
  omega

private theorem odd_of_mod_two_eq_one {z : ℤ} (hz : z % 2 = 1) : Odd z := by
  refine ⟨z / 2, ?_⟩
  omega

theorem pythagorean_quartic_center_odd_of_opposite_mod (m n : ℤ)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Odd (pythagoreanQuarticCenter m n) := by
  rcases hpar with hpar | hpar
  · have hm := even_of_mod_two_eq_zero hpar.1
    have hn := odd_of_mod_two_eq_one hpar.2
    rcases hm with ⟨a, hm⟩
    rcases hn with ⟨c, hn⟩
    rw [hm, hn]
    dsimp [pythagoreanQuarticCenter]
    refine ⟨-1 + 4 * a + 8 * a * c + 2 * a ^ 2 - 2 * c - 2 * c ^ 2, ?_⟩
    ring
  · have hm := odd_of_mod_two_eq_one hpar.1
    have hn := even_of_mod_two_eq_zero hpar.2
    rcases hm with ⟨a, hm⟩
    rcases hn with ⟨c, hn⟩
    rw [hm, hn]
    dsimp [pythagoreanQuarticCenter]
    refine ⟨2 * a + 8 * a * c + 2 * a ^ 2 + 4 * c - 2 * c ^ 2, ?_⟩
    ring

theorem pythagorean_quartic_rhs_odd_of_opposite_mod (m n : ℤ)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Odd (pythagoreanQuarticRhs m n) := by
  rcases hpar with hpar | hpar
  · have hm := even_of_mod_two_eq_zero hpar.1
    have hn := odd_of_mod_two_eq_one hpar.2
    rcases hm with ⟨a, hm⟩
    rcases hn with ⟨c, hn⟩
    rw [hm, hn]
    dsimp [pythagoreanQuarticRhs]
    refine ⟨-8 * a - 48 * a * c - 96 * a * c ^ 2 - 64 * a * c ^ 3 + 4 * a ^ 2 +
      16 * a ^ 2 * c + 16 * a ^ 2 * c ^ 2 + 32 * a ^ 3 + 64 * a ^ 3 * c +
      8 * a ^ 4 + 4 * c + 12 * c ^ 2 + 16 * c ^ 3 + 8 * c ^ 4, ?_⟩
    ring
  · have hm := odd_of_mod_two_eq_one hpar.1
    have hn := even_of_mod_two_eq_zero hpar.2
    rcases hm with ⟨a, hm⟩
    rcases hn with ⟨c, hn⟩
    rw [hm, hn]
    dsimp [pythagoreanQuarticRhs]
    refine ⟨4 * a + 48 * a * c + 16 * a * c ^ 2 - 64 * a * c ^ 3 + 12 * a ^ 2 +
      96 * a ^ 2 * c + 16 * a ^ 2 * c ^ 2 + 16 * a ^ 3 + 64 * a ^ 3 * c +
      8 * a ^ 4 + 8 * c + 4 * c ^ 2 - 32 * c ^ 3 + 8 * c ^ 4, ?_⟩
    ring

theorem pythagorean_quartic_b_odd_of_opposite_mod (m n b : ℤ)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (hb : b ^ 2 = pythagoreanQuarticRhs m n) : Odd b := by
  have hF := pythagorean_quartic_rhs_odd_of_opposite_mod m n hpar
  rcases Int.even_or_odd b with hb_even | hb_odd
  · exfalso
    rcases hb_even with ⟨c, hc⟩
    rcases hF with ⟨d, hd⟩
    rw [hc, hd] at hb
    ring_nf at hb
    omega
  · exact hb_odd

theorem pythagorean_quartic_half_factorization_of_opposite_mod (m n b : ℤ)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (hb : b ^ 2 = pythagoreanQuarticRhs m n) :
    ∃ r s : ℤ,
      pythagoreanQuarticCenter m n - b = 2 * r ∧
      pythagoreanQuarticCenter m n + b = 2 * s ∧
      r * s = 3 * m ^ 2 * n ^ 2 := by
  have hH := pythagorean_quartic_center_odd_of_opposite_mod m n hpar
  have hbodd := pythagorean_quartic_b_odd_of_opposite_mod m n b hpar hb
  rcases hH with ⟨u, hu⟩
  rcases hbodd with ⟨v, hv⟩
  refine ⟨u - v, u + v + 1, ?_, ?_, ?_⟩
  · rw [hu, hv]
    ring
  · rw [hu, hv]
    ring
  · have hf := pythagorean_quartic_factorization m n b hb
    rw [hu, hv] at hf
    ring_nf at hf ⊢
    nlinarith

theorem pythagorean_quartic_center_coprime_m (m n : ℤ)
    (hcop : Int.gcd m n = 1) :
    IsCoprime (pythagoreanQuarticCenter m n) m := by
  have hmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hnm : IsCoprime n m := hmn.symm
  have hn2m : IsCoprime (n ^ 2) m := hnm.pow_left
  have hneg : IsCoprime (-(n ^ 2)) m := hn2m.neg_left
  have h' : IsCoprime (-(n ^ 2) + m * (m + 4 * n)) m := hneg.add_mul_left_left _
  convert h' using 1
  dsimp [pythagoreanQuarticCenter]
  ring

theorem pythagorean_quartic_center_coprime_n (m n : ℤ)
    (hcop : Int.gcd m n = 1) :
    IsCoprime (pythagoreanQuarticCenter m n) n := by
  have hmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hm2n : IsCoprime (m ^ 2) n := hmn.pow_left
  have h' : IsCoprime (m ^ 2 + n * (4 * m - n)) n := hm2n.add_mul_left_left _
  convert h' using 1
  dsimp [pythagoreanQuarticCenter]
  ring

theorem pythagorean_quartic_center_coprime_m2n2 (m n : ℤ)
    (hcop : Int.gcd m n = 1) :
    IsCoprime (pythagoreanQuarticCenter m n) (m ^ 2 * n ^ 2) := by
  have hm := pythagorean_quartic_center_coprime_m m n hcop
  have hn := pythagorean_quartic_center_coprime_n m n hcop
  have hprod : IsCoprime (pythagoreanQuarticCenter m n) (m * n) := hm.mul_right hn
  have hpow : IsCoprime (pythagoreanQuarticCenter m n) ((m * n) ^ 2) := hprod.pow_right
  convert hpow using 1
  ring

theorem pythagorean_quartic_half_factor_gcd_dvd_three (m n b r s : ℤ)
    (hcop : Int.gcd m n = 1)
    (hr : pythagoreanQuarticCenter m n - b = 2 * r)
    (hs : pythagoreanQuarticCenter m n + b = 2 * s)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2) :
    ((Int.gcd r s : ℕ) : ℤ) ∣ (3 : ℤ) := by
  let gN : ℕ := Int.gcd r s
  let g : ℤ := (gN : ℤ)
  have hgr : g ∣ r := by simpa [g, gN] using Int.gcd_dvd_left r s
  have hgs : g ∣ s := by simpa [g, gN] using Int.gcd_dvd_right r s
  have hHsum : pythagoreanQuarticCenter m n = r + s := by omega
  have hgH : g ∣ pythagoreanQuarticCenter m n := by
    have hsum : g ∣ r + s := dvd_add hgr hgs
    rwa [hHsum]
  have hgprod : g ∣ 3 * m ^ 2 * n ^ 2 := by
    rw [← hrs]
    exact dvd_mul_of_dvd_left hgr s
  have hcenter_cop := pythagorean_quartic_center_coprime_m2n2 m n hcop
  have hg_cop : IsCoprime g (m ^ 2 * n ^ 2) :=
    coprime_of_dvd_left hcenter_cop hgH
  have hgcd : Int.gcd g (m ^ 2 * n ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hg_cop
  have hgprod' : g ∣ 3 * (m ^ 2 * n ^ 2) := by
    convert hgprod using 1
    ring
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hgprod' hgcd

theorem pythagorean_quartic_half_factor_gcd_eq_one_or_three (m n b r s : ℤ)
    (hcop : Int.gcd m n = 1)
    (hr : pythagoreanQuarticCenter m n - b = 2 * r)
    (hs : pythagoreanQuarticCenter m n + b = 2 * s)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2) :
    Int.gcd r s = 1 ∨ Int.gcd r s = 3 := by
  have hdiv := pythagorean_quartic_half_factor_gcd_dvd_three m n b r s hcop hr hs hrs
  let d : ℕ := Int.gcd r s
  have hdNat : d ∣ 3 := by
    have h' : (d : ℤ) ∣ (3 : ℤ) := by simpa [d] using hdiv
    exact_mod_cast h'
  have hprime : Nat.Prime 3 := by norm_num
  have hd := (Nat.dvd_prime hprime).mp hdNat
  simpa [d] using hd

theorem pythagorean_quartic_half_factor_split_of_gcd_one (m n r s : ℤ)
    (hgcd : Int.gcd r s = 1)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2) :
    (∃ a b : ℤ, (r = 3 * a ^ 2 ∨ r = -(3 * a ^ 2)) ∧
      (s = b ^ 2 ∨ s = -(b ^ 2))) ∨
    (∃ a b : ℤ, (r = a ^ 2 ∨ r = -(a ^ 2)) ∧
      (s = 3 * b ^ 2 ∨ s = -(3 * b ^ 2))) := by
  have h3prod : (3 : ℤ) ∣ r * s := by
    rw [hrs]
    exact ⟨m ^ 2 * n ^ 2, by ring⟩
  have hp : Prime (3 : ℤ) := by norm_num
  have hcop : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hsq : 3 * m ^ 2 * n ^ 2 = 3 * (m * n) ^ 2 := by ring
  rcases hp.dvd_or_dvd h3prod with h3r | h3s
  · rcases h3r with ⟨r0, hr0⟩
    have hcop0 : Int.gcd r0 s = 1 := by
      have hcop0' : IsCoprime r0 s :=
        coprime_of_dvd_left hcop ⟨3, by rw [hr0]; ring⟩
      exact Int.isCoprime_iff_gcd_eq_one.mp hcop0'
    have h0 : r0 * s = (m * n) ^ 2 := by
      rw [hr0, hsq] at hrs
      ring_nf at hrs ⊢
      nlinarith
    obtain ⟨a, ha⟩ := Int.sq_of_gcd_eq_one hcop0 h0
    have hcop0' : Int.gcd s r0 = 1 := by rw [Int.gcd_comm]; exact hcop0
    have h0' : s * r0 = (m * n) ^ 2 := by rw [mul_comm]; exact h0
    obtain ⟨b, hb⟩ := Int.sq_of_gcd_eq_one hcop0' h0'
    left
    refine ⟨a, b, ?_, hb⟩
    rcases ha with ha | ha
    · left
      rw [hr0, ha]
    · right
      rw [hr0, ha]
      ring
  · rcases h3s with ⟨s0, hs0⟩
    have hcop0 : Int.gcd r s0 = 1 := by
      have hcop0' : IsCoprime s0 r :=
        coprime_of_dvd_left hcop.symm ⟨3, by rw [hs0]; ring⟩
      have hcop0'' : IsCoprime r s0 := hcop0'.symm
      exact Int.isCoprime_iff_gcd_eq_one.mp hcop0''
    have h0 : r * s0 = (m * n) ^ 2 := by
      rw [hs0, hsq] at hrs
      ring_nf at hrs ⊢
      nlinarith
    obtain ⟨a, ha⟩ := Int.sq_of_gcd_eq_one hcop0 h0
    have hcop0' : Int.gcd s0 r = 1 := by rw [Int.gcd_comm]; exact hcop0
    have h0' : s0 * r = (m * n) ^ 2 := by rw [mul_comm]; exact h0
    obtain ⟨b, hb⟩ := Int.sq_of_gcd_eq_one hcop0' h0'
    right
    refine ⟨a, b, ha, ?_⟩
    rcases hb with hb | hb
    · left
      rw [hs0, hb]
    · right
      rw [hs0, hb]
      ring

theorem pythagorean_quartic_half_factor_three_dvd_parameter_of_gcd_three
    (m n r s : ℤ)
    (hgcd : Int.gcd r s = 3)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2) :
    (3 : ℤ) ∣ m ∨ (3 : ℤ) ∣ n := by
  have h3r : (3 : ℤ) ∣ r := by
    have h := Int.gcd_dvd_left r s
    simpa [hgcd] using h
  have h3s : (3 : ℤ) ∣ s := by
    have h := Int.gcd_dvd_right r s
    simpa [hgcd] using h
  have h9 : (9 : ℤ) ∣ r * s := by
    rcases h3r with ⟨a, ha⟩
    rcases h3s with ⟨c, hc⟩
    refine ⟨a * c, ?_⟩
    rw [ha, hc]
    ring
  have h3mn2 : (3 : ℤ) ∣ m ^ 2 * n ^ 2 := by
    rcases h9 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hrs] at hk
    ring_nf at hk ⊢
    nlinarith
  have hp : Prime (3 : ℤ) := by norm_num
  rcases hp.dvd_or_dvd h3mn2 with hm2 | hn2
  · left
    exact hp.dvd_of_dvd_pow hm2
  · right
    exact hp.dvd_of_dvd_pow hn2

private theorem coprime_not_common_three (m n : ℤ) (hcop : Int.gcd m n = 1)
    (h3m : (3 : ℤ) ∣ m) (h3n : (3 : ℤ) ∣ n) : False := by
  have h3g : (3 : ℤ) ∣ ((Int.gcd m n : ℕ) : ℤ) := Int.dvd_coe_gcd h3m h3n
  rw [hcop] at h3g
  norm_num at h3g

theorem pythagorean_quartic_half_factor_gcd_ne_three (m n b r s : ℤ)
    (hcop : Int.gcd m n = 1)
    (hr : pythagoreanQuarticCenter m n - b = 2 * r)
    (hs : pythagoreanQuarticCenter m n + b = 2 * s)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2) :
    Int.gcd r s ≠ 3 := by
  intro hgcd
  have hthree_dvd_parameter :=
    pythagorean_quartic_half_factor_three_dvd_parameter_of_gcd_three
      m n r s hgcd hrs
  have h3r : (3 : ℤ) ∣ r := by
    have h := Int.gcd_dvd_left r s
    simpa [hgcd] using h
  have h3s : (3 : ℤ) ∣ s := by
    have h := Int.gcd_dvd_right r s
    simpa [hgcd] using h
  have hHsum : pythagoreanQuarticCenter m n = r + s := by omega
  have h3H : (3 : ℤ) ∣ pythagoreanQuarticCenter m n := by
    rw [hHsum]
    exact dvd_add h3r h3s
  have hp : Prime (3 : ℤ) := by norm_num
  rcases hthree_dvd_parameter with h3m | h3n
  · have h3m2 : (3 : ℤ) ∣ m ^ 2 := by
      rcases h3m with ⟨k, hk⟩
      refine ⟨3 * k ^ 2, ?_⟩
      rw [hk]
      ring
    have h3mn : (3 : ℤ) ∣ 4 * m * n := by
      rcases h3m with ⟨k, hk⟩
      refine ⟨4 * k * n, ?_⟩
      rw [hk]
      ring
    have h3left : (3 : ℤ) ∣ m ^ 2 + 4 * m * n := dvd_add h3m2 h3mn
    have h3n2 : (3 : ℤ) ∣ n ^ 2 := by
      have hsub : (3 : ℤ) ∣ (m ^ 2 + 4 * m * n) - pythagoreanQuarticCenter m n :=
        dvd_sub h3left h3H
      convert hsub using 1
      dsimp [pythagoreanQuarticCenter]
      ring
    have h3n : (3 : ℤ) ∣ n := hp.dvd_of_dvd_pow h3n2
    exact coprime_not_common_three m n hcop h3m h3n
  · have h3n2 : (3 : ℤ) ∣ n ^ 2 := by
      rcases h3n with ⟨k, hk⟩
      refine ⟨3 * k ^ 2, ?_⟩
      rw [hk]
      ring
    have h3mn : (3 : ℤ) ∣ 4 * m * n := by
      rcases h3n with ⟨k, hk⟩
      refine ⟨4 * m * k, ?_⟩
      rw [hk]
      ring
    have h3right : (3 : ℤ) ∣ 4 * m * n - n ^ 2 := dvd_sub h3mn h3n2
    have h3m2 : (3 : ℤ) ∣ m ^ 2 := by
      have hsub : (3 : ℤ) ∣ pythagoreanQuarticCenter m n - (4 * m * n - n ^ 2) :=
        dvd_sub h3H h3right
      convert hsub using 1
      dsimp [pythagoreanQuarticCenter]
      ring
    have h3m : (3 : ℤ) ∣ m := hp.dvd_of_dvd_pow h3m2
    exact coprime_not_common_three m n hcop h3m h3n

theorem pythagorean_quartic_half_factor_gcd_eq_one (m n b r s : ℤ)
    (hcop : Int.gcd m n = 1)
    (hr : pythagoreanQuarticCenter m n - b = 2 * r)
    (hs : pythagoreanQuarticCenter m n + b = 2 * s)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2) :
    Int.gcd r s = 1 := by
  have hcases := pythagorean_quartic_half_factor_gcd_eq_one_or_three m n b r s
    hcop hr hs hrs
  have hne := pythagorean_quartic_half_factor_gcd_ne_three m n b r s hcop hr hs hrs
  rcases hcases with hone | hthree
  · exact hone
  · exact False.elim (hne hthree)

theorem pythagorean_quartic_half_factor_split (m n b r s : ℤ)
    (hcop : Int.gcd m n = 1)
    (hr : pythagoreanQuarticCenter m n - b = 2 * r)
    (hs : pythagoreanQuarticCenter m n + b = 2 * s)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2) :
    ((∃ a c : ℤ, (r = 3 * a ^ 2 ∨ r = -(3 * a ^ 2)) ∧
      (s = c ^ 2 ∨ s = -(c ^ 2))) ∨
    (∃ a c : ℤ, (r = a ^ 2 ∨ r = -(a ^ 2)) ∧
      (s = 3 * c ^ 2 ∨ s = -(3 * c ^ 2)))) := by
  have hgcd_one := pythagorean_quartic_half_factor_gcd_eq_one m n b r s hcop hr hs hrs
  exact pythagorean_quartic_half_factor_split_of_gcd_one m n r s hgcd_one hrs

theorem pythagorean_quartic_half_factor_signed_split_of_nonzero (m n b r s : ℤ)
    (hcop : Int.gcd m n = 1)
    (hr : pythagoreanQuarticCenter m n - b = 2 * r)
    (hs : pythagoreanQuarticCenter m n + b = 2 * s)
    (hrs : r * s = 3 * m ^ 2 * n ^ 2)
    (hmn : m * n ≠ 0) :
    ((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
      (r = -(3 * a ^ 2) ∧ s = -(c ^ 2))) ∨
    (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
      (r = -(a ^ 2) ∧ s = -(3 * c ^ 2)))) := by
  have hsplit := pythagorean_quartic_half_factor_split m n b r s hcop hr hs hrs
  have hpos : 0 < 3 * m ^ 2 * n ^ 2 := by
    have hmn_sq : 0 < (m * n) ^ 2 := sq_pos_of_ne_zero hmn
    nlinarith
  rcases hsplit with hleft | hright
  · rcases hleft with ⟨a, c, hrpos | hrneg, hspos | hsneg⟩
    · left; exact ⟨a, c, Or.inl ⟨hrpos, hspos⟩⟩
    · exfalso
      rw [hrpos, hsneg] at hrs
      nlinarith [sq_nonneg a, sq_nonneg c, hpos]
    · exfalso
      rw [hrneg, hspos] at hrs
      nlinarith [sq_nonneg a, sq_nonneg c, hpos]
    · left; exact ⟨a, c, Or.inr ⟨hrneg, hsneg⟩⟩
  · rcases hright with ⟨a, c, hrpos | hrneg, hspos | hsneg⟩
    · right; exact ⟨a, c, Or.inl ⟨hrpos, hspos⟩⟩
    · exfalso
      rw [hrpos, hsneg] at hrs
      nlinarith [sq_nonneg a, sq_nonneg c, hpos]
    · exfalso
      rw [hrneg, hspos] at hrs
      nlinarith [sq_nonneg a, sq_nonneg c, hpos]
    · right; exact ⟨a, c, Or.inr ⟨hrneg, hsneg⟩⟩

theorem pythagorean_quartic_axis_of_zero_product (m n : ℤ)
    (hcop : Int.gcd m n = 1) (hzero : m * n = 0) :
    (m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1) := by
  rcases mul_eq_zero.mp hzero with hm | hn
  · right
    refine ⟨hm, ?_⟩
    have hnat : n.natAbs = 1 := by
      simpa [hm, Int.gcd_zero_left] using hcop
    rcases Int.natAbs_eq_iff.mp hnat with hn | hn <;> rw [hn] <;> norm_num
  · left
    refine ⟨?_, hn⟩
    have hnat : m.natAbs = 1 := by
      simpa [hn, Int.gcd_zero_right] using hcop
    rcases Int.natAbs_eq_iff.mp hnat with hm | hm <;> rw [hm] <;> norm_num

theorem pythagorean_quartic_residual_reduction (m n b : ℤ)
    (hcop : Int.gcd m n = 1)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (hb : b ^ 2 = pythagoreanQuarticRhs m n) :
    ((m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1)) ∨
      ∃ r s : ℤ,
        pythagoreanQuarticCenter m n - b = 2 * r ∧
        pythagoreanQuarticCenter m n + b = 2 * s ∧
        r * s = 3 * m ^ 2 * n ^ 2 ∧
        Int.gcd r s = 1 ∧
        (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
          (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
        (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
          (r = -(a ^ 2) ∧ s = -(3 * c ^ 2)))) := by
  obtain ⟨r, s, hr, hs, hrs⟩ :=
    pythagorean_quartic_half_factorization_of_opposite_mod m n b hpar hb
  by_cases hzero : m * n = 0
  · left
    exact pythagorean_quartic_axis_of_zero_product m n hcop hzero
  · right
    have hgcd_one := pythagorean_quartic_half_factor_gcd_eq_one m n b r s hcop hr hs hrs
    have hsigned :=
      pythagorean_quartic_half_factor_signed_split_of_nonzero m n b r s
        hcop hr hs hrs hzero
    exact ⟨r, s, hr, hs, hrs, hgcd_one, hsigned⟩

theorem pythagorean_axis_param_p_or_q_zero (p q m n : ℤ)
    (hparam : ((p = m ^ 2 - n ^ 2 ∧ q = 2 * m * n) ∨
        (p = 2 * m * n ∧ q = m ^ 2 - n ^ 2)))
    (haxis : (m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1)) :
    p = 0 ∨ q = 0 := by
  rcases hparam with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · right
    rcases haxis with haxis | haxis
    · rw [hq, haxis.2]
      ring
    · rw [hq, haxis.1]
      ring
  · left
    rcases haxis with haxis | haxis
    · rw [hp, haxis.2]
      ring
    · rw [hp, haxis.1]
      ring

theorem pq_zero_forces_cover_degenerate (T D p q : ℤ)
    (hT : T = p + q) (hD : D = p - q) (hpq : p = 0 ∨ q = 0) :
    T = D ∨ T = -D := by
  rcases hpq with hp | hq
  · right
    rw [hT, hD, hp]
    ring
  · left
    rw [hT, hD, hq]
    ring

def NonAxisSignedResidual (m n b r s : ℤ) : Prop :=
  m * n ≠ 0 ∧
  Int.gcd m n = 1 ∧
  (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
  b ^ 2 = pythagoreanQuarticRhs m n ∧
  pythagoreanQuarticCenter m n - b = 2 * r ∧
  pythagoreanQuarticCenter m n + b = 2 * s ∧
  r * s = 3 * m ^ 2 * n ^ 2 ∧
  Int.gcd r s = 1 ∧
  ((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
    (r = -(3 * a ^ 2) ∧ s = -(c ^ 2))) ∨
  ∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
    (r = -(a ^ 2) ∧ s = -(3 * c ^ 2)))

def RationalCoverSignedResidual (t : ℚ) : Prop :=
  ∃ T D Y m n b r s : ℤ,
    0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
    Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) ∧
    NonAxisSignedResidual m n b r s

theorem nonAxisSignedResidual_product_sign {m n b r s : ℤ}
    (hres : NonAxisSignedResidual m n b r s) :
    ∃ a c : ℤ, a * c = m * n ∨ a * c = -(m * n) := by
  rcases hres with
    ⟨_hmn_nonzero, _hcop, _hpar, _hb, _hr, _hs, hrs, _hgcd_one, hsigned⟩
  rcases hsigned with hthree | hone
  · rcases hthree with ⟨a, c, hpos | hneg⟩
    · refine ⟨a, c, ?_⟩
      rcases hpos with ⟨hr, hs⟩
      have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
        rw [hr, hs] at hrs
        ring_nf at hrs ⊢
        nlinarith
      exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares
    · refine ⟨a, c, ?_⟩
      rcases hneg with ⟨hr, hs⟩
      have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
        rw [hr, hs] at hrs
        ring_nf at hrs ⊢
        nlinarith
      exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares
  · rcases hone with ⟨a, c, hpos | hneg⟩
    · refine ⟨a, c, ?_⟩
      rcases hpos with ⟨hr, hs⟩
      have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
        rw [hr, hs] at hrs
        ring_nf at hrs ⊢
        nlinarith
      exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares
    · refine ⟨a, c, ?_⟩
      rcases hneg with ⟨hr, hs⟩
      have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
        rw [hr, hs] at hrs
        ring_nf at hrs ⊢
        nlinarith
      exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares

theorem nonAxisSignedResidual_center_product_cases {m n b r s : ℤ}
    (hres : NonAxisSignedResidual m n b r s) :
    ∃ a c : ℤ,
      (a * c = m * n ∨ a * c = -(m * n)) ∧
      (pythagoreanQuarticCenter m n = 3 * a ^ 2 + c ^ 2 ∨
        pythagoreanQuarticCenter m n = -(3 * a ^ 2 + c ^ 2) ∨
        pythagoreanQuarticCenter m n = a ^ 2 + 3 * c ^ 2 ∨
        pythagoreanQuarticCenter m n = -(a ^ 2 + 3 * c ^ 2)) := by
  rcases hres with
    ⟨_, _, _, _, hcL, hcR, hrs, _, hsigned⟩
  have hcenter : pythagoreanQuarticCenter m n = r + s := by linarith
  rcases hsigned with hthree | hone
  · rcases hthree with ⟨a, c, hpos | hneg⟩
    · rcases hpos with ⟨hrval, hsval⟩
      refine ⟨a, c, ?_, ?_⟩
      · have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
          rw [hrval, hsval] at hrs; ring_nf at hrs ⊢; nlinarith
        exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares
      · exact Or.inl (by rw [hcenter, hrval, hsval])
    · rcases hneg with ⟨hrval, hsval⟩
      refine ⟨a, c, ?_, ?_⟩
      · have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
          rw [hrval, hsval] at hrs; ring_nf at hrs ⊢; nlinarith
        exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares
      · exact Or.inr (Or.inl (by rw [hcenter, hrval, hsval]; ring))
  · rcases hone with ⟨a, c, hpos | hneg⟩
    · rcases hpos with ⟨hrval, hsval⟩
      refine ⟨a, c, ?_, ?_⟩
      · have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
          rw [hrval, hsval] at hrs; ring_nf at hrs ⊢; nlinarith
        exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares
      · exact Or.inr (Or.inr (Or.inl (by rw [hcenter, hrval, hsval])))
    · rcases hneg with ⟨hrval, hsval⟩
      refine ⟨a, c, ?_, ?_⟩
      · have hsquares : (a * c) ^ 2 = (m * n) ^ 2 := by
          rw [hrval, hsval] at hrs; ring_nf at hrs ⊢; nlinarith
        exact eq_or_eq_neg_of_sq_eq_sq (a * c) (m * n) hsquares
      · exact Or.inr (Or.inr (Or.inr (by rw [hcenter, hrval, hsval]; ring)))

theorem center_three_positive_factor_identity {m n a c : ℤ}
    (hH : pythagoreanQuarticCenter m n = 3 * a ^ 2 + c ^ 2)
    (hprod : a * c = m * n ∨ a * c = -(m * n)) :
    (a * c = m * n ∧
      (m - n) * (m + n) = (a - c) * (3 * a - c)) ∨
    (a * c = -(m * n) ∧
      (m - n) * (m + n) = (a + c) * (3 * a + c)) := by
  dsimp [pythagoreanQuarticCenter] at hH
  rcases hprod with hac | hac
  · left
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) - (a - c) * (3 * a - c) =
          (m ^ 2 + 4 * m * n - n ^ 2 - (3 * a ^ 2 + c ^ 2)) -
            4 * (m * n - a * c) := by
      ring
    nlinarith
  · right
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) - (a + c) * (3 * a + c) =
          (m ^ 2 + 4 * m * n - n ^ 2 - (3 * a ^ 2 + c ^ 2)) -
            4 * (m * n + a * c) := by
      ring
    nlinarith

theorem center_three_negative_factor_identity {m n a c : ℤ}
    (hH : pythagoreanQuarticCenter m n = -(3 * a ^ 2 + c ^ 2))
    (hprod : a * c = m * n ∨ a * c = -(m * n)) :
    (a * c = m * n ∧
      (m - n) * (m + n) = -((a + c) * (3 * a + c))) ∨
    (a * c = -(m * n) ∧
      (m - n) * (m + n) = -((a - c) * (3 * a - c))) := by
  dsimp [pythagoreanQuarticCenter] at hH
  rcases hprod with hac | hac
  · left
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) + (a + c) * (3 * a + c) =
          (m ^ 2 + 4 * m * n - n ^ 2 + (3 * a ^ 2 + c ^ 2)) -
            4 * (m * n - a * c) := by
      ring
    nlinarith
  · right
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) + (a - c) * (3 * a - c) =
          (m ^ 2 + 4 * m * n - n ^ 2 + (3 * a ^ 2 + c ^ 2)) -
            4 * (m * n + a * c) := by
      ring
    nlinarith

theorem center_one_positive_factor_identity {m n a c : ℤ}
    (hH : pythagoreanQuarticCenter m n = a ^ 2 + 3 * c ^ 2)
    (hprod : a * c = m * n ∨ a * c = -(m * n)) :
    (a * c = m * n ∧
      (m - n) * (m + n) = (a - c) * (a - 3 * c)) ∨
    (a * c = -(m * n) ∧
      (m - n) * (m + n) = (a + c) * (a + 3 * c)) := by
  dsimp [pythagoreanQuarticCenter] at hH
  rcases hprod with hac | hac
  · left
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) - (a - c) * (a - 3 * c) =
          (m ^ 2 + 4 * m * n - n ^ 2 - (a ^ 2 + 3 * c ^ 2)) -
            4 * (m * n - a * c) := by
      ring
    nlinarith
  · right
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) - (a + c) * (a + 3 * c) =
          (m ^ 2 + 4 * m * n - n ^ 2 - (a ^ 2 + 3 * c ^ 2)) -
            4 * (m * n + a * c) := by
      ring
    nlinarith

theorem center_one_negative_factor_identity {m n a c : ℤ}
    (hH : pythagoreanQuarticCenter m n = -(a ^ 2 + 3 * c ^ 2))
    (hprod : a * c = m * n ∨ a * c = -(m * n)) :
    (a * c = m * n ∧
      (m - n) * (m + n) = -((a + c) * (a + 3 * c))) ∨
    (a * c = -(m * n) ∧
      (m - n) * (m + n) = -((a - c) * (a - 3 * c))) := by
  dsimp [pythagoreanQuarticCenter] at hH
  rcases hprod with hac | hac
  · left
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) + (a + c) * (a + 3 * c) =
          (m ^ 2 + 4 * m * n - n ^ 2 + (a ^ 2 + 3 * c ^ 2)) -
            4 * (m * n - a * c) := by
      ring
    nlinarith
  · right
    refine ⟨hac, ?_⟩
    have htarget :
        (m - n) * (m + n) + (a - c) * (a - 3 * c) =
          (m ^ 2 + 4 * m * n - n ^ 2 + (a ^ 2 + 3 * c ^ 2)) -
            4 * (m * n + a * c) := by
      ring
    nlinarith

theorem nonAxisSignedResidual_factor_identity_cases {m n b r s : ℤ}
    (hres : NonAxisSignedResidual m n b r s) :
    ∃ a c : ℤ,
      (a * c = m * n ∧
        ((m - n) * (m + n) = (a - c) * (3 * a - c) ∨
        (m - n) * (m + n) = -((a + c) * (3 * a + c)) ∨
        (m - n) * (m + n) = (a - c) * (a - 3 * c) ∨
        (m - n) * (m + n) = -((a + c) * (a + 3 * c)))) ∨
      (a * c = -(m * n) ∧
        ((m - n) * (m + n) = (a + c) * (3 * a + c) ∨
        (m - n) * (m + n) = -((a - c) * (3 * a - c)) ∨
        (m - n) * (m + n) = (a + c) * (a + 3 * c) ∨
        (m - n) * (m + n) = -((a - c) * (a - 3 * c)))) := by
  obtain ⟨a, c, hprod, hcenter_cases⟩ :=
    nonAxisSignedResidual_center_product_cases hres
  refine ⟨a, c, ?_⟩
  rcases hcenter_cases with hthree_pos | hthree_neg | hone_pos | hone_neg
  · rcases center_three_positive_factor_identity hthree_pos hprod with hfact | hfact
    · left
      exact ⟨hfact.1, Or.inl hfact.2⟩
    · right
      exact ⟨hfact.1, Or.inl hfact.2⟩
  · rcases center_three_negative_factor_identity hthree_neg hprod with hfact | hfact
    · left
      exact ⟨hfact.1, Or.inr (Or.inl hfact.2)⟩
    · right
      exact ⟨hfact.1, Or.inr (Or.inl hfact.2)⟩
  · rcases center_one_positive_factor_identity hone_pos hprod with hfact | hfact
    · left
      exact ⟨hfact.1, Or.inr (Or.inr (Or.inl hfact.2))⟩
    · right
      exact ⟨hfact.1, Or.inr (Or.inr (Or.inl hfact.2))⟩
  · rcases center_one_negative_factor_identity hone_neg hprod with hfact | hfact
    · left
      exact ⟨hfact.1, Or.inr (Or.inr (Or.inr hfact.2))⟩
    · right
      exact ⟨hfact.1, Or.inr (Or.inr (Or.inr hfact.2))⟩

/-- Compact form of the remaining non-axis factor-identity residual. -/
def NonAxisFactorIdentityResidual (m n a c : ℤ) : Prop :=
  (a * c = m * n ∧
    ((m - n) * (m + n) = (a - c) * (3 * a - c) ∨
    (m - n) * (m + n) = -((a + c) * (3 * a + c)) ∨
    (m - n) * (m + n) = (a - c) * (a - 3 * c) ∨
    (m - n) * (m + n) = -((a + c) * (a + 3 * c)))) ∨
  (a * c = -(m * n) ∧
    ((m - n) * (m + n) = (a + c) * (3 * a + c) ∨
    (m - n) * (m + n) = -((a - c) * (3 * a - c)) ∨
    (m - n) * (m + n) = (a + c) * (a + 3 * c) ∨
    (m - n) * (m + n) = -((a - c) * (a - 3 * c))))

def NormalizedNonAxisFactorIdentity (m n A C : ℤ) : Prop :=
  A * C = m * n ∧
    ((m - n) * (m + n) = (A - C) * (3 * A - C) ∨
    (m - n) * (m + n) = -((A + C) * (3 * A + C)) ∨
    (m - n) * (m + n) = (A - C) * (A - 3 * C) ∨
    (m - n) * (m + n) = -((A + C) * (A + 3 * C)))

theorem nonAxisFactorIdentityResidual_normalize {m n a c : ℤ}
    (hres : NonAxisFactorIdentityResidual m n a c) :
    ∃ A C : ℤ, NormalizedNonAxisFactorIdentity m n A C := by
  rcases hres with ⟨hprod, hcases⟩ | ⟨hprod, hcases⟩
  · exact ⟨a, c, hprod, hcases⟩
  · refine ⟨a, -c, ?_, ?_⟩
    · calc
        a * -c = -(a * c) := by ring
        _ = m * n := by rw [hprod]; ring
    · rcases hcases with hfac | hfac | hfac | hfac
      · left
        calc
          (m - n) * (m + n) = (a + c) * (3 * a + c) := hfac
          _ = (a - -c) * (3 * a - -c) := by ring
      · right; left
        calc
          (m - n) * (m + n) = -((a - c) * (3 * a - c)) := hfac
          _ = -((a + -c) * (3 * a + -c)) := by ring
      · right; right; left
        calc
          (m - n) * (m + n) = (a + c) * (a + 3 * c) := hfac
          _ = (a - -c) * (a - 3 * -c) := by ring
      · right; right; right
        calc
          (m - n) * (m + n) = -((a - c) * (a - 3 * c)) := hfac
          _ = -((a + -c) * (a + 3 * -c)) := by ring

def F_N12_AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

def F_N12_XBoundary (X : ℚ) : Prop :=
  X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3

theorem F_N12_rhs_factor (X : ℚ) :
    X ^ 3 + 2 * X ^ 2 - 3 * X = X * (X - 1) * (X + 3) := by
  ring

theorem F_N12_AffineEquation_factor_iff (X Y : ℚ) :
    F_N12_AffineEquation X Y ↔ Y ^ 2 = X * (X - 1) * (X + 3) := by
  unfold F_N12_AffineEquation
  rw [F_N12_rhs_factor]

theorem F_N12_affine_neg_three :
    F_N12_AffineEquation (-3) 0 := by
  norm_num [F_N12_AffineEquation]

theorem F_N12_affine_zero :
    F_N12_AffineEquation 0 0 := by
  norm_num [F_N12_AffineEquation]

theorem F_N12_affine_one :
    F_N12_AffineEquation 1 0 := by
  norm_num [F_N12_AffineEquation]

theorem F_N12_affine_neg_one_pos :
    F_N12_AffineEquation (-1) 2 := by
  norm_num [F_N12_AffineEquation]

theorem F_N12_affine_neg_one_neg :
    F_N12_AffineEquation (-1) (-2) := by
  norm_num [F_N12_AffineEquation]

theorem F_N12_affine_three_pos :
    F_N12_AffineEquation 3 6 := by
  norm_num [F_N12_AffineEquation]

theorem F_N12_affine_three_neg :
    F_N12_AffineEquation 3 (-6) := by
  norm_num [F_N12_AffineEquation]

theorem F_N12_squareclass_substitution_identity {d u v z : ℚ}
    (hd : d ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    F_N12_AffineEquation
        (d * u ^ 2 / v ^ 2)
        (d * u * z / v ^ 3)
      ↔ z ^ 2 = d * u ^ 4 + 2 * u ^ 2 * v ^ 2 - (3 / d) * v ^ 4 := by
  unfold F_N12_AffineEquation
  constructor
  · intro h
    field_simp [hd, hu, hv] at h ⊢
    ring_nf at h ⊢
    exact h
  · intro h
    field_simp [hd, hu, hv] at h ⊢
    ring_nf at h ⊢
    exact h

theorem F_N12_substitution_factor_identity {d u v z : ℚ}
    (hd : d ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    F_N12_AffineEquation
        (d * u ^ 2 / v ^ 2)
        (d * u * z / v ^ 3)
      ↔ d * z ^ 2 = (d * u ^ 2 - v ^ 2) * (d * u ^ 2 + 3 * v ^ 2) := by
  unfold F_N12_AffineEquation
  constructor
  · intro h
    field_simp [hd, hu, hv] at h ⊢
    ring_nf at h ⊢
    exact h
  · intro h
    field_simp [hd, hu, hv] at h ⊢
    ring_nf at h ⊢
    exact h

theorem E_N12_AffineEquation_of_F_N12 {X Y : ℚ}
    (h : F_N12_AffineEquation X Y) :
    MazurProof.E_N12_AffineEquation (X + 1) Y := by
  unfold F_N12_AffineEquation at h
  unfold MazurProof.E_N12_AffineEquation
  nlinarith [show (X + 1) ^ 3 - (X + 1) ^ 2 - 4 * (X + 1) + 4 =
    X ^ 3 + 2 * X ^ 2 - 3 * X by ring]

theorem F_N12_AffineEquation_of_E_N12 {u w : ℚ}
    (h : MazurProof.E_N12_AffineEquation u w) :
    F_N12_AffineEquation (u - 1) w := by
  unfold MazurProof.E_N12_AffineEquation at h
  unfold F_N12_AffineEquation
  nlinarith [show (u - 1) ^ 3 + 2 * (u - 1) ^ 2 - 3 * (u - 1) =
    u ^ 3 - u ^ 2 - 4 * u + 4 by ring]

theorem F_N12_boundary_of_E_N12_degenerate_boundary
    (hEbd : ∀ u w : ℚ,
      MazurProof.E_N12_AffineEquation u w →
      MazurProof.E_N12_DegenerateParameter u)
    {X Y : ℚ}
    (h : F_N12_AffineEquation X Y) :
    X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3 := by
  have hE : MazurProof.E_N12_AffineEquation (X + 1) Y :=
    E_N12_AffineEquation_of_F_N12 h
  have hdeg := hEbd (X + 1) Y hE
  unfold MazurProof.E_N12_DegenerateParameter at hdeg
  rcases hdeg with hneg2 | hzero | hone | htwo | hfour
  · left
    linarith
  · right; right; right; left
    linarith
  · right; left
    linarith
  · right; right; left
    linarith
  · right; right; right; right
    linarith

theorem E_N12_degenerate_boundary_of_F_N12_boundary
    (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
      X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
    (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w) :
    MazurProof.E_N12_DegenerateParameter u := by
  have hF : F_N12_AffineEquation (u - 1) w :=
    F_N12_AffineEquation_of_E_N12 h
  have hbd := hFbd hF
  unfold MazurProof.E_N12_DegenerateParameter
  rcases hbd with hneg3 | hzero | hone | hneg1 | hthree
  · left
    linarith
  · right; right; left
    linarith
  · right; right; right; left
    linarith
  · right; left
    linarith
  · right; right; right; right
    linarith

theorem rat_sq_ne_three (t : ℚ) : t ^ 2 ≠ 3 := by
  intro h
  have hs : IsSquare (3 : ℚ) := ⟨t, by simpa [sq] using h.symm⟩
  have hsint : IsSquare (3 : ℤ) := Rat.isSquare_intCast_iff.mp (by simpa using hs)
  norm_num [IsSquare] at hsint

theorem rat_sq_ne_one_div_three (t : ℚ) : t ^ 2 ≠ (1 / 3 : ℚ) := by
  intro h
  exact rat_sq_ne_three (3 * t) (by
    nlinarith)

theorem branch_B1_to_F {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C)) :
    ∃ Y : ℚ, F_N12_AffineEquation (((m : ℚ) / (A : ℚ)) ^ 2) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (q + 1) * r ^ 2 - 4 * q * r + 3 * q - q ^ 2 = 0 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
    have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
      exact_mod_cast hAC
    have hB1q :
        ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
          ((A : ℚ) - (C : ℚ)) * (3 * (A : ℚ) - (C : ℚ)) := by
      exact_mod_cast hB1
    have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
      rw [hACq]
    have hB1mul :
        ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
          ((m : ℚ) ^ 2) * (((A : ℚ) - (C : ℚ)) * (3 * (A : ℚ) - (C : ℚ))) := by
      rw [hB1q]
    dsimp [q, r]
    field_simp [hAq]
    ring_nf at hACsq hB1mul ⊢
    nlinarith
  refine ⟨(q + 1) * r - 2 * q, ?_⟩
  change F_N12_AffineEquation q ((q + 1) * r - 2 * q)
  dsimp [F_N12_AffineEquation]
  have hzero :
      ((q + 1) * r - 2 * q) ^ 2 - (q ^ 3 + 2 * q ^ 2 - 3 * q) = 0 := by
    calc
      ((q + 1) * r - 2 * q) ^ 2 - (q ^ 3 + 2 * q ^ 2 - 3 * q) =
          (q + 1) * ((q + 1) * r ^ 2 - 4 * q * r + 3 * q - q ^ 2) := by ring
      _ = 0 := by rw [hrel, mul_zero]
  exact sub_eq_zero.mp hzero

theorem branch_B2_to_F {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB2 : (m - n) * (m + n) = -((A + C) * (3 * A + C))) :
    ∃ Y : ℚ, F_N12_AffineEquation (-(((m : ℚ) / (A : ℚ)) ^ 2)) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (q - 1) * r ^ 2 + 4 * q * r + q ^ 2 + 3 * q = 0 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
    have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
      exact_mod_cast hAC
    have hB2q :
        ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
          -(((A : ℚ) + (C : ℚ)) * (3 * (A : ℚ) + (C : ℚ))) := by
      exact_mod_cast hB2
    have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
      rw [hACq]
    have hB2mul :
        ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
          ((m : ℚ) ^ 2) * (-(((A : ℚ) + (C : ℚ)) * (3 * (A : ℚ) + (C : ℚ)))) := by
      rw [hB2q]
    dsimp [q, r]
    field_simp [hAq]
    ring_nf at hACsq hB2mul ⊢
    nlinarith
  refine ⟨(q - 1) * r + 2 * q, ?_⟩
  change F_N12_AffineEquation (-q) ((q - 1) * r + 2 * q)
  dsimp [F_N12_AffineEquation]
  have hzero :
      ((q - 1) * r + 2 * q) ^ 2 - ((-q) ^ 3 + 2 * (-q) ^ 2 - 3 * (-q)) = 0 := by
    calc
      ((q - 1) * r + 2 * q) ^ 2 - ((-q) ^ 3 + 2 * (-q) ^ 2 - 3 * (-q)) =
          (q - 1) * ((q - 1) * r ^ 2 + 4 * q * r + q ^ 2 + 3 * q) := by ring
      _ = 0 := by rw [hrel, mul_zero]
  exact sub_eq_zero.mp hzero

theorem branch_B3_to_F {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB3 : (m - n) * (m + n) = (A - C) * (A - 3 * C)) :
    ∃ Y : ℚ, F_N12_AffineEquation (3 * (((m : ℚ) / (A : ℚ)) ^ 2)) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (3 * q + 1) * r ^ 2 - 4 * q * r + q - q ^ 2 = 0 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
    have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
      exact_mod_cast hAC
    have hB3q :
        ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
          ((A : ℚ) - (C : ℚ)) * ((A : ℚ) - 3 * (C : ℚ)) := by
      exact_mod_cast hB3
    have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
      rw [hACq]
    have hB3mul :
        ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
          ((m : ℚ) ^ 2) * (((A : ℚ) - (C : ℚ)) * ((A : ℚ) - 3 * (C : ℚ))) := by
      rw [hB3q]
    dsimp [q, r]
    field_simp [hAq]
    ring_nf at hACsq hB3mul ⊢
    nlinarith
  refine ⟨3 * ((3 * q + 1) * r - 2 * q), ?_⟩
  change F_N12_AffineEquation (3 * q) (3 * ((3 * q + 1) * r - 2 * q))
  dsimp [F_N12_AffineEquation]
  have hzero :
      (3 * ((3 * q + 1) * r - 2 * q)) ^ 2 -
          ((3 * q) ^ 3 + 2 * (3 * q) ^ 2 - 3 * (3 * q)) = 0 := by
    calc
      (3 * ((3 * q + 1) * r - 2 * q)) ^ 2 -
          ((3 * q) ^ 3 + 2 * (3 * q) ^ 2 - 3 * (3 * q)) =
            9 * (3 * q + 1) * ((3 * q + 1) * r ^ 2 - 4 * q * r + q - q ^ 2) := by ring
      _ = 0 := by rw [hrel, mul_zero]
  exact sub_eq_zero.mp hzero

theorem branch_B4_to_F {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB4 : (m - n) * (m + n) = -((A + C) * (A + 3 * C))) :
    ∃ Y : ℚ, F_N12_AffineEquation (-3 * (((m : ℚ) / (A : ℚ)) ^ 2)) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (3 * q - 1) * r ^ 2 + 4 * q * r + q + q ^ 2 = 0 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
    have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
      exact_mod_cast hAC
    have hB4q :
        ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
          -(((A : ℚ) + (C : ℚ)) * ((A : ℚ) + 3 * (C : ℚ))) := by
      exact_mod_cast hB4
    have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
      rw [hACq]
    have hB4mul :
        ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
          ((m : ℚ) ^ 2) * (-(((A : ℚ) + (C : ℚ)) * ((A : ℚ) + 3 * (C : ℚ)))) := by
      rw [hB4q]
    dsimp [q, r]
    field_simp [hAq]
    ring_nf at hACsq hB4mul ⊢
    nlinarith
  refine ⟨3 * ((3 * q - 1) * r + 2 * q), ?_⟩
  change F_N12_AffineEquation (-3 * q) (3 * ((3 * q - 1) * r + 2 * q))
  dsimp [F_N12_AffineEquation]
  have hzero :
      (3 * ((3 * q - 1) * r + 2 * q)) ^ 2 -
          ((-3 * q) ^ 3 + 2 * (-3 * q) ^ 2 - 3 * (-3 * q)) = 0 := by
    calc
      (3 * ((3 * q - 1) * r + 2 * q)) ^ 2 -
          ((-3 * q) ^ 3 + 2 * (-3 * q) ^ 2 - 3 * (-3 * q)) =
            9 * (3 * q - 1) * ((3 * q - 1) * r ^ 2 + 4 * q * r + q + q ^ 2) := by ring
      _ = 0 := by rw [hrel, mul_zero]
  exact sub_eq_zero.mp hzero

theorem normalizedNonAxisFactorIdentity_to_F {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hres : NormalizedNonAxisFactorIdentity m n A C) :
    ∃ X Y : ℚ,
      F_N12_AffineEquation X Y ∧
      (X = ((m : ℚ) / (A : ℚ)) ^ 2 ∨
        X = -(((m : ℚ) / (A : ℚ)) ^ 2) ∨
        X = 3 * (((m : ℚ) / (A : ℚ)) ^ 2) ∨
        X = -3 * (((m : ℚ) / (A : ℚ)) ^ 2)) := by
  rcases hres with ⟨hAC, hcases⟩
  have hA : A ≠ 0 := by
    intro hAzero
    exact hmn0 (by
      rw [← hAC, hAzero]
      ring)
  rcases hcases with hB1 | hB2 | hB3 | hB4
  · obtain ⟨Y, hF⟩ := branch_B1_to_F hAC hA hB1
    exact ⟨((m : ℚ) / (A : ℚ)) ^ 2, Y, hF, Or.inl rfl⟩
  · obtain ⟨Y, hF⟩ := branch_B2_to_F hAC hA hB2
    exact ⟨-(((m : ℚ) / (A : ℚ)) ^ 2), Y, hF, Or.inr (Or.inl rfl)⟩
  · obtain ⟨Y, hF⟩ := branch_B3_to_F hAC hA hB3
    exact ⟨3 * (((m : ℚ) / (A : ℚ)) ^ 2), Y, hF, Or.inr (Or.inr (Or.inl rfl))⟩
  · obtain ⟨Y, hF⟩ := branch_B4_to_F hAC hA hB4
    exact ⟨-3 * (((m : ℚ) / (A : ℚ)) ^ 2), Y, hF, Or.inr (Or.inr (Or.inr rfl))⟩

theorem nonAxisFactorIdentityResidual_to_F {m n a c : ℤ}
    (hmn0 : m * n ≠ 0)
    (hres : NonAxisFactorIdentityResidual m n a c) :
    ∃ A C : ℤ, ∃ X Y : ℚ,
      NormalizedNonAxisFactorIdentity m n A C ∧
      F_N12_AffineEquation X Y ∧
      (X = ((m : ℚ) / (A : ℚ)) ^ 2 ∨
        X = -(((m : ℚ) / (A : ℚ)) ^ 2) ∨
        X = 3 * (((m : ℚ) / (A : ℚ)) ^ 2) ∨
        X = -3 * (((m : ℚ) / (A : ℚ)) ^ 2)) := by
  obtain ⟨A, C, hnorm⟩ := nonAxisFactorIdentityResidual_normalize hres
  obtain ⟨X, Y, hF, hX⟩ := normalizedNonAxisFactorIdentity_to_F hmn0 hnorm
  exact ⟨A, C, X, Y, hnorm, hF, hX⟩

theorem int_left_ne_zero_of_mul_ne_zero {m n : ℤ} (hmn0 : m * n ≠ 0) : m ≠ 0 := by
  intro hm
  exact hmn0 (by simp [hm])

theorem int_right_ne_zero_of_mul_ne_zero {m n : ℤ} (hmn0 : m * n ≠ 0) : n ≠ 0 := by
  intro hn
  exact hmn0 (by simp [hn])

theorem normal_factor_A_ne_zero {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n) :
    A ≠ 0 := by
  intro hA
  exact hmn0 (by
    rw [← hAC, hA]
    ring)

theorem ratio_sq_ne_zero_of_nonaxis {m n A : ℤ}
    (hmn0 : m * n ≠ 0)
    (hA : A ≠ 0) :
    ((m : ℚ) / (A : ℚ)) ^ 2 ≠ 0 := by
  have hm : m ≠ 0 := int_left_ne_zero_of_mul_ne_zero hmn0
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hAQ : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  exact pow_ne_zero 2 (div_ne_zero hmQ hAQ)

theorem opposite_parity_not_eq {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
    (h : m = n) :
    False := by
  omega

theorem opposite_parity_not_neg {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
    (h : m = -n) :
    False := by
  omega

theorem int_ratio_sq_eq_one_cases {m A : ℤ}
    (hA : A ≠ 0)
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = A ∨ m = -A := by
  have hAQ : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hsq : (m : ℚ) ^ 2 = (A : ℚ) ^ 2 := by
    field_simp [hAQ] at hq
    simpa using hq
  rcases eq_or_eq_neg_of_sq_eq_sq (m : ℚ) (A : ℚ) hsq with hm | hm
  · left
    exact_mod_cast hm
  · right
    exact_mod_cast hm

private theorem same_sign_C_eq_of_ratio_eq_one {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hmA : m = A) :
    C = n := by
  have hm0 : m ≠ 0 := int_left_ne_zero_of_mul_ne_zero hmn0
  have hmul : m * C = m * n := by
    simpa [hmA.symm] using hAC
  exact mul_left_cancel₀ hm0 hmul

private theorem neg_sign_C_eq_of_ratio_eq_one {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hmA : m = -A) :
    C = -n := by
  have hm0 : m ≠ 0 := int_left_ne_zero_of_mul_ne_zero hmn0
  have hmul : m * (-C) = m * n := by
    calc
      m * (-C) = (-m) * C := by ring
      _ = A * C := by rw [hmA]; ring
      _ = m * n := hAC
  have hneg : -C = n := mul_left_cancel₀ hm0 hmul
  omega

theorem branch_B1_q1_forces_m_eq_n {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C))
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = n := by
  have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
  rcases int_ratio_sq_eq_one_cases hA hq with hmA | hmA
  · have hC : C = n := same_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [← hmA, hC] at hB1
    ring_nf at hB1
    nlinarith
  · have hC : C = -n := neg_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [show A = -m by omega, hC] at hB1
    ring_nf at hB1
    nlinarith

theorem branch_B2_q1_forces_m_eq_neg_n {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hB2 : (m - n) * (m + n) = -((A + C) * (3 * A + C)))
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = -n := by
  have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
  have hm0 : m ≠ 0 := int_left_ne_zero_of_mul_ne_zero hmn0
  rcases int_ratio_sq_eq_one_cases hA hq with hmA | hmA
  · have hC : C = n := same_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [← hmA, hC] at hB2
    ring_nf at hB2
    have hprod4 : 4 * (m * (m + n)) = 0 := by
      nlinarith [show 4 * (m * (m + n)) = 4 * m ^ 2 + 4 * (m * n) by ring]
    have hprod : m * (m + n) = 0 := by omega
    rcases mul_eq_zero.mp hprod with hm | hsum
    · exact False.elim (hm0 hm)
    · omega
  · have hC : C = -n := neg_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [show A = -m by omega, hC] at hB2
    ring_nf at hB2
    have hprod4 : 4 * (m * (m + n)) = 0 := by
      nlinarith [show 4 * (m * (m + n)) = 4 * m ^ 2 + 4 * (m * n) by ring]
    have hprod : m * (m + n) = 0 := by omega
    rcases mul_eq_zero.mp hprod with hm | hsum
    · exact False.elim (hm0 hm)
    · omega

theorem branch_B3_q1_forces_m_eq_n {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hB3 : (m - n) * (m + n) = (A - C) * (A - 3 * C))
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = n := by
  have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
  have hn0 : n ≠ 0 := int_right_ne_zero_of_mul_ne_zero hmn0
  rcases int_ratio_sq_eq_one_cases hA hq with hmA | hmA
  · have hC : C = n := same_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [← hmA, hC] at hB3
    ring_nf at hB3
    have hprod4 : 4 * (n * (m - n)) = 0 := by
      nlinarith [show 4 * (n * (m - n)) = 4 * (m * n) - 4 * n ^ 2 by ring]
    have hprod : n * (m - n) = 0 := by omega
    rcases mul_eq_zero.mp hprod with hn | hdiff
    · exact False.elim (hn0 hn)
    · omega
  · have hC : C = -n := neg_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [show A = -m by omega, hC] at hB3
    ring_nf at hB3
    have hprod4 : 4 * (n * (m - n)) = 0 := by
      nlinarith [show 4 * (n * (m - n)) = 4 * (m * n) - 4 * n ^ 2 by ring]
    have hprod : n * (m - n) = 0 := by omega
    rcases mul_eq_zero.mp hprod with hn | hdiff
    · exact False.elim (hn0 hn)
    · omega

theorem branch_B4_q1_forces_m_eq_neg_n {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hB4 : (m - n) * (m + n) = -((A + C) * (A + 3 * C)))
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = -n := by
  have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
  rcases int_ratio_sq_eq_one_cases hA hq with hmA | hmA
  · have hC : C = n := same_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [← hmA, hC] at hB4
    ring_nf at hB4
    nlinarith
  · have hC : C = -n := neg_sign_C_eq_of_ratio_eq_one hmn0 hAC hmA
    rw [show A = -m by omega, hC] at hB4
    ring_nf at hB4
    nlinarith

theorem no_nonAxisFactorIdentityResidual_of_F_boundary
    (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
      X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
    {m n a c : ℤ}
    (hmn0 : m * n ≠ 0)
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
    (hres : NonAxisFactorIdentityResidual m n a c) :
    False := by
  obtain ⟨A, C, hnorm⟩ := nonAxisFactorIdentityResidual_normalize hres
  rcases hnorm with ⟨hAC, hB1 | hB2 | hB3 | hB4⟩
  · have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
    let t : ℚ := (m : ℚ) / (A : ℚ)
    let q : ℚ := t ^ 2
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact sq_nonneg t
    have hq_ne0 : q ≠ 0 := by
      dsimp [q, t]
      exact ratio_sq_ne_zero_of_nonaxis hmn0 hA
    obtain ⟨Y, hF⟩ := branch_B1_to_F hAC hA hB1
    have hFq : F_N12_AffineEquation q Y := by
      simpa [q, t] using hF
    rcases hFbd hFq with hx | hx | hx | hx | hx
    · nlinarith [hq_nonneg]
    · exact hq_ne0 hx
    · have hmn : m = n :=
        branch_B1_q1_forces_m_eq_n hmn0 hAC hB1 (by simpa [q, t] using hx)
      exact opposite_parity_not_eq hpar hmn
    · nlinarith [hq_nonneg]
    · exact rat_sq_ne_three t (by simpa [q, t] using hx)
  · have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
    let t : ℚ := (m : ℚ) / (A : ℚ)
    let q : ℚ := t ^ 2
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact sq_nonneg t
    have hq_ne0 : q ≠ 0 := by
      dsimp [q, t]
      exact ratio_sq_ne_zero_of_nonaxis hmn0 hA
    obtain ⟨Y, hF⟩ := branch_B2_to_F hAC hA hB2
    have hFq : F_N12_AffineEquation (-q) Y := by
      simpa [q, t] using hF
    rcases hFbd hFq with hx | hx | hx | hx | hx
    · have hq3 : q = 3 := by nlinarith
      exact rat_sq_ne_three t (by simpa [q, t] using hq3)
    · have hq0 : q = 0 := by nlinarith
      exact hq_ne0 hq0
    · have hqneg : q = -1 := by nlinarith
      nlinarith [hq_nonneg]
    · have hq1 : q = 1 := by nlinarith
      have hmn : m = -n :=
        branch_B2_q1_forces_m_eq_neg_n hmn0 hAC hB2 (by simpa [q, t] using hq1)
      exact opposite_parity_not_neg hpar hmn
    · have hqneg3 : q = -3 := by nlinarith
      nlinarith [hq_nonneg]
  · have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
    let t : ℚ := (m : ℚ) / (A : ℚ)
    let q : ℚ := t ^ 2
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact sq_nonneg t
    have hq_ne0 : q ≠ 0 := by
      dsimp [q, t]
      exact ratio_sq_ne_zero_of_nonaxis hmn0 hA
    obtain ⟨Y, hF⟩ := branch_B3_to_F hAC hA hB3
    have hFq : F_N12_AffineEquation (3 * q) Y := by
      simpa [q, t] using hF
    rcases hFbd hFq with hx | hx | hx | hx | hx
    · have hqneg : q = -1 := by nlinarith
      nlinarith [hq_nonneg]
    · have hq0 : q = 0 := by nlinarith
      exact hq_ne0 hq0
    · have hq13 : q = 1 / 3 := by nlinarith
      exact rat_sq_ne_one_div_three t (by simpa [q, t] using hq13)
    · have hqneg13 : q = -(1 / 3) := by nlinarith
      nlinarith [hq_nonneg]
    · have hq1 : q = 1 := by nlinarith
      have hmn : m = n :=
        branch_B3_q1_forces_m_eq_n hmn0 hAC hB3 (by simpa [q, t] using hq1)
      exact opposite_parity_not_eq hpar hmn
  · have hA : A ≠ 0 := normal_factor_A_ne_zero hmn0 hAC
    let t : ℚ := (m : ℚ) / (A : ℚ)
    let q : ℚ := t ^ 2
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact sq_nonneg t
    have hq_ne0 : q ≠ 0 := by
      dsimp [q, t]
      exact ratio_sq_ne_zero_of_nonaxis hmn0 hA
    obtain ⟨Y, hF⟩ := branch_B4_to_F hAC hA hB4
    have hFq : F_N12_AffineEquation (-3 * q) Y := by
      simpa [q, t] using hF
    rcases hFbd hFq with hx | hx | hx | hx | hx
    · have hq1 : q = 1 := by nlinarith
      have hmn : m = -n :=
        branch_B4_q1_forces_m_eq_neg_n hmn0 hAC hB4 (by simpa [q, t] using hq1)
      exact opposite_parity_not_neg hpar hmn
    · have hq0 : q = 0 := by nlinarith
      exact hq_ne0 hq0
    · have hqneg13 : q = -(1 / 3) := by nlinarith
      nlinarith [hq_nonneg]
    · have hq13 : q = 1 / 3 := by nlinarith
      exact rat_sq_ne_one_div_three t (by simpa [q, t] using hq13)
    · have hqneg : q = -1 := by nlinarith
      nlinarith [hq_nonneg]

theorem no_constrainedFactorIdentityResidual_of_F_boundary
    (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
      X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3) :
    ¬ ∃ m n a c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) ∧
      NonAxisFactorIdentityResidual m n a c := by
  rintro ⟨m, n, a, c, hmn0, _hcop, hpar, hres⟩
  exact no_nonAxisFactorIdentityResidual_of_F_boundary hFbd hmn0 hpar hres

private theorem quartic_square_of_center_three {m n a c : ℤ}
    (hprod_sq : (a * c) ^ 2 = (m * n) ^ 2)
    (hcenter_sq : pythagoreanQuarticCenter m n ^ 2 = (3 * a ^ 2 + c ^ 2) ^ 2) :
    (3 * a ^ 2 - c ^ 2) ^ 2 = pythagoreanQuarticRhs m n := by
  calc
    (3 * a ^ 2 - c ^ 2) ^ 2 =
        (3 * a ^ 2 + c ^ 2) ^ 2 - 12 * (a * c) ^ 2 := by ring
    _ = pythagoreanQuarticCenter m n ^ 2 - 12 * (m * n) ^ 2 := by
      rw [← hcenter_sq, hprod_sq]
    _ = pythagoreanQuarticRhs m n :=
      pythagorean_quartic_center_square_sub m n

private theorem quartic_square_of_center_one {m n a c : ℤ}
    (hprod_sq : (a * c) ^ 2 = (m * n) ^ 2)
    (hcenter_sq : pythagoreanQuarticCenter m n ^ 2 = (a ^ 2 + 3 * c ^ 2) ^ 2) :
    (a ^ 2 - 3 * c ^ 2) ^ 2 = pythagoreanQuarticRhs m n := by
  calc
    (a ^ 2 - 3 * c ^ 2) ^ 2 =
        (a ^ 2 + 3 * c ^ 2) ^ 2 - 12 * (a * c) ^ 2 := by ring
    _ = pythagoreanQuarticCenter m n ^ 2 - 12 * (m * n) ^ 2 := by
      rw [← hcenter_sq, hprod_sq]
    _ = pythagoreanQuarticRhs m n :=
      pythagorean_quartic_center_square_sub m n

theorem nonAxisFactorIdentityResidual_quartic_square {m n a c : ℤ}
    (hres : NonAxisFactorIdentityResidual m n a c) :
    ∃ b : ℤ, b ^ 2 = pythagoreanQuarticRhs m n := by
  rcases hres with ⟨hprod, hcases⟩ | ⟨hprod, hcases⟩
  · have hprod_sq : (a * c) ^ 2 = (m * n) ^ 2 := by rw [hprod]
    rcases hcases with hfac | hfac | hfac | hfac
    · refine ⟨3 * a ^ 2 - c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = 3 * a ^ 2 + c ^ 2 := by
        have htarget :
            pythagoreanQuarticCenter m n - (3 * a ^ 2 + c ^ 2) =
              ((m - n) * (m + n) - (a - c) * (3 * a - c)) +
                4 * (m * n - a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_three hprod_sq (by rw [hcenter])
    · refine ⟨3 * a ^ 2 - c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = -(3 * a ^ 2 + c ^ 2) := by
        have htarget :
            pythagoreanQuarticCenter m n + (3 * a ^ 2 + c ^ 2) =
              ((m - n) * (m + n) + (a + c) * (3 * a + c)) +
                4 * (m * n - a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_three hprod_sq (by rw [hcenter]; ring)
    · refine ⟨a ^ 2 - 3 * c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = a ^ 2 + 3 * c ^ 2 := by
        have htarget :
            pythagoreanQuarticCenter m n - (a ^ 2 + 3 * c ^ 2) =
              ((m - n) * (m + n) - (a - c) * (a - 3 * c)) +
                4 * (m * n - a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_one hprod_sq (by rw [hcenter])
    · refine ⟨a ^ 2 - 3 * c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = -(a ^ 2 + 3 * c ^ 2) := by
        have htarget :
            pythagoreanQuarticCenter m n + (a ^ 2 + 3 * c ^ 2) =
              ((m - n) * (m + n) + (a + c) * (a + 3 * c)) +
                4 * (m * n - a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_one hprod_sq (by rw [hcenter]; ring)
  · have hprod_sq : (a * c) ^ 2 = (m * n) ^ 2 := by rw [hprod]; ring
    rcases hcases with hfac | hfac | hfac | hfac
    · refine ⟨3 * a ^ 2 - c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = 3 * a ^ 2 + c ^ 2 := by
        have htarget :
            pythagoreanQuarticCenter m n - (3 * a ^ 2 + c ^ 2) =
              ((m - n) * (m + n) - (a + c) * (3 * a + c)) +
                4 * (m * n + a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_three hprod_sq (by rw [hcenter])
    · refine ⟨3 * a ^ 2 - c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = -(3 * a ^ 2 + c ^ 2) := by
        have htarget :
            pythagoreanQuarticCenter m n + (3 * a ^ 2 + c ^ 2) =
              ((m - n) * (m + n) + (a - c) * (3 * a - c)) +
                4 * (m * n + a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_three hprod_sq (by rw [hcenter]; ring)
    · refine ⟨a ^ 2 - 3 * c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = a ^ 2 + 3 * c ^ 2 := by
        have htarget :
            pythagoreanQuarticCenter m n - (a ^ 2 + 3 * c ^ 2) =
              ((m - n) * (m + n) - (a + c) * (a + 3 * c)) +
                4 * (m * n + a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_one hprod_sq (by rw [hcenter])
    · refine ⟨a ^ 2 - 3 * c ^ 2, ?_⟩
      have hcenter : pythagoreanQuarticCenter m n = -(a ^ 2 + 3 * c ^ 2) := by
        have htarget :
            pythagoreanQuarticCenter m n + (a ^ 2 + 3 * c ^ 2) =
              ((m - n) * (m + n) + (a - c) * (a - 3 * c)) +
                4 * (m * n + a * c) := by
          dsimp [pythagoreanQuarticCenter]
          ring
        nlinarith
      exact quartic_square_of_center_one hprod_sq (by rw [hcenter]; ring)

theorem nonAxisSignedResidual_factorIdentityResidual {m n b r s : ℤ}
    (hres : NonAxisSignedResidual m n b r s) :
    ∃ a c : ℤ, NonAxisFactorIdentityResidual m n a c := by
  exact nonAxisSignedResidual_factor_identity_cases hres

theorem nonAxisSignedResidual_factorIdentityResidual_with_constraints {m n b r s : ℤ}
    (hres : NonAxisSignedResidual m n b r s) :
    ∃ a c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      NonAxisFactorIdentityResidual m n a c := by
  rcases hres with ⟨hmn, hcop, hpar, hb, hr, hs, hrs, hgcd, hsigned⟩
  have hres' : NonAxisSignedResidual m n b r s :=
    ⟨hmn, hcop, hpar, hb, hr, hs, hrs, hgcd, hsigned⟩
  obtain ⟨a, c, hfac⟩ := nonAxisSignedResidual_factorIdentityResidual hres'
  exact ⟨a, c, hmn, hcop, hpar, hfac⟩

theorem rationalCoverSignedResidual_factorIdentityResidual {t : ℚ}
    (hres : RationalCoverSignedResidual t) :
    ∃ T D Y m n b r s a c : ℤ,
      0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
      Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) ∧
      NonAxisSignedResidual m n b r s ∧
      NonAxisFactorIdentityResidual m n a c := by
  obtain ⟨T, D, Y, m, n, b, r, s, hDpos, hcop, ht, hcover, hresidual⟩ := hres
  obtain ⟨a, c, hfactor⟩ := nonAxisSignedResidual_factorIdentityResidual hresidual
  exact ⟨T, D, Y, m, n, b, r, s, a, c, hDpos, hcop, ht, hcover,
    hresidual, hfactor⟩

theorem rationalCoverSignedResidual_constrainedFactorIdentityResidual {t : ℚ}
    (hres : RationalCoverSignedResidual t) :
    ∃ m n a c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      NonAxisFactorIdentityResidual m n a c := by
  obtain ⟨_, _, _, m, n, b, r, s, _, _, _, _, hresidual⟩ := hres
  obtain ⟨a, c, hmn, hcop, hpar, hfac⟩ :=
    nonAxisSignedResidual_factorIdentityResidual_with_constraints hresidual
  exact ⟨m, n, a, c, hmn, hcop, hpar, hfac⟩

theorem pythagoreanQuarticRhs_sq_sub_two_mul (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2
        + 4 * (m ^ 2 - n ^ 2) * (2 * m * n)
        + (2 * m * n) ^ 2
      = pythagoreanQuarticRhs m n := by
  unfold pythagoreanQuarticRhs
  ring

theorem pythagoreanQuarticRhs_two_mul_sq_sub (m n : ℤ) :
    (2 * m * n) ^ 2
        + 4 * (2 * m * n) * (m ^ 2 - n ^ 2)
        + (m ^ 2 - n ^ 2) ^ 2
      = pythagoreanQuarticRhs m n := by
  unfold pythagoreanQuarticRhs
  ring

theorem quartic_rhs_from_pythagorean_legs {R S m n : ℤ}
    (hlegs :
      (R = m ^ 2 - n ^ 2 ∧ S = 2 * m * n) ∨
      (R = 2 * m * n ∧ S = m ^ 2 - n ^ 2)) :
    R ^ 2 + 4 * R * S + S ^ 2 = pythagoreanQuarticRhs m n := by
  rcases hlegs with hlegs | hlegs
  · rcases hlegs with ⟨rfl, rfl⟩
    exact pythagoreanQuarticRhs_sq_sub_two_mul m n
  · rcases hlegs with ⟨rfl, rfl⟩
    exact pythagoreanQuarticRhs_two_mul_sq_sub m n

theorem pythagorean_params_mul_ne_zero_of_legs {R S m n : ℤ}
    (hRS0 : R * S ≠ 0)
    (hlegs :
      (R = m ^ 2 - n ^ 2 ∧ S = 2 * m * n) ∨
      (R = 2 * m * n ∧ S = m ^ 2 - n ^ 2)) :
    m * n ≠ 0 := by
  have hR0 : R ≠ 0 := by
    intro hR
    apply hRS0
    simp [hR]
  have hS0 : S ≠ 0 := by
    intro hS
    apply hRS0
    simp [hS]
  rcases hlegs with hlegs | hlegs
  · rcases hlegs with ⟨_hR, hS⟩
    intro hmn
    apply hS0
    calc
      S = 2 * m * n := hS
      _ = 2 * (m * n) := by ring
      _ = 0 := by rw [hmn]; ring
  · rcases hlegs with ⟨hR, _hS⟩
    intro hmn
    apply hR0
    calc
      R = 2 * m * n := hR
      _ = 2 * (m * n) := by ring
      _ = 0 := by rw [hmn]; ring

private lemma odd_add_of_emod_zero_one {a b : ℤ}
    (ha : a % 2 = 0) (hb : b % 2 = 1) : Odd (a + b) := by
  rw [Int.odd_iff]
  rw [Int.add_emod, ha, hb]
  norm_num

private lemma odd_add_of_emod_one_zero {a b : ℤ}
    (ha : a % 2 = 1) (hb : b % 2 = 0) : Odd (a + b) := by
  rw [add_comm]
  exact odd_add_of_emod_zero_one hb ha

private lemma odd_add_of_pythagorean_param_parity {m n : ℤ}
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Odd (m + n) := by
  rcases hpar with h | h
  · exact odd_add_of_emod_zero_one h.1 h.2
  · exact odd_add_of_emod_one_zero h.1 h.2

theorem primitive_pythagorean_twist_to_pythagoreanQuarticRhs {R S r s : ℤ}
    (hRS0 : R * S ≠ 0)
    (hcop : Int.gcd R S = 1)
    (hpar : Odd (R + S))
    (hs : s ^ 2 = R ^ 2 + S ^ 2)
    (hr : r ^ 2 = R ^ 2 + 4 * R * S + S ^ 2) :
    ∃ m n : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      Odd (m + n) ∧
      r ^ 2 = pythagoreanQuarticRhs m n := by
  have htrip : PythagoreanTriple R S s := by
    dsimp [PythagoreanTriple]
    calc
      R * R + S * S = R ^ 2 + S ^ 2 := by ring
      _ = s ^ 2 := hs.symm
      _ = s * s := by ring
  have _hpar_supplied : Odd (R + S) := hpar
  obtain ⟨m, n, hlegs, _hsign, hgcd, hmnpar⟩ :=
    PythagoreanTriple.coprime_classification.mp ⟨htrip, hcop⟩
  refine ⟨m, n, ?_, hgcd, ?_, ?_⟩
  · exact pythagorean_params_mul_ne_zero_of_legs hRS0 hlegs
  · exact odd_add_of_pythagorean_param_parity hmnpar
  · rw [hr]
    exact quartic_rhs_from_pythagorean_legs hlegs

def QuarticB (u v Z : ℤ) : Prop :=
  Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)

def QuarticA (u v Z : ℤ) : Prop :=
  Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)

theorem quarticA_add_four_v_four (u v : ℤ) :
    (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) + (2 * v ^ 2) ^ 2 =
      (u ^ 2 + v ^ 2) ^ 2 := by
  ring

theorem quarticA_pythagorean_identity {u v Z : ℤ}
    (hA : QuarticA u v Z) :
    Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  dsimp [QuarticA] at hA
  rw [hA]
  exact quarticA_add_four_v_four u v

theorem quarticA_pythagoreanTriple {u v Z : ℤ}
    (hA : QuarticA u v Z) :
    PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2) := by
  dsimp [PythagoreanTriple]
  have h := quarticA_pythagorean_identity (u := u) (v := v) (Z := Z) hA
  nlinarith [h]

theorem quarticA_right_factor_pos {u v : ℤ}
    (hv0 : v ≠ 0) :
    0 < u ^ 2 + 3 * v ^ 2 := by
  have hv2pos : 0 < v ^ 2 := sq_pos_of_ne_zero hv0
  have hu2nonneg : 0 ≤ u ^ 2 := sq_nonneg u
  nlinarith

theorem quarticA_left_factor_pos {u v Z : ℤ}
    (hv0 : v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    0 < u ^ 2 - v ^ 2 := by
  dsimp [QuarticA] at hA
  have hright : 0 < u ^ 2 + 3 * v ^ 2 := quarticA_right_factor_pos (u := u) hv0
  have hprod_nonneg : 0 ≤ (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
    rw [← hA]
    exact sq_nonneg Z
  have hleft_nonneg : 0 ≤ u ^ 2 - v ^ 2 := by
    nlinarith
  have hleft_ne : u ^ 2 - v ^ 2 ≠ 0 := sub_ne_zero.mpr hne
  exact lt_of_le_of_ne hleft_nonneg (Ne.symm hleft_ne)

theorem eisenstein_sq_sub_sq_add_mul (A B : ℤ) :
    (A ^ 2 - B ^ 2) ^ 2 + A ^ 2 * B ^ 2 =
      A ^ 4 - A ^ 2 * B ^ 2 + B ^ 4 := by
  ring

theorem eisenstein_from_half_sum_diff (M N : ℤ) :
    (M - N) ^ 2 + M * N = M ^ 2 - M * N + N ^ 2 := by
  ring

theorem eisenstein_to_fermat14 (m n : ℤ) :
    (m + n) ^ 4 - (m + n) ^ 2 * (m - n) ^ 2 + (m - n) ^ 4 =
      m ^ 4 + 14 * m ^ 2 * n ^ 2 + n ^ 4 := by
  ring

theorem quarticA_factor_diff (u v : ℤ) :
    (u ^ 2 + 3 * v ^ 2) - (u ^ 2 - v ^ 2) = 4 * v ^ 2 := by
  ring

/-- The Eisenstein/Ljunggren quartic residual reached by the `QuarticA` branch. -/
def EisensteinQuarticResidual : Prop :=
  ∃ m n c : ℤ,
    m * n ≠ 0 ∧
    Int.gcd m n = 1 ∧
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4

def SameSignSquareFactors (a b : ℤ) : Prop :=
  ∃ m n : ℤ,
    m * n ≠ 0 ∧
    Int.gcd m n = 1 ∧
      ((a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2)))

def QuarticAEisensteinParam (u v : ℤ) : Prop :=
  ∃ a b : ℤ,
    a * b ≠ 0 ∧
    Int.gcd a b = 1 ∧
    a * b = v ^ 2 ∧
    u ^ 2 = a ^ 2 - a * b + b ^ 2

theorem eisensteinQuarticResidual_of_param_of_signedSquares {u a b : ℤ}
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsq : SameSignSquareFactors a b) :
    EisensteinQuarticResidual := by
  rcases hsq with ⟨m, n, hmn0, hmn_coprime, hsign⟩
  refine ⟨m, n, u, hmn0, hmn_coprime, ?_⟩
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        rw [ha, hb]
        ring
  · rcases hneg with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        rw [ha, hb]
        ring

def CoprimeSquareProductExtraction : Prop :=
  ∀ {v a b : ℤ},
    a * b ≠ 0 →
    Int.gcd a b = 1 →
    a * b = v ^ 2 →
    SameSignSquareFactors a b

theorem eisensteinQuarticResidual_of_eisensteinParam {u v : ℤ}
    (hParam : QuarticAEisensteinParam u v)
    (hExtract :
      ∀ {a b : ℤ},
        a * b ≠ 0 →
        Int.gcd a b = 1 →
        a * b = v ^ 2 →
        SameSignSquareFactors a b) :
    EisensteinQuarticResidual := by
  rcases hParam with ⟨a, b, hab0, hab_coprime, hab_square, hu⟩
  exact eisensteinQuarticResidual_of_param_of_signedSquares
    hu (hExtract hab0 hab_coprime hab_square)

theorem quarticA_eisensteinParam_from_evenLegParams {u v r s : ℤ}
    (hrs0 : r * s ≠ 0)
    (hrs_coprime : Int.gcd r s = 1)
    (hprod : r * s = v ^ 2)
    (hhyp : r ^ 2 + s ^ 2 = u ^ 2 + v ^ 2) :
    QuarticAEisensteinParam u v := by
  refine ⟨r, s, hrs0, hrs_coprime, hprod, ?_⟩
  calc
    u ^ 2 = (u ^ 2 + v ^ 2) - v ^ 2 := by ring
    _ = (r ^ 2 + s ^ 2) - v ^ 2 := by rw [← hhyp]
    _ = r ^ 2 - r * s + s ^ 2 := by
      rw [← hprod]
      ring

theorem quarticA_eisensteinParam_from_oddLegParams {u v r s : ℤ}
    (hab0 : (r + s) * (r - s) ≠ 0)
    (hab_coprime : Int.gcd (r + s) (r - s) = 1)
    (hprod : (r + s) * (r - s) = v ^ 2)
    (hhyp : 2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2) :
    QuarticAEisensteinParam u v := by
  refine ⟨r + s, r - s, hab0, hab_coprime, hprod, ?_⟩
  calc
    u ^ 2 = (u ^ 2 + v ^ 2) - v ^ 2 := by ring
    _ = 2 * (r ^ 2 + s ^ 2) - v ^ 2 := by rw [← hhyp]
    _ = (r + s) ^ 2 - (r + s) * (r - s) + (r - s) ^ 2 := by
      rw [← hprod]
      ring

lemma quarticA_int_sum_sq_pos_of_mul_ne_zero {u v : ℤ}
    (huv0 : u * v ≠ 0) :
    0 < u ^ 2 + v ^ 2 := by
  have hu0 : u ≠ 0 := by
    intro hu
    exact huv0 (by simp [hu])
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu0) (sq_nonneg v)

lemma quarticA_even_square_leg_mod_two (v : ℤ) :
    (2 * v ^ 2) % 2 = 0 := by
  simp

lemma quarticA_first_leg_mod_two_eq_one_of_second_leg_even {x y z : ℤ}
    (htrip : PythagoreanTriple x y z)
    (hcop : Int.gcd x y = 1)
    (hy : y % 2 = 0) :
    x % 2 = 1 := by
  obtain hbad | hgood := htrip.even_odd_of_coprime hcop
  · rw [hy] at hbad
    exact False.elim (zero_ne_one hbad.2)
  · exact hgood.1

theorem quarticA_evenLegParams_of_pythagorean_leg_coprime {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (htrip : PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2))
    (hlegcop : Int.gcd Z (2 * v ^ 2) = 1) :
    ∃ r s : ℤ,
      r * s ≠ 0 ∧
      Int.gcd r s = 1 ∧
      r * s = v ^ 2 ∧
      r ^ 2 + s ^ 2 = u ^ 2 + v ^ 2 := by
  have hZmod : Z % 2 = 1 :=
    quarticA_first_leg_mod_two_eq_one_of_second_leg_even
      htrip hlegcop (quarticA_even_square_leg_mod_two v)
  have hsum_pos : 0 < u ^ 2 + v ^ 2 :=
    quarticA_int_sum_sq_pos_of_mul_ne_zero huv0
  obtain ⟨m, n, _hZ, h2v, hsum, hgcd, _hmnpar, _hm_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      htrip hlegcop hZmod hsum_pos
  have hprod : m * n = v ^ 2 := by
    have htwo : 2 * (m * n) = 2 * (v ^ 2) := by
      calc
        2 * (m * n) = 2 * m * n := by ring
        _ = 2 * v ^ 2 := h2v.symm
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) htwo
  have hmn0 : m * n ≠ 0 := by
    have hv0 : v ≠ 0 := by
      intro hv
      exact huv0 (by simp [hv])
    have hvsq0 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv0
    rw [hprod]
    exact hvsq0
  exact ⟨m, n, hmn0, hgcd, hprod, hsum.symm⟩

theorem quarticA_evenLegParams_of_oppParity_with_leg_coprime {u v Z : ℤ}
    (_hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (_hne : u ^ 2 ≠ v ^ 2)
    (_hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z)
    (hlegcop : Int.gcd Z (2 * v ^ 2) = 1) :
    ∃ r s : ℤ,
      r * s ≠ 0 ∧
      Int.gcd r s = 1 ∧
      r * s = v ^ 2 ∧
      r ^ 2 + s ^ 2 = u ^ 2 + v ^ 2 := by
  exact quarticA_evenLegParams_of_pythagorean_leg_coprime
    (u := u) (v := v) (Z := Z)
    huv0 (quarticA_pythagoreanTriple hA) hlegcop

theorem quarticA_eisensteinParam_of_oppParity_with_leg_coprime {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z)
    (hlegcop : Int.gcd Z (2 * v ^ 2) = 1) :
    QuarticAEisensteinParam u v := by
  obtain ⟨r, s, hrs0, hrs_coprime, hprod, hhyp⟩ :=
    quarticA_evenLegParams_of_oppParity_with_leg_coprime
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hopp hA hlegcop
  exact quarticA_eisensteinParam_from_evenLegParams
    (u := u) (v := v) (r := r) (s := s)
    hrs0 hrs_coprime hprod hhyp

private theorem quarticA_odd_odd_two_dvd_sum_sq {u v : ℤ}
    (huodd : Odd u) (hvodd : Odd v) :
    (2 : ℤ) ∣ u ^ 2 + v ^ 2 := by
  exact Even.two_dvd ((huodd.pow).add_odd hvodd.pow)

private theorem quarticA_two_dvd_left_of_pythagorean_even_hyp {Z v H : ℤ}
    (htrip : PythagoreanTriple Z (2 * v ^ 2) H)
    (h2H : (2 : ℤ) ∣ H) :
    (2 : ℤ) ∣ Z := by
  have hHeven : Even H := even_iff_two_dvd.mpr h2H
  have hy_even : Even (2 * v ^ 2) := even_two_mul (v ^ 2)
  have hy_sq_even : Even ((2 * v ^ 2) * (2 * v ^ 2)) :=
    hy_even.mul_right (2 * v ^ 2)
  have hsum_even : Even (Z * Z + (2 * v ^ 2) * (2 * v ^ 2)) := by
    dsimp [PythagoreanTriple] at htrip
    rw [htrip]
    exact hHeven.mul_right H
  have hZ_sq_even : Even (Z * Z) :=
    (Int.even_add.mp hsum_even).mpr hy_sq_even
  have hZeven : Even Z := by
    rcases Int.even_mul.mp hZ_sq_even with hZ | hZ <;> exact hZ
  exact Even.two_dvd hZeven

theorem quarticA_odd_odd_divided_pythagoreanTriple {u v Z : ℤ}
    (huodd : Odd u) (hvodd : Odd v)
    (htrip : PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2)) :
    PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2) := by
  have h2H : (2 : ℤ) ∣ u ^ 2 + v ^ 2 :=
    quarticA_odd_odd_two_dvd_sum_sq huodd hvodd
  have h2Z : (2 : ℤ) ∣ Z :=
    quarticA_two_dvd_left_of_pythagorean_even_hyp
      (Z := Z) (v := v) (H := u ^ 2 + v ^ 2) htrip h2H
  have hZeq : 2 * (Z / 2) = Z := by
    simpa [mul_comm] using Int.ediv_mul_cancel h2Z
  have hHeq : 2 * ((u ^ 2 + v ^ 2) / 2) = u ^ 2 + v ^ 2 := by
    simpa [mul_comm] using Int.ediv_mul_cancel h2H
  have hmul :
      PythagoreanTriple (2 * (Z / 2)) (2 * (v ^ 2))
        (2 * ((u ^ 2 + v ^ 2) / 2)) := by
    simpa [hZeq, hHeq] using htrip
  exact (PythagoreanTriple.mul_iff
    (x := Z / 2) (y := v ^ 2) (z := (u ^ 2 + v ^ 2) / 2)
    (2 : ℤ) (by norm_num)).mp hmul

theorem quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA {u v Z : ℤ}
    (huodd : Odd u) (hvodd : Odd v)
    (hA : QuarticA u v Z) :
    PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2) := by
  exact quarticA_odd_odd_divided_pythagoreanTriple
    (u := u) (v := v) (Z := Z) huodd hvodd
    (quarticA_pythagoreanTriple hA)

def QuarticAOddOddRSData (u v _Z : ℤ) : Prop :=
  ∃ r s : ℤ,
    Int.gcd (r + s) (r - s) = 1 ∧
    v ^ 2 = r ^ 2 - s ^ 2 ∧
    (u ^ 2 + v ^ 2) / 2 = r ^ 2 + s ^ 2

def QuarticAOddOddRSDataTheorem : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    Odd u →
    Odd v →
    QuarticA u v Z →
    QuarticAOddOddRSData u v Z

private theorem add_sub_mul_ne_zero_of_eq_square_of_ne_zero {r s v : ℤ}
    (hprod : (r + s) * (r - s) = v ^ 2)
    (hv0 : v ≠ 0) :
    (r + s) * (r - s) ≠ 0 := by
  intro hzero
  have hv_sq_zero : v ^ 2 = 0 := by
    simpa [hzero] using hprod.symm
  have hv_mul_zero : v * v = 0 := by
    simpa [pow_two] using hv_sq_zero
  rcases mul_eq_zero.mp hv_mul_zero with hv | hv
  · exact hv0 hv
  · exact hv0 hv

theorem quarticA_eisensteinParam_from_oddOddRSData {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (huodd : Odd u) (hvodd : Odd v)
    (hRS : QuarticAOddOddRSData u v Z) :
    QuarticAEisensteinParam u v := by
  rcases hRS with ⟨r, s, hab_coprime, hv_sq, hH⟩
  have hv0 : v ≠ 0 := by
    intro hv
    exact huv0 (by simp [hv])
  have hprod : (r + s) * (r - s) = v ^ 2 := by
    rw [hv_sq]
    ring
  have hab0 : (r + s) * (r - s) ≠ 0 :=
    add_sub_mul_ne_zero_of_eq_square_of_ne_zero hprod hv0
  have h2H : (2 : ℤ) ∣ u ^ 2 + v ^ 2 :=
    quarticA_odd_odd_two_dvd_sum_sq huodd hvodd
  have hhyp : 2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2 := by
    rw [← hH]
    rw [mul_comm, Int.ediv_mul_cancel h2H]
  exact quarticA_eisensteinParam_from_oddLegParams
    (u := u) (v := v) (r := r) (s := s)
    hab0 hab_coprime hprod hhyp

def QuarticAOddOddDividedTriplePrimitiveTheorem : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    Odd u →
    Odd v →
    QuarticA u v Z →
    Int.gcd (Z / 2) (v ^ 2) = 1

theorem int_gcd_eq_one_of_no_common_prime {x y : ℤ}
    (hprime : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → (p : ℤ) ∣ y → False) :
    Int.gcd x y = 1 := by
  rw [Int.gcd_def]
  change Nat.Coprime x.natAbs y.natAbs
  by_contra hcop
  obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  exact hprime p hp
    ((Int.natCast_dvd).mpr hpx)
    ((Int.natCast_dvd).mpr hpy)

theorem int_natPrime_dvd_of_dvd_sq {p : ℕ} {x : ℤ}
    (hp : p.Prime) (hpx2 : (p : ℤ) ∣ x ^ 2) :
    (p : ℤ) ∣ x := by
  exact Int.Prime.dvd_pow' hp hpx2

theorem two_mul_ediv_two_sq_add_sq_of_odd {u v : ℤ}
    (huodd : Odd u) (hvodd : Odd v) :
    2 * ((u ^ 2 + v ^ 2) / 2) = u ^ 2 + v ^ 2 := by
  have hu2odd : Odd (u ^ 2) := by
    simpa [pow_two] using huodd.mul huodd
  have hv2odd : Odd (v ^ 2) := by
    simpa [pow_two] using hvodd.mul hvodd
  have hEven : Even (u ^ 2 + v ^ 2) := hu2odd.add_odd hv2odd
  have htwo_dvd : (2 : ℤ) ∣ u ^ 2 + v ^ 2 := by
    simpa [even_iff_two_dvd] using hEven
  simpa [mul_comm] using (Int.ediv_mul_cancel htwo_dvd)

theorem quarticA_odd_odd_divided_pythagorean_identity {u v Z : ℤ}
    (huodd : Odd u) (hvodd : Odd v) (hA : QuarticA u v Z) :
    (Z / 2) ^ 2 + (v ^ 2) ^ 2 = ((u ^ 2 + v ^ 2) / 2) ^ 2 := by
  simpa [PythagoreanTriple, pow_two] using
    (quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA
      (u := u) (v := v) (Z := Z) huodd hvodd hA)

theorem quarticAOddOddDividedTriplePrimitive :
    QuarticAOddOddDividedTriplePrimitiveTheorem := by
  intro u v Z hcop huv0 huodd hvodd hA
  apply int_gcd_eq_one_of_no_common_prime
  intro p hp hpZ2 hpv2
  have hpv : (p : ℤ) ∣ v := int_natPrime_dvd_of_dvd_sq hp hpv2
  have hpZprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  by_cases hp2 : p = 2
  · subst hp2; exact (int_not_two_dvd_of_odd hvodd) hpv
  · have hpnot2 := odd_nat_prime_int_not_dvd_two hp hp2
    have hpu : ¬ (p : ℤ) ∣ u := by
      intro hpu
      have hpg : (p : ℤ) ∣ ((Int.gcd u v : ℕ) : ℤ) := Int.dvd_coe_gcd hpu hpv
      rw [hcop] at hpg; exact hpZprime.not_dvd_one hpg
    have h2Z : (2 : ℤ) ∣ Z :=
      quarticA_two_dvd_left_of_pythagorean_even_hyp
        (quarticA_pythagoreanTriple hA) (quarticA_odd_odd_two_dvd_sum_sq huodd hvodd)
    have hpZfull : (p : ℤ) ∣ Z := by
      have h := dvd_mul_of_dvd_left hpZ2 (2 : ℤ)
      rwa [Int.ediv_mul_cancel h2Z] at h
    have hpZsq : (p : ℤ) ∣ Z ^ 2 := dvd_pow hpZfull (by norm_num : 2 ≠ 0)
    dsimp [QuarticA] at hA
    have hpRHS : (p : ℤ) ∣ (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by rwa [← hA]
    have hpdiff : (p : ℤ) ∣ v ^ 2 * (2 * u ^ 2 - 3 * v ^ 2) := dvd_mul_of_dvd_left hpv2 _
    have hpu4 : (p : ℤ) ∣ u ^ 4 := by
      have h := dvd_sub hpRHS hpdiff
      have heq : (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) -
          v ^ 2 * (2 * u ^ 2 - 3 * v ^ 2) = u ^ 4 := by ring
      rwa [heq] at h
    exact hpu (hpZprime.dvd_of_dvd_pow hpu4)

def QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem : Prop :=
  ∀ {u v Z : ℤ},
    u * v ≠ 0 →
    Odd u →
    Odd v →
    PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2) →
    Int.gcd (Z / 2) (v ^ 2) = 1 →
    QuarticAOddOddRSData u v Z

private theorem quarticA_half_sum_sq_pos_of_mul_ne_zero_of_two_dvd {u v : ℤ}
    (huv0 : u * v ≠ 0)
    (h2 : (2 : ℤ) ∣ u ^ 2 + v ^ 2) :
    0 < (u ^ 2 + v ^ 2) / 2 := by
  have hu0 : u ≠ 0 := by
    intro hu
    exact huv0 (by simp [hu])
  have hsumpos : 0 < u ^ 2 + v ^ 2 := by
    have hu2pos : 0 < u ^ 2 := sq_pos_of_ne_zero hu0
    have hv2nonneg : 0 ≤ v ^ 2 := sq_nonneg v
    nlinarith
  rcases h2 with ⟨k, hk⟩
  have hkpos : 0 < k := by
    have h2kpos : 0 < 2 * k := by
      rw [← hk]
      exact hsumpos
    nlinarith
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  exact hkpos

private theorem odd_add_of_opposite_parity_mod_two {r s : ℤ}
    (hpp : (r % 2 = 0 ∧ s % 2 = 1) ∨ (r % 2 = 1 ∧ s % 2 = 0)) :
    Odd (r + s) := by
  rcases hpp with hpp | hpp
  · exact (Int.even_iff.mpr hpp.1).add_odd (Int.odd_iff.mpr hpp.2)
  · exact (Int.odd_iff.mpr hpp.1).add_even (Int.even_iff.mpr hpp.2)

theorem int_gcd_add_sub_eq_one_of_gcd_eq_one_of_opp_parity {r s : ℤ}
    (hcop : Int.gcd r s = 1)
    (hpp : (r % 2 = 0 ∧ s % 2 = 1) ∨ (r % 2 = 1 ∧ s % 2 = 0)) :
    Int.gcd (r + s) (r - s) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hp_add, hp_sub⟩ := Nat.Prime.not_coprime_iff_dvd.mp hne
  rw [← Int.natCast_dvd] at hp_add hp_sub
  by_cases hp2 : p = 2
  · have h2_add : (2 : ℤ) ∣ r + s := by
      simpa [hp2] using hp_add
    have h_add_odd : Odd (r + s) := odd_add_of_opposite_parity_mod_two hpp
    have h_add_even : Even (r + s) := even_iff_two_dvd.mpr h2_add
    exact (Int.not_even_iff_odd.mpr h_add_odd) h_add_even
  · have hpZ : Prime (p : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
    have hp_not_dvd_two : ¬ (p : ℤ) ∣ (2 : ℤ) :=
      odd_nat_prime_int_not_dvd_two hp hp2
    have hp_2r : (p : ℤ) ∣ 2 * r := by
      have h := dvd_add hp_add hp_sub
      have hcalc : (r + s) + (r - s) = 2 * r := by ring
      simpa [hcalc] using h
    have hp_2s : (p : ℤ) ∣ 2 * s := by
      have h := dvd_sub hp_add hp_sub
      have hcalc : (r + s) - (r - s) = 2 * s := by ring
      simpa [hcalc] using h
    have hp_r : (p : ℤ) ∣ r := by
      rcases hpZ.dvd_or_dvd hp_2r with hp_two | hp_r
      · exact False.elim (hp_not_dvd_two hp_two)
      · exact hp_r
    have hp_s : (p : ℤ) ∣ s := by
      rcases hpZ.dvd_or_dvd hp_2s with hp_two | hp_s
      · exact False.elim (hp_not_dvd_two hp_two)
      · exact hp_s
    have hp_gcd : (p : ℤ) ∣ ((Int.gcd r s : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hp_r hp_s
    have hp_one : (p : ℤ) ∣ (1 : ℤ) := by
      simpa [hcop] using hp_gcd
    exact hpZ.not_dvd_one hp_one

theorem quarticA_oddOddRSDataOfPrimitiveDividedTripleTheorem :
    QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem := by
  intro u v Z huv0 huodd hvodd htrip hcop
  have hv2odd : Odd (v ^ 2) := hvodd.pow
  have hv2mod : v ^ 2 % 2 = 1 := Int.odd_iff.mp hv2odd
  have hcop_symm : Int.gcd (v ^ 2) (Z / 2) = 1 := by
    simpa [Int.gcd_comm] using hcop
  have h2sum : (2 : ℤ) ∣ u ^ 2 + v ^ 2 :=
    quarticA_odd_odd_two_dvd_sum_sq huodd hvodd
  have hHpos : 0 < (u ^ 2 + v ^ 2) / 2 :=
    quarticA_half_sum_sq_pos_of_mul_ne_zero_of_two_dvd huv0 h2sum
  obtain ⟨r, s, hv_sq, _hZ_half, hH, hrs_coprime, hrs_parity, _hr_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      (x := v ^ 2)
      (y := Z / 2)
      (z := (u ^ 2 + v ^ 2) / 2)
      htrip.symm hcop_symm hv2mod hHpos
  refine ⟨r, s, ?_, hv_sq, hH⟩
  exact int_gcd_add_sub_eq_one_of_gcd_eq_one_of_opp_parity
    hrs_coprime hrs_parity

theorem QuarticAOddOddRSDataTheorem_of_dividedPrimitive_and_classification
    (hprim : QuarticAOddOddDividedTriplePrimitiveTheorem)
    (hclass : QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem) :
    QuarticAOddOddRSDataTheorem := by
  intro u v Z hcop huv0 hne huodd hvodd hA
  exact hclass huv0 huodd hvodd
    (quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA
      (u := u) (v := v) (Z := Z) huodd hvodd hA)
    (hprim hcop huv0 huodd hvodd hA)

def QuarticAParamBridge : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    QuarticA u v Z →
    QuarticAEisensteinParam u v

theorem quarticA_to_eisensteinQuarticResidual_of_bridge
    (hBridge : QuarticAParamBridge)
    (hExtract : CoprimeSquareProductExtraction)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    EisensteinQuarticResidual := by
  exact eisensteinQuarticResidual_of_eisensteinParam
    (hBridge hcop huv0 hne hA)
    (fun {a b} hab0 hab_coprime hab_square =>
      hExtract hab0 hab_coprime hab_square)

theorem quarticA_to_eisenstein_residual_statement_of_bridge
    (hBridge : QuarticAParamBridge)
    (hExtract : CoprimeSquareProductExtraction)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  exact quarticA_to_eisensteinQuarticResidual_of_bridge
    hBridge hExtract hcop huv0 hne hA

def QuarticAOppParityParamBridge : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    ((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) →
    QuarticA u v Z →
    QuarticAEisensteinParam u v

def QuarticAOddOddParamBridge : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    Odd u →
    Odd v →
    QuarticA u v Z →
    QuarticAEisensteinParam u v

theorem QuarticAOddOddParamBridge_of_RSDataTheorem
    (hRSTheorem : QuarticAOddOddRSDataTheorem) :
    QuarticAOddOddParamBridge := by
  intro u v Z hcop huv0 hne huodd hvodd hA
  exact quarticA_eisensteinParam_from_oddOddRSData
    (u := u) (v := v) (Z := Z)
    huv0 huodd hvodd
    (hRSTheorem hcop huv0 hne huodd hvodd hA)

def QuarticAPrimitiveParitySplit : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    QuarticA u v Z →
    (((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) ∨ (Odd u ∧ Odd v))

theorem quarticA_natAbs_two_dvd_of_even {z : ℤ} (hz : Even z) :
    (2 : ℕ) ∣ z.natAbs := by
  have h2z : (2 : ℤ) ∣ z := even_iff_two_dvd.mp hz
  rcases h2z with ⟨k, hk⟩
  refine ⟨k.natAbs, ?_⟩
  calc
    z.natAbs = ((2 : ℤ) * k).natAbs := by simp [hk]
    _ = (2 : ℤ).natAbs * k.natAbs := by
      simpa using (Int.natAbs_mul (2 : ℤ) k)
    _ = 2 * k.natAbs := by norm_num

theorem quarticA_not_even_even_of_int_gcd_eq_one {u v : ℤ}
    (hcop : Int.gcd u v = 1) :
    ¬ (Even u ∧ Even v) := by
  rintro ⟨hu, hv⟩
  have huNat : (2 : ℕ) ∣ u.natAbs := quarticA_natAbs_two_dvd_of_even hu
  have hvNat : (2 : ℕ) ∣ v.natAbs := quarticA_natAbs_two_dvd_of_even hv
  have hgNat : (2 : ℕ) ∣ Nat.gcd u.natAbs v.natAbs :=
    Nat.dvd_gcd huNat hvNat
  have hcopNat : Nat.gcd u.natAbs v.natAbs = 1 := by
    simpa [Int.gcd_eq_natAbs] using hcop
  rw [hcopNat] at hgNat
  norm_num at hgNat

theorem quarticAPrimitiveParitySplit_proof : QuarticAPrimitiveParitySplit := by
  intro u v Z hcop _huv0 _hA
  rcases Int.even_or_odd u with huEven | huOdd
  · rcases Int.even_or_odd v with hvEven | hvOdd
    · exfalso
      exact quarticA_not_even_even_of_int_gcd_eq_one
        (u := u) (v := v) hcop ⟨huEven, hvEven⟩
    · exact Or.inl (Or.inr ⟨huEven, hvOdd⟩)
  · rcases Int.even_or_odd v with hvEven | hvOdd
    · exact Or.inl (Or.inl ⟨huOdd, hvEven⟩)
    · exact Or.inr ⟨huOdd, hvOdd⟩

theorem quarticA_oppParity_factor_product_odd {u v : ℤ}
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) :
    Odd ((u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) := by
  rcases hopp with h | h
  · rcases h with ⟨hu, hv⟩
    have hu2 : Odd (u ^ 2) := by simpa using (hu.pow : Odd (u ^ 2))
    have hv2 : Even (v ^ 2) := by
      exact (Int.even_pow' (m := v) (n := 2) (by norm_num : 2 ≠ 0)).2 hv
    have hleft : Odd (u ^ 2 - v ^ 2) := hu2.sub_even hv2
    have h3v2 : Even (3 * v ^ 2) := hv2.mul_left 3
    have hright : Odd (u ^ 2 + 3 * v ^ 2) := hu2.add_even h3v2
    exact hleft.mul hright
  · rcases h with ⟨hu, hv⟩
    have hu2 : Even (u ^ 2) := by
      exact (Int.even_pow' (m := u) (n := 2) (by norm_num : 2 ≠ 0)).2 hu
    have hv2 : Odd (v ^ 2) := by simpa using (hv.pow : Odd (v ^ 2))
    have hleft : Odd (u ^ 2 - v ^ 2) := hu2.sub_odd hv2
    have hthree : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have h3v2 : Odd (3 * v ^ 2) := hthree.mul hv2
    have hright : Odd (u ^ 2 + 3 * v ^ 2) := hu2.add_odd h3v2
    exact hleft.mul hright

theorem quarticA_oppParity_Z_odd {u v Z : ℤ}
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z) :
    Odd Z := by
  have hAeq :
      Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
    simpa [QuarticA] using hA
  have hZ2 : Odd (Z ^ 2) := by
    rw [hAeq]
    exact quarticA_oppParity_factor_product_odd (u := u) (v := v) hopp
  exact (Int.odd_pow' (m := Z) (n := 2) (by norm_num : 2 ≠ 0)).1 hZ2

theorem quarticA_oppParity_leg_coprime {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (_huv0 : u * v ≠ 0)
    (_hne : u ^ 2 ≠ v ^ 2)
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z) :
    Int.gcd Z (2 * v ^ 2) = 1 := by
  rw [Int.gcd_eq_natAbs, ← Nat.coprime_iff_gcd_eq_one]
  refine Nat.coprime_of_dvd' ?_
  intro p hp hpZ hpLeg
  have hpZ_int : (p : ℤ) ∣ Z := (Int.natCast_dvd).mpr hpZ
  have hpLeg_int : (p : ℤ) ∣ 2 * v ^ 2 := (Int.natCast_dvd).mpr hpLeg
  rcases prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp hpLeg_int with hp2 | hpv_nat
  · exfalso
    have hZodd : Odd Z := quarticA_oppParity_Z_odd
      (u := u) (v := v) (Z := Z) hopp hA
    have h2Z : (2 : ℤ) ∣ Z := by
      simpa [hp2] using hpZ_int
    have hZeven : Even Z := by
      exact even_iff_two_dvd.mpr h2Z
    exact (Int.not_even_iff_odd.mpr hZodd) hZeven
  · have hpv_int : (p : ℤ) ∣ v := (Int.natCast_dvd).mpr hpv_nat
    have hAeq :
        Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
      simpa [QuarticA] using hA
    have hpZ2 : (p : ℤ) ∣ Z ^ 2 :=
      dvd_pow hpZ_int (by norm_num : 2 ≠ 0)
    have hprod :
        (p : ℤ) ∣ (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
      simpa [hAeq] using hpZ2
    have hpv2 : (p : ℤ) ∣ v ^ 2 :=
      dvd_pow hpv_int (by norm_num : 2 ≠ 0)
    have hpv4 : (p : ℤ) ∣ v ^ 4 :=
      dvd_pow hpv_int (by norm_num : 4 ≠ 0)
    have hterm1 : (p : ℤ) ∣ 2 * u ^ 2 * v ^ 2 := by
      convert dvd_mul_of_dvd_right hpv2 ((2 : ℤ) * u ^ 2) using 1
    have hterm2 : (p : ℤ) ∣ 3 * v ^ 4 :=
      dvd_mul_of_dvd_right hpv4 3
    have htail : (p : ℤ) ∣ 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4 :=
      dvd_sub hterm1 hterm2
    have hfac_expand :
        (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) =
          u ^ 4 + 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4 := by
      ring
    rw [hfac_expand] at hprod
    have hpu4' :
        (p : ℤ) ∣
          (u ^ 4 + 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4) -
            (2 * u ^ 2 * v ^ 2 - 3 * v ^ 4) :=
      dvd_sub hprod htail
    have hpu4 : (p : ℤ) ∣ u ^ 4 := by
      convert hpu4' using 1
      ring
    have hpu_int : (p : ℤ) ∣ u := Int.Prime.dvd_pow' hp hpu4
    have hpu_nat : p ∣ u.natAbs := (Int.natCast_dvd).mp hpu_int
    have hp_gcd : p ∣ Int.gcd u v := by
      rw [Int.gcd_eq_natAbs]
      exact Nat.dvd_gcd hpu_nat hpv_nat
    simpa [hcop] using hp_gcd

theorem quarticA_paramBridge_of_parity_cases
    (hParity : QuarticAPrimitiveParitySplit)
    (hOpp : QuarticAOppParityParamBridge)
    (hOddOdd : QuarticAOddOddParamBridge) :
    QuarticAParamBridge := by
  intro u v Z hcop huv0 hne hA
  rcases hParity hcop huv0 hA with hOp | hOo
  · exact hOpp hcop huv0 hne hOp hA
  · exact hOddOdd hcop huv0 hne hOo.1 hOo.2 hA

theorem quarticAOppParityParamBridge_of_leg_coprime
    (hlegcop_of_quarticA :
      ∀ {u v Z : ℤ},
        Int.gcd u v = 1 →
        u * v ≠ 0 →
        u ^ 2 ≠ v ^ 2 →
        ((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) →
        QuarticA u v Z →
        Int.gcd Z (2 * v ^ 2) = 1) :
    QuarticAOppParityParamBridge := by
  intro u v Z hcop huv0 hne hopp hA
  exact quarticA_eisensteinParam_of_oppParity_with_leg_coprime
    (u := u) (v := v) (Z := Z)
    hcop huv0 hne hopp hA
      (hlegcop_of_quarticA
        (u := u) (v := v) (Z := Z)
        hcop huv0 hne hopp hA)

theorem quarticAOddOddRSDataTheorem_checked :
    QuarticAOddOddRSDataTheorem := by
  exact
    QuarticAOddOddRSDataTheorem_of_dividedPrimitive_and_classification
      quarticAOddOddDividedTriplePrimitive
      quarticA_oddOddRSDataOfPrimitiveDividedTripleTheorem

theorem quarticAOddOddParamBridge_checked :
    QuarticAOddOddParamBridge := by
  exact
    QuarticAOddOddParamBridge_of_RSDataTheorem
      quarticAOddOddRSDataTheorem_checked

theorem quarticAOppParityParamBridge_checked :
    QuarticAOppParityParamBridge := by
  refine quarticAOppParityParamBridge_of_leg_coprime ?_
  intro u v Z hcop huv0 hne hopp hA
  exact quarticA_oppParity_leg_coprime
    (u := u) (v := v) (Z := Z)
    hcop huv0 hne hopp hA

theorem quarticAParamBridge_checked :
    QuarticAParamBridge := by
  exact quarticA_paramBridge_of_parity_cases
    quarticAPrimitiveParitySplit_proof
    quarticAOppParityParamBridge_checked
    quarticAOddOddParamBridge_checked

theorem quarticA_Z_ne_zero_of_nontrivial {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    Z ≠ 0 := by
  have hv0 : v ≠ 0 := by
    intro hv
    exact huv0 (by simp [hv])
  have hleft : 0 < u ^ 2 - v ^ 2 :=
    quarticA_left_factor_pos (u := u) (v := v) (Z := Z) hv0 hne hA
  have hright : 0 < u ^ 2 + 3 * v ^ 2 :=
    quarticA_right_factor_pos (u := u) (v := v) hv0
  have hprod : 0 < (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) :=
    mul_pos hleft hright
  dsimp [QuarticA] at hA
  intro hZ
  have hzero : (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) = 0 := by
    rw [← hA, hZ]
    ring
  exact (ne_of_gt hprod) hzero

theorem quarticB_sum_factor_halves_odd {u v : ℤ}
    (hu : Odd u) (hv : Odd v) :
    ∃ b : ℤ, u ^ 2 + v ^ 2 = 2 * b ∧ Odd b := by
  rcases hu with ⟨m, hm⟩
  rcases hv with ⟨n, hn⟩
  subst u
  subst v
  refine ⟨2 * m ^ 2 + 2 * m + 2 * n ^ 2 + 2 * n + 1, ?_, ?_⟩
  · ring
  · refine ⟨m ^ 2 + m + n ^ 2 + n, ?_⟩
    ring

theorem quarticB_twist_factor_halves_odd {u v : ℤ}
    (hu : Odd u) (hv : Odd v) :
    ∃ a : ℤ, 3 * u ^ 2 - v ^ 2 = 2 * a ∧ Odd a := by
  rcases hu with ⟨m, hm⟩
  rcases hv with ⟨n, hn⟩
  subst u
  subst v
  refine ⟨6 * m ^ 2 + 6 * m - 2 * n ^ 2 - 2 * n + 1, ?_, ?_⟩
  · ring
  · refine ⟨3 * m ^ 2 + 3 * m - n ^ 2 - n, ?_⟩
    ring

theorem quarticB_sum_sq_pos_of_mul_ne_zero {u v : ℤ}
    (huv0 : u * v ≠ 0) :
    0 < u ^ 2 + v ^ 2 := by
  have hu0 : u ≠ 0 := by
    intro hu
    exact huv0 (by simp [hu])
  have hv0 : v ≠ 0 := by
    intro hv
    exact huv0 (by simp [hv])
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu0
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv0
  nlinarith

theorem quarticB_left_factor_nonneg_of_square_product {A B Z : ℤ}
    (hBpos : 0 < B) (h : Z ^ 2 = A * B) :
    0 ≤ A := by
  have hprod : 0 ≤ A * B := by
    rw [← h]
    exact sq_nonneg Z
  by_contra hneg
  have hAlt : A < 0 := lt_of_not_ge hneg
  have hprodNeg : A * B < 0 := mul_neg_of_neg_of_pos hAlt hBpos
  nlinarith

theorem quarticB_left_factor_pos {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (hne : 3 * u ^ 2 - v ^ 2 ≠ 0)
    (hB : QuarticB u v Z) :
    0 < 3 * u ^ 2 - v ^ 2 := by
  dsimp [QuarticB] at hB
  have hsumpos : 0 < u ^ 2 + v ^ 2 :=
    quarticB_sum_sq_pos_of_mul_ne_zero (u := u) (v := v) huv0
  have hnonneg : 0 ≤ 3 * u ^ 2 - v ^ 2 :=
    quarticB_left_factor_nonneg_of_square_product
      (A := 3 * u ^ 2 - v ^ 2) (B := u ^ 2 + v ^ 2) (Z := Z)
      hsumpos hB
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem nat_coprime_mul_eq_sq {a b z : ℕ}
    (hcop : Nat.Coprime a b)
    (h : a * b = z ^ 2) :
    ∃ r s : ℕ, a = r ^ 2 ∧ b = s ^ 2 := by
  have hgcd : IsUnit (GCDMonoid.gcd a b) := by
    rw [gcd_eq_nat_gcd, hcop.gcd_eq_one]
    exact isUnit_one
  obtain ⟨r, hr⟩ :=
    exists_eq_pow_of_mul_eq_pow
      (α := ℕ) (a := a) (b := b) (c := z) (k := 2) hgcd h
  have hgcd' : IsUnit (GCDMonoid.gcd b a) := by
    rw [gcd_eq_nat_gcd, Nat.gcd_comm, hcop.gcd_eq_one]
    exact isUnit_one
  have h' : b * a = z ^ 2 := by
    simpa [mul_comm] using h
  obtain ⟨s, hs⟩ :=
    exists_eq_pow_of_mul_eq_pow
      (α := ℕ) (a := b) (b := a) (c := z) (k := 2) hgcd' h'
  exact ⟨r, s, hr, hs⟩

theorem int_coprime_mul_eq_sq_of_nonneg {a b z : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcop : Int.gcd a b = 1)
    (h : a * b = z ^ 2) :
    ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2 := by
  have hcopNat : Nat.Coprime a.natAbs b.natAbs := by
    change Nat.gcd a.natAbs b.natAbs = 1
    simpa [Int.gcd_eq_natAbs] using hcop
  have hnat : a.natAbs * b.natAbs = z.natAbs ^ 2 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs h
  obtain ⟨r, s, hr, hs⟩ := nat_coprime_mul_eq_sq hcopNat hnat
  refine ⟨(r : ℤ), (s : ℤ), ?_, ?_⟩
  · have ha_abs : (a.natAbs : ℤ) = a := by
      rw [Int.natCast_natAbs, abs_of_nonneg ha]
    rw [← ha_abs, hr]
    norm_num
  · have hb_abs : (b.natAbs : ℤ) = b := by
      rw [Int.natCast_natAbs, abs_of_nonneg hb]
    rw [← hb_abs, hs]
    norm_num

theorem gcd_eq_one_of_square_factors_gcd_eq_one {a b m n : ℤ}
    (hcop : Int.gcd a b = 1)
    (ha : a = m ^ 2)
    (hb : b = n ^ 2) :
    Int.gcd m n = 1 := by
  have hsqcop : IsCoprime (m ^ 2) (n ^ 2) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [← ha, ← hb] using hcop
  have hmn : IsCoprime m n := by
    exact (IsCoprime.pow_iff (x := m) (y := n) (m := 2) (n := 2)
      (by norm_num) (by norm_num)).mp hsqcop
  exact Int.isCoprime_iff_gcd_eq_one.mp hmn

theorem sameSignSquareFactors_of_coprime_square_product {v a b : ℤ}
    (hab0 : a * b ≠ 0)
    (hcop : Int.gcd a b = 1)
    (hsq : a * b = v ^ 2) :
    SameSignSquareFactors a b := by
  have hv0 : v ≠ 0 := by
    intro hv
    exact hab0 (by rw [hsq, hv]; ring)
  have hprod_pos : 0 < a * b := by
    rw [hsq]
    exact sq_pos_of_ne_zero hv0
  rcases lt_trichotomy a 0 with ha_neg | ha_zero | ha_pos
  · have hb_neg : b < 0 := by
      by_contra hnot
      have hb_nonneg : 0 ≤ b := le_of_not_gt hnot
      have hprod_nonpos : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha_neg) hb_nonneg
      linarith
    have hnegcop : Int.gcd (-a) (-b) = 1 := by
      simpa using hcop
    have hnegprod : (-a) * (-b) = v ^ 2 := by
      simpa using hsq
    obtain ⟨m, n, hm, hn⟩ :=
      int_coprime_mul_eq_sq_of_nonneg
        (show 0 ≤ -a by linarith)
        (show 0 ≤ -b by linarith)
        hnegcop hnegprod
    have hmn0 : m * n ≠ 0 := by
      intro hmn
      rcases mul_eq_zero.mp hmn with hm0 | hn0
      · have ha0 : a = 0 := by
          rw [show a = -(-a) by ring, hm, hm0]
          ring
        linarith
      · have hb0 : b = 0 := by
          rw [show b = -(-b) by ring, hn, hn0]
          ring
        linarith
    have hmn : Int.gcd m n = 1 :=
      gcd_eq_one_of_square_factors_gcd_eq_one hnegcop hm hn
    refine ⟨m, n, hmn0, hmn, Or.inr ⟨?_, ?_⟩⟩
    · rw [show a = -(-a) by ring, hm]
    · rw [show b = -(-b) by ring, hn]
  · exfalso
    exact hab0 (by simp [ha_zero])
  · have hb_pos : 0 < b := by
      by_contra hnot
      have hb_nonpos : b ≤ 0 := le_of_not_gt hnot
      have hprod_nonpos : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha_pos) hb_nonpos
      linarith
    obtain ⟨m, n, hm, hn⟩ :=
      int_coprime_mul_eq_sq_of_nonneg
        (le_of_lt ha_pos)
        (le_of_lt hb_pos)
        hcop hsq
    have hmn0 : m * n ≠ 0 := by
      intro hmn
      rcases mul_eq_zero.mp hmn with hm0 | hn0
      · have ha0 : a = 0 := by
          rw [hm, hm0]
          ring
        linarith
      · have hb0 : b = 0 := by
          rw [hn, hn0]
          ring
        linarith
    have hmn : Int.gcd m n = 1 :=
      gcd_eq_one_of_square_factors_gcd_eq_one hcop hm hn
    exact ⟨m, n, hmn0, hmn, Or.inl ⟨hm, hn⟩⟩

theorem coprimeSquareProductExtraction :
    CoprimeSquareProductExtraction := by
  intro v a b hab0 hcop hsq
  exact sameSignSquareFactors_of_coprime_square_product hab0 hcop hsq

def NontrivialEisensteinQuarticResidual : Prop :=
  ∃ m n c : ℤ,
    m * n ≠ 0 ∧
    Int.gcd m n = 1 ∧
    m ^ 2 ≠ n ^ 2 ∧
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4

private theorem sameSignSquareFactors_eq_of_diag {a b m n : ℤ}
    (hdiag : m ^ 2 = n ^ 2)
    (hsign :
      (a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2))) :
    a = b := by
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨ha, hb⟩
    rw [ha, hb, hdiag]
  · rcases hneg with ⟨ha, hb⟩
    rw [ha, hb, hdiag]

private theorem square_eq_of_param_of_ab_eq {u v a b : ℤ}
    (hab_eq : a = b)
    (hab_square : a * b = v ^ 2)
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2) :
    u ^ 2 = v ^ 2 := by
  calc
    u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
    _ = a * b := by
      rw [hab_eq]
      ring
    _ = v ^ 2 := hab_square

theorem sameSignSquareFactors_nondiagonal_of_quarticA_ne {u v a b m n : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hab_square : a * b = v ^ 2)
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsign :
      (a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2))) :
    m ^ 2 ≠ n ^ 2 := by
  intro hdiag
  have hab_eq : a = b :=
    sameSignSquareFactors_eq_of_diag (a := a) (b := b) hdiag hsign
  have huv : u ^ 2 = v ^ 2 :=
    square_eq_of_param_of_ab_eq
      (u := u) (v := v) (a := a) (b := b)
      hab_eq hab_square hu
  exact hne huv

private theorem eisenstein_quartic_eq_of_signedSquares {u a b m n : ℤ}
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsign :
      (a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2))) :
    u ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = (m ^ 2) ^ 2 - (m ^ 2) * (n ^ 2) + (n ^ 2) ^ 2 := by
        rw [ha, hb]
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        ring
  · rcases hneg with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = (-(m ^ 2)) ^ 2 - (-(m ^ 2)) * (-(n ^ 2)) + (-(n ^ 2)) ^ 2 := by
        rw [ha, hb]
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        ring

theorem nontrivialEisensteinQuarticResidual_of_param_of_signedSquares {u v a b : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hab_square : a * b = v ^ 2)
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsq : SameSignSquareFactors a b) :
    NontrivialEisensteinQuarticResidual := by
  rcases hsq with ⟨m, n, hmn0, hcop, hsign⟩
  refine ⟨m, n, u, hmn0, hcop, ?_, ?_⟩
  · exact sameSignSquareFactors_nondiagonal_of_quarticA_ne
      (u := u) (v := v) (a := a) (b := b) (m := m) (n := n)
      hne hab_square hu hsign
  · exact eisenstein_quartic_eq_of_signedSquares
      (u := u) (a := a) (b := b) (m := m) (n := n)
      hu hsign

def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

/-- Rational affine Eisenstein quartic `y² = x⁴ - x² + 1`. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- The rational x-coordinate classification for the Eisenstein quartic. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1

/-- The elliptic curve model used for the rational Eisenstein quartic. -/
def E24 (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4

/-- The shifted model `E1 : Y² = X(X-1)(X+3)`, related to `E24` by
`X = U - 1`. -/
def E1 (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 1) * (X + 3)

/-- The `X`-coordinate classification on the shifted model. -/
def E1XCoordinateClassification : Prop :=
  ∀ {X Y : ℚ}, E1 X Y →
    X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3

/-- The translation `X = U - 1` sends `E24` to `E1`. -/
theorem e24_to_e1_shift {U V : ℚ} (h : E24 U V) :
    E1 (U - 1) V := by
  unfold E24 at h
  unfold E1
  ring_nf at h ⊢
  exact h

/-- The inverse translation `U = X + 1` sends `E1` to `E24`. -/
theorem e1_to_e24_shift {X Y : ℚ} (h : E1 X Y) :
    E24 (X + 1) Y := by
  unfold E1 at h
  unfold E24
  ring_nf at h ⊢
  exact h

/-- The `U` coordinate of the rational map `C12 → E24`. -/
def C12ToE24U (x y : ℚ) : ℚ :=
  2 * (y + 1) / x ^ 2

/-- The `V` coordinate of the rational map `C12 → E24`. -/
def C12ToE24V (x y : ℚ) : ℚ :=
  x * (C12ToE24U x y ^ 2 - 4) / 2

/-- Residual hard input: the possible `U`-coordinates on `E24`. -/
def E24XCoordinateClassification : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    U = -2 ∨ U = 1 ∨ U = 2 ∨ U = 0 ∨ U = 4

/-- The shifted `E1` coordinate list implies the `E24` `U`-coordinate list. -/
theorem e24XCoordinateClassification_of_e1X
    (hE1x : E1XCoordinateClassification) :
    E24XCoordinateClassification := by
  intro U V hE24
  have hE1 : E1 (U - 1) V := e24_to_e1_shift hE24
  rcases hE1x hE1 with hXm3 | hX0 | hX1 | hXm1 | hX3
  · left
    linarith
  · right; left
    linarith
  · right; right; left
    linarith
  · right; right; right; left
    linarith
  · right; right; right; right
    linarith

private theorem c12_to_e24_U_relation_clear_den {x y : ℚ}
    (hC : RatQuarticEisenstein x y) :
    (2 * (y + 1)) ^ 2 - 4 * (x ^ 2) ^ 2 =
      4 * (2 * (y + 1)) - 4 * x ^ 2 := by
  unfold RatQuarticEisenstein at hC
  ring_nf at hC ⊢
  nlinarith

/-- The denominator-cleared relation for the `U` coordinate of the `C12 → E24` map. -/
theorem c12_to_e24_U_relation {x y : ℚ}
    (hC : RatQuarticEisenstein x y) (hx : x ≠ 0) :
    x ^ 2 * (C12ToE24U x y ^ 2 - 4) =
      4 * (C12ToE24U x y - 1) := by
  set U : ℚ := C12ToE24U x y with hU
  set z : ℚ := x ^ 2 with hz
  set a : ℚ := 2 * (y + 1) with ha
  have hz_ne : z ≠ 0 := by
    rw [hz]
    exact pow_ne_zero 2 hx
  have hUz : U * z = a := by
    rw [hU, hz, ha]
    unfold C12ToE24U
    exact div_mul_cancel₀ (2 * (y + 1)) (pow_ne_zero 2 hx)
  have hclear : a ^ 2 - 4 * z ^ 2 = 4 * a - 4 * z := by
    rw [ha, hz]
    exact c12_to_e24_U_relation_clear_den hC
  apply mul_right_cancel₀ hz_ne
  calc
    (z * (U ^ 2 - 4)) * z = (U * z) ^ 2 - 4 * z ^ 2 := by
      ring
    _ = a ^ 2 - 4 * z ^ 2 := by
      rw [hUz]
    _ = 4 * a - 4 * z := hclear
    _ = (4 * (U - 1)) * z := by
      rw [← hUz]
      ring

private theorem e24_of_U_relation {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1)) :
    E24 U (x * (U ^ 2 - 4) / 2) := by
  unfold E24
  calc
    (x * (U ^ 2 - 4) / 2) ^ 2
        = (x ^ 2 * (U ^ 2 - 4)) * (U ^ 2 - 4) / 4 := by
      ring
    _ = (4 * (U - 1)) * (U ^ 2 - 4) / 4 := by
      rw [hrel]
    _ = U ^ 3 - U ^ 2 - 4 * U + 4 := by
      ring

/-- The rational map from the nonzero-`x` part of `C12` lands on `E24`. -/
theorem c12_to_e24_map_correct {x y : ℚ}
    (hC : RatQuarticEisenstein x y) (hx : x ≠ 0) :
    E24 (C12ToE24U x y) (C12ToE24V x y) := by
  unfold C12ToE24V
  exact e24_of_U_relation (x := x) (U := C12ToE24U x y)
    (c12_to_e24_U_relation hC hx)

private theorem c12_relation_false_of_U_eq_neg_two {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = -2) : False := by
  rw [hU] at hrel
  norm_num at hrel

private theorem c12_relation_false_of_U_eq_one {x U : ℚ}
    (hx : x ≠ 0)
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 1) : False := by
  rw [hU] at hrel
  norm_num at hrel
  exact hx hrel

private theorem c12_relation_false_of_U_eq_two {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 2) : False := by
  rw [hU] at hrel
  norm_num at hrel

private theorem c12_relation_x_sq_eq_one_of_U_eq_zero {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 0) :
    x ^ 2 = 1 := by
  rw [hU] at hrel
  norm_num at hrel
  rcases hrel with hx1 | hxm1
  · rw [hx1]
    norm_num
  · rw [hxm1]
    norm_num

private theorem c12_relation_x_sq_eq_one_of_U_eq_four {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 4) :
    x ^ 2 = 1 := by
  rw [hU] at hrel
  norm_num at hrel
  rcases hrel with hx1 | hxm1
  · rw [hx1]
    norm_num
  · rw [hxm1]
    norm_num

/-- The `E24` `U`-coordinate classification forces the quartic `x`-classification. -/
theorem ratQuarticEisensteinXClassification_of_e24_x
    (hE24x : E24XCoordinateClassification) :
    RatQuarticEisensteinXClassification := by
  intro x y hC
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    have hx : x ≠ 0 := hx0
    have hrel :
        x ^ 2 * (C12ToE24U x y ^ 2 - 4) =
          4 * (C12ToE24U x y - 1) :=
      c12_to_e24_U_relation hC hx
    have hE24 : E24 (C12ToE24U x y) (C12ToE24V x y) :=
      c12_to_e24_map_correct hC hx
    rcases hE24x hE24 with hU | hU | hU | hU | hU
    · exact False.elim (c12_relation_false_of_U_eq_neg_two hrel hU)
    · exact False.elim (c12_relation_false_of_U_eq_one hx hrel hU)
    · exact False.elim (c12_relation_false_of_U_eq_two hrel hU)
    · exact c12_relation_x_sq_eq_one_of_U_eq_zero hrel hU
    · exact c12_relation_x_sq_eq_one_of_U_eq_four hrel hU

theorem rat_div_pow_two_mul_pow_two (a b : ℚ) (hb : b ≠ 0) :
    (a / b) ^ 2 * b ^ 2 = a ^ 2 := by
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  calc
    (a / b) ^ 2 * b ^ 2
        = (a ^ 2 / b ^ 2) * b ^ 2 := by
            rw [div_pow]
    _ = a ^ 2 := by
            exact div_mul_cancel₀ (a ^ 2) hb2

theorem rat_div_pow_four_mul_pow_four (a b : ℚ) (hb : b ≠ 0) :
    (a / b) ^ 4 * b ^ 4 = a ^ 4 := by
  have hb4 : b ^ 4 ≠ 0 := pow_ne_zero 4 hb
  calc
    (a / b) ^ 4 * b ^ 4
        = (a ^ 4 / b ^ 4) * b ^ 4 := by
            rw [div_pow]
    _ = a ^ 4 := by
            exact div_mul_cancel₀ (a ^ 4) hb4

theorem rat_c_over_nsq_square_mul_denom_four (c n : ℚ) (hn : n ≠ 0) :
    (c / n ^ 2) ^ 2 * n ^ 4 = c ^ 2 := by
  calc
    (c / n ^ 2) ^ 2 * n ^ 4
        = (c / n ^ 2) ^ 2 * (n ^ 2) ^ 2 := by
            rw [show n ^ 4 = (n ^ 2) ^ 2 by ring]
    _ = c ^ 2 := by
            exact rat_div_pow_two_mul_pow_two c (n ^ 2) (pow_ne_zero 2 hn)

theorem rat_div_square_mul_denom_four (m n : ℚ) (hn : n ≠ 0) :
    (m / n) ^ 2 * n ^ 4 = m ^ 2 * n ^ 2 := by
  calc
    (m / n) ^ 2 * n ^ 4
        = (m / n) ^ 2 * (n ^ 2 * n ^ 2) := by
            rw [show n ^ 4 = n ^ 2 * n ^ 2 by ring]
    _ = ((m / n) ^ 2 * n ^ 2) * n ^ 2 := by
            rw [← mul_assoc]
    _ = m ^ 2 * n ^ 2 := by
            rw [rat_div_pow_two_mul_pow_two m n hn]

theorem rat_quartic_eisenstein_rhs_mul_denom
    (m n : ℚ) (hn : n ≠ 0) :
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4 =
      m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  have h4 : (m / n) ^ 4 * n ^ 4 = m ^ 4 :=
    rat_div_pow_four_mul_pow_four m n hn
  have h2 : (m / n) ^ 2 * n ^ 4 = m ^ 2 * n ^ 2 :=
    rat_div_square_mul_denom_four m n hn
  have hdistrib (A B D : ℚ) : (A - B + 1) * D = A * D - B * D + D := by
    ring
  calc
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4
        = (m / n) ^ 4 * n ^ 4 - (m / n) ^ 2 * n ^ 4 + n ^ 4 := by
            simpa using hdistrib ((m / n) ^ 4) ((m / n) ^ 2) (n ^ 4)
    _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
            rw [h4, h2]

theorem int_to_ratQuarticEisenstein {m n c : ℤ}
    (hn : n ≠ 0)
    (hc : c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) :
    RatQuarticEisenstein ((m : ℚ) / (n : ℚ)) ((c : ℚ) / (n : ℚ) ^ 2) := by
  unfold RatQuarticEisenstein
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hn4Q : (n : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 hnQ
  have hcQ :
      (c : ℚ) ^ 2 =
        (m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4 := by
    exact_mod_cast hc
  have hmul :
      (((c : ℚ) / (n : ℚ) ^ 2) ^ 2) * (n : ℚ) ^ 4 =
        (((m : ℚ) / (n : ℚ)) ^ 4 - ((m : ℚ) / (n : ℚ)) ^ 2 + 1) *
          (n : ℚ) ^ 4 := by
    calc
      (((c : ℚ) / (n : ℚ) ^ 2) ^ 2) * (n : ℚ) ^ 4
          = (c : ℚ) ^ 2 := by
              exact rat_c_over_nsq_square_mul_denom_four
                (c : ℚ) (n : ℚ) hnQ
      _ = (m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4 := hcQ
      _ = (((m : ℚ) / (n : ℚ)) ^ 4 - ((m : ℚ) / (n : ℚ)) ^ 2 + 1) *
            (n : ℚ) ^ 4 := by
              symm
              exact rat_quartic_eisenstein_rhs_mul_denom
                (m : ℚ) (n : ℚ) hnQ
  exact mul_right_cancel₀ hn4Q hmul

private theorem int_eq_zero_of_rat_div_eq_zero {m n : ℤ}
    (hn : n ≠ 0)
    (h : (m : ℚ) / (n : ℚ) = 0) :
    m = 0 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hmQ : (m : ℚ) = 0 := by
    calc
      (m : ℚ) = ((m : ℚ) / (n : ℚ)) * (n : ℚ) := by
          symm
          exact div_mul_cancel₀ (m : ℚ) hnQ
      _ = 0 * (n : ℚ) := by
          rw [h]
      _ = 0 := by
          ring
  exact_mod_cast hmQ

private theorem int_sq_eq_of_rat_div_sq_eq_one {m n : ℤ}
    (hn : n ≠ 0)
    (h : ((m : ℚ) / (n : ℚ)) ^ 2 = 1) :
    m ^ 2 = n ^ 2 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hQ : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 := by
    calc
      (m : ℚ) ^ 2
          = (((m : ℚ) / (n : ℚ)) ^ 2) * (n : ℚ) ^ 2 := by
              symm
              exact rat_div_pow_two_mul_pow_two (m : ℚ) (n : ℚ) hnQ
      _ = 1 * (n : ℚ) ^ 2 := by
          rw [h]
      _ = (n : ℚ) ^ 2 := by
          ring
  exact_mod_cast hQ

theorem eisensteinQuarticSquareClassification_of_rat_x
    (hRat : RatQuarticEisensteinXClassification) :
    EisensteinQuarticSquareClassification := by
  intro m n c hc
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  · have hcurve :
        RatQuarticEisenstein ((m : ℚ) / (n : ℚ)) ((c : ℚ) / (n : ℚ) ^ 2) :=
      int_to_ratQuarticEisenstein (m := m) (n := n) (c := c) hn hc
    rcases hRat hcurve with hx0 | hx1
    · exact Or.inl (int_eq_zero_of_rat_div_eq_zero (m := m) (n := n) hn hx0)
    · exact Or.inr
        (Or.inr (int_sq_eq_of_rat_div_sq_eq_one (m := m) (n := n) hn hx1))

/-- Double-leg right-triangle obstruction over `ℚ`. -/
def DoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h ^ 2 = x ^ 2 + y ^ 2 →
    k ^ 2 = (2 * x) ^ 2 + y ^ 2 →
    x = 0 ∨ y = 0

private theorem doubleLeg_u_sq_sub_y_sq {x y h u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hu : u = h + x) :
    u ^ 2 - y ^ 2 = 2 * u * x := by
  rw [hu]
  nlinarith [hh]

private theorem doubleLeg_quartic_num {x y h k u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2)
    (hu : u = h + x) :
    (k * u) ^ 2 = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := by
  have hrel : u ^ 2 - y ^ 2 = 2 * u * x :=
    doubleLeg_u_sq_sub_y_sq hh hu
  calc
    (k * u) ^ 2 = k ^ 2 * u ^ 2 := by ring
    _ = ((2 * x) ^ 2 + y ^ 2) * u ^ 2 := by rw [hk]
    _ = (2 * u * x) ^ 2 + u ^ 2 * y ^ 2 := by ring
    _ = (u ^ 2 - y ^ 2) ^ 2 + u ^ 2 * y ^ 2 := by rw [← hrel]
    _ = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := by
      ring

private theorem doubleLeg_ratQuarticEisenstein_point {x y h k u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2)
    (hu : u = h + x)
    (hy : y ≠ 0) :
    RatQuarticEisenstein (u / y) (k * u / y ^ 2) := by
  unfold RatQuarticEisenstein
  have hnum : (k * u) ^ 2 = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 :=
    doubleLeg_quartic_num hh hk hu
  have hy2_ne : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hy4_ne : y ^ 4 ≠ 0 := pow_ne_zero 4 hy
  have hleft : ((k * u / y ^ 2) ^ 2) * y ^ 4 = (k * u) ^ 2 := by
    field_simp [hy, hy2_ne, hy4_ne]
  have hright :
      ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 =
        u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := by
    field_simp [hy, hy2_ne, hy4_ne]
  have hmul :
      ((k * u / y ^ 2) ^ 2) * y ^ 4 =
        ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 := by
    calc
      ((k * u / y ^ 2) ^ 2) * y ^ 4 = (k * u) ^ 2 := hleft
      _ = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := hnum
      _ = ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 := hright.symm
  exact mul_right_cancel₀ hy4_ne hmul

/-- The rational Eisenstein quartic classification proves the double-leg
right-triangle obstruction. -/
theorem doubleLeg_of_ratQuarticEisenstein
    (hRat : RatQuarticEisensteinXClassification) :
    DoubleLegRightTrianglesDegenerate := by
  intro x y h k hh hk
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr hy
  let u : ℚ := h + x
  have hu : u = h + x := rfl
  by_cases hu0 : u = 0
  · have hh_neg : h = -x := by
      calc
        h = u - x := by rw [hu]; ring
        _ = -x := by rw [hu0]; ring
    have hhx2 : h ^ 2 = x ^ 2 := by
      rw [hh_neg]
      ring
    have hy_sq : y ^ 2 = 0 := by
      nlinarith [hh, hhx2]
    exact Or.inr (sq_eq_zero_iff.mp hy_sq)
  · have hC : RatQuarticEisenstein (u / y) (k * u / y ^ 2) :=
      doubleLeg_ratQuarticEisenstein_point hh hk hu hy
    rcases hRat hC with hr_zero | hr_sq
    · have hu_eq : u = (u / y) * y :=
        (div_mul_cancel₀ u hy).symm
      have hu_zero : u = 0 := by
        calc
          u = (u / y) * y := hu_eq
          _ = 0 := by rw [hr_zero]; ring
      exact False.elim (hu0 hu_zero)
    · have hu2_eq_y2 : u ^ 2 = y ^ 2 := by
        calc
          u ^ 2 = (u / y) ^ 2 * y ^ 2 := by
            symm
            rw [div_pow]
            exact div_mul_cancel₀ (u ^ 2) (pow_ne_zero 2 hy)
          _ = 1 * y ^ 2 := by rw [hr_sq]
          _ = y ^ 2 := by ring
      have hrel : u ^ 2 - y ^ 2 = 2 * u * x :=
        doubleLeg_u_sq_sub_y_sq hh hu
      have hprod : (2 * u) * x = 0 := by
        nlinarith [hrel, hu2_eq_y2]
      have h2u_ne : (2 * u : ℚ) ≠ 0 := by
        exact mul_ne_zero (by norm_num) hu0
      rcases mul_eq_zero.mp hprod with h2u | hx0
      · exact False.elim (h2u_ne h2u)
      · exact Or.inl hx0

def EisensteinQuarticPrimitiveClassification : Prop :=
  ∀ {m n c : ℤ},
    Int.gcd m n = 1 →
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

def EisensteinQuarticNoNontrivialPrimitive : Prop :=
  ∀ {m n c : ℤ},
    m * n ≠ 0 →
    Int.gcd m n = 1 →
    m ^ 2 ≠ n ^ 2 →
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    False

theorem eisensteinQuarticPrimitiveClassification_of_squareClassification
    (hClass : EisensteinQuarticSquareClassification) :
    EisensteinQuarticPrimitiveClassification := by
  intro m n c _hcop hc
  exact hClass (m := m) (n := n) (c := c) hc

theorem eisensteinQuarticNoNontrivialPrimitive_of_primitiveClassification
    (hClass : EisensteinQuarticPrimitiveClassification) :
    EisensteinQuarticNoNontrivialPrimitive := by
  intro m n c hmn0 hcop hdiag hc
  rcases hClass (m := m) (n := n) (c := c) hcop hc with hm0 | hn0 | hsq
  · exact hmn0 (by simp [hm0])
  · exact hmn0 (by simp [hn0])
  · exact hdiag hsq

theorem eisensteinQuarticNoNontrivialPrimitive_of_squareClassification
    (hClass : EisensteinQuarticSquareClassification) :
    EisensteinQuarticNoNontrivialPrimitive := by
  exact
    eisensteinQuarticNoNontrivialPrimitive_of_primitiveClassification
      (eisensteinQuarticPrimitiveClassification_of_squareClassification hClass)

theorem quarticA_to_eisensteinQuarticResidual_checked {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    EisensteinQuarticResidual := by
  exact
    quarticA_to_eisensteinQuarticResidual_of_bridge
      quarticAParamBridge_checked
      coprimeSquareProductExtraction
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

theorem quarticA_to_eisenstein_residual_statement_checked {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  exact
    quarticA_to_eisenstein_residual_statement_of_bridge
      quarticAParamBridge_checked
      coprimeSquareProductExtraction
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

def QuarticAToNontrivialEisensteinResidualStatement : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    QuarticA u v Z →
    NontrivialEisensteinQuarticResidual

theorem nontrivialEisensteinQuarticResidual_of_param_checked {u v : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hParam : QuarticAEisensteinParam u v) :
    NontrivialEisensteinQuarticResidual := by
  rcases hParam with ⟨a, b, hab0, hcop, hab_square, hu⟩
  exact nontrivialEisensteinQuarticResidual_of_param_of_signedSquares
    (u := u) (v := v) (a := a) (b := b)
    hne hab_square hu
    (sameSignSquareFactors_of_coprime_square_product
      (a := a) (b := b) (v := v) hab0 hcop hab_square)

theorem quarticA_to_nontrivial_eisenstein_residual_statement_checked :
    QuarticAToNontrivialEisensteinResidualStatement := by
  intro u v Z hcop huv0 hne hA
  exact nontrivialEisensteinQuarticResidual_of_param_checked
    (u := u) (v := v)
    hne
    (quarticAParamBridge_checked
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA)

theorem quarticA_no_solution_of_nontrivial_eisenstein_residual
    (hNo : EisensteinQuarticNoNontrivialPrimitive)
    (hResidual : QuarticAToNontrivialEisensteinResidualStatement)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  obtain ⟨m, n, c, hmn0, hmncop, hdiag, hc⟩ :=
    hResidual (u := u) (v := v) (Z := Z) hcop huv0 hne hA
  exact hNo (m := m) (n := n) (c := c) hmn0 hmncop hdiag hc

theorem quarticA_no_solution_of_eisensteinQuarticSquareClassification
    (hClass : EisensteinQuarticSquareClassification)
    (hResidual : QuarticAToNontrivialEisensteinResidualStatement)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  exact
    quarticA_no_solution_of_nontrivial_eisenstein_residual
      (eisensteinQuarticNoNontrivialPrimitive_of_squareClassification hClass)
      hResidual
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

theorem quarticA_no_solution_of_nontrivial_eisenstein_residual_checked
    (hNo : EisensteinQuarticNoNontrivialPrimitive)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  exact
    quarticA_no_solution_of_nontrivial_eisenstein_residual
      hNo
      quarticA_to_nontrivial_eisenstein_residual_statement_checked
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

theorem quarticA_no_solution_of_eisensteinQuarticSquareClassification_checked
    (hClass : EisensteinQuarticSquareClassification)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  exact
    quarticA_no_solution_of_eisensteinQuarticSquareClassification
      hClass
      quarticA_to_nontrivial_eisenstein_residual_statement_checked
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

theorem quarticB_half_factors_coprime {u v a b : ℤ}
    (hcop : Int.gcd u v = 1)
    (haOdd : Odd a)
    (ha : 3 * u ^ 2 - v ^ 2 = 2 * a)
    (hb : u ^ 2 + v ^ 2 = 2 * b) :
    Int.gcd a b = 1 := by
  apply int_gcd_eq_one_of_no_common_prime
  intro p hp hpa hpb
  have hpZprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  by_cases hp2 : p = 2
  · subst hp2; exact (int_not_two_dvd_of_odd haOdd) hpa
  · have hpnot2 := odd_nat_prime_int_not_dvd_two hp hp2
    have hpf1 : (p : ℤ) ∣ 3 * u ^ 2 - v ^ 2 := by
      rw [ha]; exact dvd_mul_of_dvd_right hpa 2
    have hpf2 : (p : ℤ) ∣ u ^ 2 + v ^ 2 := by
      rw [hb]; exact dvd_mul_of_dvd_right hpb 2
    have hp4u2 : (p : ℤ) ∣ (2 * u) ^ 2 := by
      have := dvd_add hpf1 hpf2
      have heq : 3 * u ^ 2 - v ^ 2 + (u ^ 2 + v ^ 2) = (2 * u) ^ 2 := by ring
      rwa [heq] at this
    have hp2u : (p : ℤ) ∣ 2 * u := int_natPrime_dvd_of_dvd_sq hp hp4u2
    have hpu : (p : ℤ) ∣ u := by
      rcases hpZprime.dvd_or_dvd hp2u with h2 | hu
      · exact absurd h2 hpnot2
      · exact hu
    have hp4v2 : (p : ℤ) ∣ (2 * v) ^ 2 := by
      have h3f2 : (p : ℤ) ∣ 3 * (u ^ 2 + v ^ 2) := dvd_mul_of_dvd_right hpf2 3
      have := dvd_sub h3f2 hpf1
      have heq : 3 * (u ^ 2 + v ^ 2) - (3 * u ^ 2 - v ^ 2) = (2 * v) ^ 2 := by ring
      rwa [heq] at this
    have hp2v : (p : ℤ) ∣ 2 * v := int_natPrime_dvd_of_dvd_sq hp hp4v2
    have hpv : (p : ℤ) ∣ v := by
      rcases hpZprime.dvd_or_dvd hp2v with h2 | hv
      · exact absurd h2 hpnot2
      · exact hv
    have hpg : (p : ℤ) ∣ ((Int.gcd u v : ℕ) : ℤ) := Int.dvd_coe_gcd hpu hpv
    rw [hcop] at hpg; exact hpZprime.not_dvd_one hpg

theorem even_of_sq_eq_four_mul {Z t : ℤ}
    (h : Z ^ 2 = 4 * t) :
    Even Z := by
  rcases Int.even_or_odd Z with hEven | hOdd
  · exact hEven
  · exfalso
    have hOddSq : Odd (Z ^ 2) := hOdd.pow
    have hEvenSq : Even (Z ^ 2) := by
      rw [h]
      exact ⟨2 * t, by ring⟩
    exact (Int.not_even_iff_odd.mpr hOddSq) hEvenSq

lemma half_sum_diff_sum_sq (R S : ℤ) :
    (R + S) ^ 2 + (R - S) ^ 2 = 2 * (R ^ 2 + S ^ 2) := by
  ring

lemma half_sum_diff_twist_sq (R S : ℤ) :
    3 * (R + S) ^ 2 - (R - S) ^ 2 =
      2 * (R ^ 2 + 4 * R * S + S ^ 2) := by
  ring

lemma quartic_B_half_substitution (R S : ℤ) :
    ((3 * (R + S) ^ 2 - (R - S) ^ 2) *
      ((R + S) ^ 2 + (R - S) ^ 2)) =
      4 * (R ^ 2 + 4 * R * S + S ^ 2) * (R ^ 2 + S ^ 2) := by
  ring

theorem quartic_B_split_halves_to_pythagoreanQuarticRhs {u v r s R S : ℤ}
    (hsplit₁ : 3 * u ^ 2 - v ^ 2 = 2 * r ^ 2)
    (hsplit₂ : u ^ 2 + v ^ 2 = 2 * s ^ 2)
    (hu : u = R + S)
    (hv : v = R - S)
    (hRS0 : R * S ≠ 0)
    (hcop : Int.gcd R S = 1)
    (hpar : Odd (R + S)) :
    ∃ m n b : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      Odd (m + n) ∧
      b ^ 2 = pythagoreanQuarticRhs m n := by
  have hsRS : s ^ 2 = R ^ 2 + S ^ 2 := by
    have hsum := half_sum_diff_sum_sq R S
    rw [hu, hv] at hsplit₂
    nlinarith
  have hrRS : r ^ 2 = R ^ 2 + 4 * R * S + S ^ 2 := by
    have htwist := half_sum_diff_twist_sq R S
    rw [hu, hv] at hsplit₁
    nlinarith
  obtain ⟨m, n, hmn0, hmn, hmnpar, hquartic⟩ :=
    primitive_pythagorean_twist_to_pythagoreanQuarticRhs hRS0 hcop hpar hsRS hrRS
  exact ⟨m, n, r, hmn0, hmn, hmnpar, hquartic⟩

lemma odd_odd_split_as_sum_diff {u v : ℤ}
    (hu : Odd u) (hv : Odd v) :
    ∃ R S : ℤ, u = R + S ∧ v = R - S ∧ Odd (R + S) := by
  rcases hu with ⟨U, hU⟩
  rcases hv with ⟨V, hV⟩
  refine ⟨U + V + 1, U - V, ?_, ?_, ?_⟩
  · rw [hU]
    ring
  · rw [hV]
    ring
  · exact ⟨U, by ring⟩

lemma split_mul_ne_zero_of_sq_ne {u v R S : ℤ}
    (hu : u = R + S)
    (hv : v = R - S)
    (hsqne : u ^ 2 ≠ v ^ 2) :
    R * S ≠ 0 := by
  intro hRS
  apply hsqne
  rcases mul_eq_zero.mp hRS with hR | hS
  · calc
      u ^ 2 = (R + S) ^ 2 := by rw [hu]
      _ = (R - S) ^ 2 := by rw [hR]; ring
      _ = v ^ 2 := by rw [hv]
  · calc
      u ^ 2 = (R + S) ^ 2 := by rw [hu]
      _ = (R - S) ^ 2 := by rw [hS]; ring
      _ = v ^ 2 := by rw [hv]

lemma int_gcd_of_coprime_sum_diff {u v R S : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : u = R + S)
    (hv : v = R - S) :
    Int.gcd R S = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have huv : IsCoprime (R + S) (R - S) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [hu, hv] using hcop
  rcases huv with ⟨x, y, hxy⟩
  refine ⟨x + y, x - y, ?_⟩
  calc
    (x + y) * R + (x - y) * S =
        x * (R + S) + y * (R - S) := by ring
    _ = 1 := hxy

theorem quartic_B_to_pythagoreanQuarticRhs {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u) (hv : Odd v)
    (huv0 : u * v ≠ 0)
    (hne : 3 * u ^ 2 - v ^ 2 ≠ 0)
    (hsqne : u ^ 2 ≠ v ^ 2)
    (hB : QuarticB u v Z) :
    ∃ m n b : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      Odd (m + n) ∧
      b ^ 2 = pythagoreanQuarticRhs m n := by
  rcases quarticB_twist_factor_halves_odd hu hv with ⟨A, hA, hAOdd⟩
  rcases quarticB_sum_factor_halves_odd hu hv with ⟨B, hBhalf, _hBOdd⟩
  have hZsq_four : Z ^ 2 = 4 * (A * B) := by
    calc
      Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) := by
        simpa [QuarticB] using hB
      _ = (2 * A) * (2 * B) := by rw [hA, hBhalf]
      _ = 4 * (A * B) := by ring
  have hZeven : Even Z := even_of_sq_eq_four_mul hZsq_four
  rcases hZeven with ⟨c, hZc⟩
  have hABsq : A * B = c ^ 2 := by
    have h4 : 4 * (A * B) = 4 * c ^ 2 := by
      calc
        4 * (A * B) = Z ^ 2 := by rw [hZsq_four]
        _ = (2 * c) ^ 2 := by
          rw [hZc]
          ring
        _ = 4 * c ^ 2 := by ring
    omega
  have hleft_pos : 0 < 3 * u ^ 2 - v ^ 2 :=
    quarticB_left_factor_pos huv0 hne hB
  have hsum_pos : 0 < u ^ 2 + v ^ 2 :=
    quarticB_sum_sq_pos_of_mul_ne_zero huv0
  have hA_nonneg : 0 ≤ A := by
    have htwoApos : 0 < 2 * A := by
      rw [← hA]
      exact hleft_pos
    omega
  have hB_nonneg : 0 ≤ B := by
    have htwoBpos : 0 < 2 * B := by
      rw [← hBhalf]
      exact hsum_pos
    omega
  have hcopAB : Int.gcd A B = 1 :=
    quarticB_half_factors_coprime hcop hAOdd hA hBhalf
  rcases int_coprime_mul_eq_sq_of_nonneg hA_nonneg hB_nonneg hcopAB hABsq with
    ⟨r, s, hr, hs⟩
  have hsplit₁ : 3 * u ^ 2 - v ^ 2 = 2 * r ^ 2 := by
    calc
      3 * u ^ 2 - v ^ 2 = 2 * A := hA
      _ = 2 * r ^ 2 := by rw [hr]
  have hsplit₂ : u ^ 2 + v ^ 2 = 2 * s ^ 2 := by
    calc
      u ^ 2 + v ^ 2 = 2 * B := hBhalf
      _ = 2 * s ^ 2 := by rw [hs]
  rcases odd_odd_split_as_sum_diff hu hv with ⟨R, S, huRS, hvRS, hpar⟩
  have hRS0 : R * S ≠ 0 :=
    split_mul_ne_zero_of_sq_ne huRS hvRS hsqne
  have hcopRS : Int.gcd R S = 1 :=
    int_gcd_of_coprime_sum_diff hcop huRS hvRS
  exact quartic_B_split_halves_to_pythagoreanQuarticRhs
    hsplit₁ hsplit₂ huRS hvRS hRS0 hcopRS hpar

theorem pq_model_pythagorean_params (p q a b : ℤ)
    (ha : p ^ 2 + q ^ 2 = a ^ 2)
    (hb : p ^ 2 + 4 * p * q + q ^ 2 = b ^ 2)
    (hcop : Int.gcd p q = 1) :
    ∃ m n : ℤ,
      ((p = m ^ 2 - n ^ 2 ∧ q = 2 * m * n) ∨
        (p = 2 * m * n ∧ q = m ^ 2 - n ^ 2)) ∧
      (a = m ^ 2 + n ^ 2 ∨ a = -(m ^ 2 + n ^ 2)) ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      b ^ 2 = pythagoreanQuarticRhs m n := by
  have htrip : PythagoreanTriple p q a := by
    simpa [PythagoreanTriple, sq] using ha
  obtain ⟨m, n, hpq, ha', hmn, hpar⟩ :=
    PythagoreanTriple.coprime_classification.mp ⟨htrip, hcop⟩
  refine ⟨m, n, hpq, ha', hmn, hpar, ?_⟩
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [← hb, hp, hq]
    dsimp [pythagoreanQuarticRhs]
    ring
  · rw [← hb, hp, hq]
    dsimp [pythagoreanQuarticRhs]
    ring

theorem kubert_cover_pythagorean_params (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ p q a b m n : ℤ,
      T = p + q ∧ D = p - q ∧
      p ^ 2 + q ^ 2 = a ^ 2 ∧
      p ^ 2 + 4 * p * q + q ^ 2 = b ^ 2 ∧
      Int.gcd p q = 1 ∧
      ((Even p ∧ Odd q) ∨ (Odd p ∧ Even q)) ∧
      ((p = m ^ 2 - n ^ 2 ∧ q = 2 * m * n) ∨
        (p = 2 * m * n ∧ q = m ^ 2 - n ^ 2)) ∧
      (a = m ^ 2 + n ^ 2 ∨ a = -(m ^ 2 + n ^ 2)) ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      b ^ 2 = pythagoreanQuarticRhs m n := by
  obtain ⟨p, q, a, b, hT, hD, ha, hb, hpq, hpar⟩ :=
    kubert_cover_pq_model_primitive T D Y hDpos hcop h
  obtain ⟨m, n, hparam, ha', hmn, hmnpar, hbquartic⟩ :=
    pq_model_pythagorean_params p q a b ha hb hpq
  exact ⟨p, q, a, b, m, n, hT, hD, ha, hb, hpq, hpar,
    hparam, ha', hmn, hmnpar, hbquartic⟩

theorem kubert_cover_pythagorean_half_factors (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ m n b r s : ℤ,
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      b ^ 2 = pythagoreanQuarticRhs m n ∧
      pythagoreanQuarticCenter m n - b = 2 * r ∧
      pythagoreanQuarticCenter m n + b = 2 * s ∧
      r * s = 3 * m ^ 2 * n ^ 2 ∧
      ((Int.gcd r s : ℕ) : ℤ) ∣ (3 : ℤ) ∧
      (Int.gcd r s = 1 ∨ Int.gcd r s = 3) ∧
      Int.gcd r s = 1 ∧
      ((∃ a c : ℤ, (r = 3 * a ^ 2 ∨ r = -(3 * a ^ 2)) ∧
        (s = c ^ 2 ∨ s = -(c ^ 2))) ∨
      (∃ a c : ℤ, (r = a ^ 2 ∨ r = -(a ^ 2)) ∧
        (s = 3 * c ^ 2 ∨ s = -(3 * c ^ 2)))) ∧
      (m * n ≠ 0 →
        (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
          (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
        (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
          (r = -(a ^ 2) ∧ s = -(3 * c ^ 2))))) ∧
      (Int.gcd r s = 3 → ((3 : ℤ) ∣ m ∨ (3 : ℤ) ∣ n)) ∧
      (m * n = 0 → ((m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1))) := by
  obtain ⟨p, q, a, b, m, n, hT, hD, ha, hb, hpq, hpar,
    hparam, ha', hmn, hmnpar, hbquartic⟩ :=
    kubert_cover_pythagorean_params T D Y hDpos hcop h
  obtain ⟨r, s, hr, hs, hrs⟩ :=
    pythagorean_quartic_half_factorization_of_opposite_mod m n b hmnpar hbquartic
  have hgcd := pythagorean_quartic_half_factor_gcd_dvd_three m n b r s hmn hr hs hrs
  have hgcd_cases :=
    pythagorean_quartic_half_factor_gcd_eq_one_or_three m n b r s hmn hr hs hrs
  have hgcd_one := pythagorean_quartic_half_factor_gcd_eq_one m n b r s hmn hr hs hrs
  have hsplit := pythagorean_quartic_half_factor_split m n b r s hmn hr hs hrs
  have hsigned_split :
      m * n ≠ 0 →
        (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
          (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
        (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
          (r = -(a ^ 2) ∧ s = -(3 * c ^ 2)))) := by
    intro hnonzero
    exact pythagorean_quartic_half_factor_signed_split_of_nonzero
      m n b r s hmn hr hs hrs hnonzero
  have hthree_dvd_parameter :
      Int.gcd r s = 3 → ((3 : ℤ) ∣ m ∨ (3 : ℤ) ∣ n) := by
    intro hgcd_three
    exact pythagorean_quartic_half_factor_three_dvd_parameter_of_gcd_three
      m n r s hgcd_three hrs
  have haxis :
      m * n = 0 → ((m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1)) := by
    intro hzero
    exact pythagorean_quartic_axis_of_zero_product m n hmn hzero
  exact ⟨m, n, b, r, s, hmn, hmnpar, hbquartic, hr, hs, hrs,
    hgcd, hgcd_cases, hgcd_one, hsplit, hsigned_split, hthree_dvd_parameter, haxis⟩

theorem kubert_cover_residual_reduction (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    ∃ m n b : ℤ,
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      b ^ 2 = pythagoreanQuarticRhs m n ∧
      (((m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1)) ∨
        ∃ r s : ℤ,
          pythagoreanQuarticCenter m n - b = 2 * r ∧
          pythagoreanQuarticCenter m n + b = 2 * s ∧
          r * s = 3 * m ^ 2 * n ^ 2 ∧
          Int.gcd r s = 1 ∧
          (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
            (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
          (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
            (r = -(a ^ 2) ∧ s = -(3 * c ^ 2))))) := by
  obtain ⟨p, q, a, b, m, n, hT, hD, ha, hb, hpq, hpar,
    hparam, ha', hmn, hmnpar, hbquartic⟩ :=
    kubert_cover_pythagorean_params T D Y hDpos hcop h
  exact ⟨m, n, b, hmn, hmnpar, hbquartic,
    pythagorean_quartic_residual_reduction m n b hmn hmnpar hbquartic⟩

theorem kubert_cover_degenerate_or_signed_residual (T D Y : ℤ)
    (hDpos : 0 < D) (hcop : Int.gcd T D = 1)
    (h : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    (T = D ∨ T = -D) ∨
      ∃ m n b r s : ℤ,
        m * n ≠ 0 ∧
        Int.gcd m n = 1 ∧
        (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
        b ^ 2 = pythagoreanQuarticRhs m n ∧
        pythagoreanQuarticCenter m n - b = 2 * r ∧
        pythagoreanQuarticCenter m n + b = 2 * s ∧
        r * s = 3 * m ^ 2 * n ^ 2 ∧
        Int.gcd r s = 1 ∧
        (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
          (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
        (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
          (r = -(a ^ 2) ∧ s = -(3 * c ^ 2)))) := by
  obtain ⟨p, q, a, b, m, n, hT, hD, ha, hb, hpq, hpar,
    hparam, ha', hmn, hmnpar, hbquartic⟩ :=
    kubert_cover_pythagorean_params T D Y hDpos hcop h
  obtain ⟨r, s, hr, hs, hrs⟩ :=
    pythagorean_quartic_half_factorization_of_opposite_mod m n b hmnpar hbquartic
  by_cases hzero : m * n = 0
  · left
    have haxis := pythagorean_quartic_axis_of_zero_product m n hmn hzero
    have hpqzero := pythagorean_axis_param_p_or_q_zero p q m n hparam haxis
    exact pq_zero_forces_cover_degenerate T D p q hT hD hpqzero
  · right
    have hgcd_one := pythagorean_quartic_half_factor_gcd_eq_one m n b r s hmn hr hs hrs
    have hsigned :=
      pythagorean_quartic_half_factor_signed_split_of_nonzero m n b r s
        hmn hr hs hrs hzero
    exact ⟨m, n, b, r, s, hzero, hmn, hmnpar, hbquartic,
      hr, hs, hrs, hgcd_one, hsigned⟩

theorem rational_kubert_cover_pythagorean_half_factors (t q : ℚ)
    (h : q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1)) :
    ∃ T D Y m n b r s : ℤ,
      0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
      Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      b ^ 2 = pythagoreanQuarticRhs m n ∧
      pythagoreanQuarticCenter m n - b = 2 * r ∧
      pythagoreanQuarticCenter m n + b = 2 * s ∧
      r * s = 3 * m ^ 2 * n ^ 2 ∧
      ((Int.gcd r s : ℕ) : ℤ) ∣ (3 : ℤ) ∧
      (Int.gcd r s = 1 ∨ Int.gcd r s = 3) ∧
      Int.gcd r s = 1 ∧
      ((∃ a c : ℤ, (r = 3 * a ^ 2 ∨ r = -(3 * a ^ 2)) ∧
        (s = c ^ 2 ∨ s = -(c ^ 2))) ∨
      (∃ a c : ℤ, (r = a ^ 2 ∨ r = -(a ^ 2)) ∧
        (s = 3 * c ^ 2 ∨ s = -(3 * c ^ 2)))) ∧
      (m * n ≠ 0 →
        (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
          (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
        (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
          (r = -(a ^ 2) ∧ s = -(3 * c ^ 2))))) ∧
      (Int.gcd r s = 3 → ((3 : ℤ) ∣ m ∨ (3 : ℤ) ∣ n)) ∧
      (m * n = 0 → ((m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1))) := by
  obtain ⟨T, D, Y, hDpos, hcop, ht, hcover⟩ := kubert_cover_integral_model t q h
  obtain ⟨m, n, b, r, s, hmn, hmnpar, hbquartic, hr, hs, hrs,
      hgcd, hgcd_cases, hgcd_one, hsplit, hsigned_split, hthree_dvd_parameter, haxis⟩ :=
    kubert_cover_pythagorean_half_factors T D Y hDpos hcop hcover
  exact ⟨T, D, Y, m, n, b, r, s, hDpos, hcop, ht, hcover, hmn, hmnpar,
    hbquartic, hr, hs, hrs, hgcd, hgcd_cases, hgcd_one, hsplit, hsigned_split,
    hthree_dvd_parameter, haxis⟩

theorem rational_kubert_cover_residual_reduction (t q : ℚ)
    (h : q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1)) :
    ∃ T D Y m n b : ℤ,
      0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
      Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      b ^ 2 = pythagoreanQuarticRhs m n ∧
      (((m ^ 2 = 1 ∧ n = 0) ∨ (m = 0 ∧ n ^ 2 = 1)) ∨
        ∃ r s : ℤ,
          pythagoreanQuarticCenter m n - b = 2 * r ∧
          pythagoreanQuarticCenter m n + b = 2 * s ∧
          r * s = 3 * m ^ 2 * n ^ 2 ∧
          Int.gcd r s = 1 ∧
          (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
            (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
          (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
            (r = -(a ^ 2) ∧ s = -(3 * c ^ 2))))) := by
  obtain ⟨T, D, Y, hDpos, hcop, ht, hcover⟩ := kubert_cover_integral_model t q h
  obtain ⟨m, n, b, hmn, hmnpar, hbquartic, hred⟩ :=
    kubert_cover_residual_reduction T D Y hDpos hcop hcover
  exact ⟨T, D, Y, m, n, b, hDpos, hcop, ht, hcover, hmn, hmnpar, hbquartic, hred⟩

theorem rational_kubert_cover_degenerate_or_signed_residual (t q : ℚ)
    (h : q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1)) :
    (t = 1 ∨ t = -1) ∨
      ∃ T D Y m n b r s : ℤ,
        0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
        Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) ∧
        m * n ≠ 0 ∧
        Int.gcd m n = 1 ∧
        (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
        b ^ 2 = pythagoreanQuarticRhs m n ∧
        pythagoreanQuarticCenter m n - b = 2 * r ∧
        pythagoreanQuarticCenter m n + b = 2 * s ∧
        r * s = 3 * m ^ 2 * n ^ 2 ∧
        Int.gcd r s = 1 ∧
        (((∃ a c : ℤ, (r = 3 * a ^ 2 ∧ s = c ^ 2) ∨
          (r = -(3 * a ^ 2) ∧ s = -(c ^ 2)))) ∨
        (∃ a c : ℤ, (r = a ^ 2 ∧ s = 3 * c ^ 2) ∨
          (r = -(a ^ 2) ∧ s = -(3 * c ^ 2)))) := by
  obtain ⟨T, D, Y, hDpos, hcop, ht, hcover⟩ := kubert_cover_integral_model t q h
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  rcases kubert_cover_degenerate_or_signed_residual T D Y hDpos hcop hcover with hdeg | hres
  · left
    rcases hdeg with hTD | hTD
    · left
      rw [ht, hTD]
      field_simp [hDne]
    · right
      rw [ht, hTD]
      push_cast
      field_simp [hDne]
  · right
    obtain ⟨m, n, b, r, s, hmn_nonzero, hmn, hmnpar, hbquartic,
      hr, hs, hrs, hgcd_one, hsigned⟩ := hres
    exact ⟨T, D, Y, m, n, b, r, s, hDpos, hcop, ht, hcover,
      hmn_nonzero, hmn, hmnpar, hbquartic, hr, hs, hrs, hgcd_one, hsigned⟩

theorem rational_kubert_cover_degenerate_or_signedResidual (t q : ℚ)
    (h : q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1)) :
    (t = 1 ∨ t = -1) ∨ RationalCoverSignedResidual t := by
  rcases rational_kubert_cover_degenerate_or_signed_residual t q h with hdeg | hres
  · exact Or.inl hdeg
  · right
    obtain ⟨T, D, Y, m, n, b, r, s, hDpos, hcop, ht, hcover,
      hmn_nonzero, hmn, hmnpar, hbquartic, hr, hs, hrs, hgcd_one, hsigned⟩ := hres
    exact ⟨T, D, Y, m, n, b, r, s, hDpos, hcop, ht, hcover,
      hmn_nonzero, hmn, hmnpar, hbquartic, hr, hs, hrs, hgcd_one, hsigned⟩

/-! ## Large positive integral branch -/

theorem N12_factor_int (u : ℤ) :
    u ^ 3 - u ^ 2 - 4 * u + 4 = (u - 1) * (u - 2) * (u + 2) := by
  ring

theorem N12_factor₂_int (u : ℤ) :
    u ^ 3 - u ^ 2 - 4 * u + 4 = (u - 1) * (u ^ 2 - 4) := by
  ring

theorem N12_coprime_of_not_three_dvd (u : ℤ)
    (h3 : ¬ (3 : ℤ) ∣ u - 1) : IsCoprime (u - 1) (u ^ 2 - 4) := by
  have hmod : (u - 1) % 3 = 0 ∨ (u - 1) % 3 = 1 ∨ (u - 1) % 3 = 2 := by
    omega
  rcases hmod with h0 | h1 | h2
  · exact False.elim (h3 (Int.dvd_of_emod_eq_zero h0))
  · let q : ℤ := (u - 1) / 3
    have hq : u - 1 = 3 * q + 1 := by
      dsimp [q]
      omega
    refine ⟨1 - q * (u + 1), q, ?_⟩
    ring_nf
    omega
  · let q : ℤ := (u + 1) / 3
    have hq : u - 1 = 3 * q - 1 := by
      dsimp [q]
      omega
    refine ⟨-1 + q * (u + 1), -q, ?_⟩
    ring_nf
    omega

theorem N12_large_integer_descent_of_quartic
    (hquartic : ∀ a b : ℤ,
      b ^ 2 = 3 * a ^ 4 + 2 * a ^ 2 - 1 → a ^ 2 = 1)
    (u w : ℤ)
    (hu : 5 ≤ u)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) : False := by
  have hfact : (u - 1) * (u ^ 2 - 4) = w ^ 2 := by
    rw [N12_factor₂_int] at h
    exact h.symm
  have hu1_pos : 0 < u - 1 := by omega
  have hu2_pos : 0 < u ^ 2 - 4 := by nlinarith
  by_cases h3 : (3 : ℤ) ∣ u - 1
  · rcases h3 with ⟨s, hs⟩
    have hs_def : u - 1 = 3 * s := hs
    have hs_ge : 2 ≤ s := by omega
    have hu_eq : u = 3 * s + 1 := by omega
    have hquad : u ^ 2 - 4 = 3 * (3 * s ^ 2 + 2 * s - 1) := by
      rw [hu_eq]
      ring
    have h9 : w ^ 2 = 9 * (s * (3 * s ^ 2 + 2 * s - 1)) := by
      calc
        w ^ 2 = (u - 1) * (u ^ 2 - 4) := hfact.symm
        _ = (3 * s) * (3 * (3 * s ^ 2 + 2 * s - 1)) := by rw [hs_def, hquad]
        _ = 9 * (s * (3 * s ^ 2 + 2 * s - 1)) := by ring
    have h3sq : (3 : ℤ) ∣ w ^ 2 := by
      rw [h9]
      exact dvd_mul_of_dvd_left (show (3 : ℤ) ∣ 9 by norm_num) _
    have h3w : (3 : ℤ) ∣ w := by
      have hp : Prime (3 : ℤ) := by norm_num
      have hmul : (3 : ℤ) ∣ w * w := by
        simpa [pow_two] using h3sq
      rcases hp.dvd_or_dvd hmul with hw | hw
      · exact hw
      · exact hw
    rcases h3w with ⟨k, hk⟩
    have hk_sq : k ^ 2 = s * (3 * s ^ 2 + 2 * s - 1) := by
      subst w
      ring_nf at h9
      nlinarith
    have hk_prod_sq : s * (3 * s ^ 2 + 2 * s - 1) = k ^ 2 := by
      nlinarith
    have hcop : IsCoprime s (3 * s ^ 2 + 2 * s - 1) := ⟨3 * s + 2, -1, by ring⟩
    obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hk_prod_sq
    · have hcop' : IsCoprime (3 * s ^ 2 + 2 * s - 1) s := hcop.symm
      have hk_sq' : (3 * s ^ 2 + 2 * s - 1) * s = k ^ 2 := by
        nlinarith
      obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hk_sq'
      · have hquartic_eq : b ^ 2 = 3 * a ^ 4 + 2 * a ^ 2 - 1 := by
          calc
            b ^ 2 = 3 * s ^ 2 + 2 * s - 1 := hb.symm
            _ = 3 * a ^ 4 + 2 * a ^ 2 - 1 := by
              rw [ha]
              ring
        have ha1 : a ^ 2 = 1 := hquartic a b hquartic_eq
        nlinarith
      · have hpos : 0 < 3 * s ^ 2 + 2 * s - 1 := by nlinarith
        nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg a]
  · have hcop : IsCoprime (u - 1) (u ^ 2 - 4) :=
      N12_coprime_of_not_three_dvd u h3
    obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hfact
    · have ha_ge4 : 4 ≤ a ^ 2 := by nlinarith
      have hcop' : IsCoprime (u ^ 2 - 4) (u - 1) := hcop.symm
      have hfact' : (u ^ 2 - 4) * (u - 1) = w ^ 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hfact
      obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hfact'
      · have hu_eq : u = a ^ 2 + 1 := by nlinarith
        have hkey : b ^ 2 = (a ^ 2 + 1) ^ 2 - 4 := by
          calc
            b ^ 2 = u ^ 2 - 4 := hb.symm
            _ = (a ^ 2 + 1) ^ 2 - 4 := by
              rw [hu_eq]
        have hlow : a ^ 4 < b ^ 2 := by nlinarith
        have hhigh : b ^ 2 < (a ^ 2 + 1) ^ 2 := by nlinarith
        have hb_pos : 0 < b ^ 2 := by nlinarith
        have hb_ne : b ≠ 0 := by
          intro h0
          simp [h0] at hb_pos
        rcases lt_or_gt_of_ne hb_ne with hbneg | hbpos
        · have hlt : a ^ 2 < -b := by
            nlinarith [sq_nonneg (b + a ^ 2)]
          have hgt : -b < a ^ 2 + 1 := by
            nlinarith [sq_nonneg (b + a ^ 2 + 1)]
          omega
        · have hlt : a ^ 2 < b := by
            nlinarith [sq_nonneg (b - a ^ 2 - 1)]
          have hgt : b < a ^ 2 + 1 := by
            nlinarith [sq_nonneg (b - a ^ 2)]
          omega
      · nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg a]

theorem N12_large_integer_descent_of_pell
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (u w : ℤ)
    (hu : 5 ≤ u)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) : False :=
  N12_large_integer_descent_of_quartic
    (quartic_square_only_pm_one_of_pell hpell) u w hu h

/-- Integer squares are never congruent to `2` modulo `4`. -/
private theorem sq_mod_four_ne_two (z : ℤ) : z ^ 2 % 4 ≠ 2 := by
  rcases Int.emod_two_eq_zero_or_one z with hz | hz
  · obtain ⟨k, hk⟩ : (2 : ℤ) ∣ z := ⟨z / 2, by omega⟩
    rw [hk]
    ring_nf
    omega
  · obtain ⟨k, hk⟩ : ∃ k, z = 2 * k + 1 := ⟨z / 2, by omega⟩
    rw [hk]
    ring_nf
    omega

/--
Conditional integer-point classification for the N=12 obstruction curve.
The only remaining input is the same Pell residual used by the quartic branch.
-/
theorem N12_integral_points_degenerate_of_pell
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (u w : ℤ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4 := by
  by_cases hu_ge : 5 ≤ u
  · exact False.elim (N12_large_integer_descent_of_pell hpell u w hu_ge h)
  have hu_le : u ≤ 4 := by omega
  by_cases hu_low : u ≤ -3
  · have hfact : w ^ 2 = (u - 1) * (u - 2) * (u + 2) := by
      rw [h, N12_factor_int]
    have hneg : (u - 1) * (u - 2) * (u + 2) < 0 := by
      nlinarith [sq_nonneg (u + 3), sq_nonneg (u + 2)]
    exact False.elim (by nlinarith [sq_nonneg w])
  have hu_min : -2 ≤ u := by omega
  interval_cases u
  · left
    rfl
  · exfalso
    have hmod : w ^ 2 % 4 = 2 := by
      rw [h]
      norm_num
    exact sq_mod_four_ne_two w hmod
  · right; left
    rfl
  · right; right; left
    rfl
  · right; right; right; left
    rfl
  · exfalso
    have hmod : w ^ 2 % 4 = 2 := by
      rw [h]
      norm_num
    exact sq_mod_four_ne_two w hmod
  · right; right; right; right
    rfl

/-- Integer-point classification stated with the shared rational obstruction predicate. -/
theorem N12_integral_curve_point_degenerate_of_pell
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (u w : ℤ)
    (h : MazurProof.E_N12_AffineEquation (u : ℚ) (w : ℚ)) :
    MazurProof.E_N12_DegenerateParameter (u : ℚ) := by
  have hint : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 := by
    unfold MazurProof.E_N12_AffineEquation at h
    exact_mod_cast h
  rcases N12_integral_points_degenerate_of_pell hpell u w hint with hu | hu | hu | hu | hu
  all_goals
    unfold MazurProof.E_N12_DegenerateParameter
    rw [hu]
    norm_num

/--
Conditional classification when the `u`-coordinate is integral but the
`w`-coordinate is still rational.  A rational square equal to an integer is an
integer square, so this reduces to `N12_integral_points_degenerate_of_pell`.
-/
theorem N12_integer_x_rational_point_degenerate_of_pell
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (u : ℤ) (w : ℚ)
    (h : MazurProof.E_N12_AffineEquation (u : ℚ) w) :
    MazurProof.E_N12_DegenerateParameter (u : ℚ) := by
  set N : ℤ := u ^ 3 - u ^ 2 - 4 * u + 4
  have hsq : IsSquare (N : ℚ) := by
    refine ⟨w, ?_⟩
    unfold MazurProof.E_N12_AffineEquation at h
    rw [sq] at h
    rw [h]
    push_cast [N]
    ring
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨W, hW⟩ := hsq
  have hWint : W ^ 2 = N := by
    rw [sq]
    linarith
  rcases N12_integral_points_degenerate_of_pell hpell u W (by simpa [N] using hWint)
      with hu | hu | hu | hu | hu
  all_goals
    unfold MazurProof.E_N12_DegenerateParameter
    rw [hu]
    norm_num

/--
Conditional classification for rational points whose normalized rational
`u`-coordinate has denominator `1`.
-/
theorem N12_rational_point_degenerate_of_den_eq_one_of_pell
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w)
    (hden : u.den = 1) :
    MazurProof.E_N12_DegenerateParameter u := by
  have hu : u = (u.num : ℚ) := by
    calc
      u = (u.num : ℚ) / (u.den : ℚ) := (Rat.num_div_den u).symm
      _ = (u.num : ℚ) := by rw [hden]; norm_num
  rw [hu] at h ⊢
  exact N12_integer_x_rational_point_degenerate_of_pell hpell u.num w h

/--
Conditional classification when a rational point is expressed in the
normalized square-denominator form with denominator `B = 1`.
-/
theorem N12_rational_point_degenerate_of_square_den_eq_one_of_pell
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w)
    (A B : ℤ)
    (hu : u = (A : ℚ) / (B : ℚ) ^ 2)
    (hB : B = 1) :
    MazurProof.E_N12_DegenerateParameter u := by
  have huA : u = (A : ℚ) := by
    rw [hu, hB]
    norm_num
  rw [huA] at h ⊢
  exact N12_integer_x_rational_point_degenerate_of_pell hpell A w h

/--
The remaining denominator residual for the full rational N=12 obstruction
curve: every primitive square-denominator integral model has denominator `1`.
-/
def N12SquareDenominatorOneResidual : Prop :=
  ∀ A B C : ℤ,
    0 < B →
    Int.gcd A B = 1 →
    C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) →
    B = 1

/--
Equivalent attack form for the square-denominator residual: there is no
primitive normalized integral model with denominator `B > 1`.
-/
def N12NoNontrivialSquareDenominatorResidual : Prop :=
  ∀ A B C : ℤ,
    1 < B →
    Int.gcd A B = 1 →
    C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) →
    False

private theorem square_denominator_int_dvd_of_rat_eq_int
    (A B m : ℤ) (hBne : B ≠ 0)
    (h : (A : ℚ) / (B : ℚ) ^ 2 = (m : ℚ)) :
    B ∣ A := by
  have hBq : (B : ℚ) ≠ 0 := by
    exact_mod_cast hBne
  have hBsq : (B : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hBq
  have hAq : (A : ℚ) = (m : ℚ) * (B : ℚ) ^ 2 := by
    calc
      (A : ℚ) = ((A : ℚ) / (B : ℚ) ^ 2) * (B : ℚ) ^ 2 := by
        exact (div_mul_cancel₀ (A : ℚ) hBsq).symm
      _ = (m : ℚ) * (B : ℚ) ^ 2 := by rw [h]
  have hAq' : (A : ℚ) = ((m * B ^ 2 : ℤ) : ℚ) := by
    rw [hAq]
    push_cast
    ring
  have hAint : A = m * B ^ 2 := by
    exact_mod_cast hAq'
  rw [hAint]
  exact dvd_mul_of_dvd_right
    (dvd_pow_self B (by norm_num : (2 : ℕ) ≠ 0)) m

theorem primitive_square_denominator_ne_int
    (A B m : ℤ)
    (hBgt : 1 < B)
    (hcop : Int.gcd A B = 1) :
    (A : ℚ) / (B : ℚ) ^ 2 ≠ (m : ℚ) := by
  intro h
  have hBne : B ≠ 0 := by omega
  have hBdvdA : B ∣ A :=
    square_denominator_int_dvd_of_rat_eq_int A B m hBne h
  have hBdvdgcd : B ∣ ((Int.gcd A B : ℕ) : ℤ) :=
    Int.dvd_coe_gcd hBdvdA (dvd_refl B)
  have hBdvd1 : B ∣ (1 : ℤ) := by
    simpa [hcop] using hBdvdgcd
  have hunit : IsUnit B := isUnit_of_dvd_one hBdvd1
  have hBnatAbs : B.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hunit
  have hBnonneg : 0 ≤ B := by omega
  have hB1 : B = 1 := by
    have hcast : ((B.natAbs : ℕ) : ℤ) = (1 : ℤ) := by
      exact_mod_cast hBnatAbs
    rwa [Int.natAbs_of_nonneg hBnonneg] at hcast
  omega

theorem primitive_square_denominator_not_E_N12_DegenerateParameter
    (A B : ℤ)
    (hBgt : 1 < B)
    (hcop : Int.gcd A B = 1) :
    ¬ MazurProof.E_N12_DegenerateParameter ((A : ℚ) / (B : ℚ) ^ 2) := by
  intro hdeg
  unfold MazurProof.E_N12_DegenerateParameter at hdeg
  rcases hdeg with hneg2 | hzero | hone | htwo | hfour
  · exact (primitive_square_denominator_ne_int A B (-2) hBgt hcop) (by simpa using hneg2)
  · exact (primitive_square_denominator_ne_int A B 0 hBgt hcop) (by simpa using hzero)
  · exact (primitive_square_denominator_ne_int A B 1 hBgt hcop) (by simpa using hone)
  · exact (primitive_square_denominator_ne_int A B 2 hBgt hcop) (by simpa using htwo)
  · exact (primitive_square_denominator_ne_int A B 4 hBgt hcop) (by simpa using hfour)

theorem square_denominator_rational_curve_equation
    (A B C : ℤ)
    (hBne : B ≠ 0)
    (hC : C ^ 2 =
      (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    MazurProof.E_N12_AffineEquation
      ((A : ℚ) / (B : ℚ) ^ 2)
      ((C : ℚ) / (B : ℚ) ^ 3) := by
  unfold MazurProof.E_N12_AffineEquation
  have hBq : (B : ℚ) ≠ 0 := by
    exact_mod_cast hBne
  have hB2 : (B : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hBq
  have hB3 : (B : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hBq
  have hB4 : (B : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 hBq
  have hB5 : (B : ℚ) ^ 5 ≠ 0 := pow_ne_zero 5 hBq
  have hB6 : (B : ℚ) ^ 6 ≠ 0 := pow_ne_zero 6 hBq
  have hCq :
      (C : ℚ) ^ 2 =
        ((A : ℚ) - (B : ℚ) ^ 2) *
          ((A : ℚ) - 2 * (B : ℚ) ^ 2) *
            ((A : ℚ) + 2 * (B : ℚ) ^ 2) := by
    exact_mod_cast hC
  field_simp [hBq, hB2, hB3, hB4, hB5, hB6]
  ring_nf at hCq ⊢
  exact hCq

theorem N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    (hboundary : ∀ u w : ℚ,
      MazurProof.E_N12_AffineEquation u w →
      MazurProof.E_N12_DegenerateParameter u) :
    N12NoNontrivialSquareDenominatorResidual := by
  intro A B C hBgt hcop hC
  let u : ℚ := (A : ℚ) / (B : ℚ) ^ 2
  let w : ℚ := (C : ℚ) / (B : ℚ) ^ 3
  have hBne : B ≠ 0 := by omega
  have hcurve : MazurProof.E_N12_AffineEquation u w := by
    dsimp [u, w]
    exact square_denominator_rational_curve_equation A B C hBne hC
  have hdeg : MazurProof.E_N12_DegenerateParameter u := hboundary u w hcurve
  exact primitive_square_denominator_not_E_N12_DegenerateParameter A B hBgt hcop hdeg

theorem square_denominator_one_residual_of_no_nontrivial
    (hno : N12NoNontrivialSquareDenominatorResidual) :
    N12SquareDenominatorOneResidual := by
  intro A B C hBpos hcop hC
  by_cases hB : B = 1
  · exact hB
  · exfalso
    have hBgt : 1 < B := by omega
    exact hno A B C hBgt hcop hC

/--
Full rational N=12 obstruction curve classification reduced to the two
remaining elementary number-theory residuals:
* the Pell residual already used by the integral branch;
* the square-denominator residual `B = 1`.
-/
theorem N12_rational_points_degenerate_of_pell_and_denominator
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (hden : N12SquareDenominatorOneResidual)
    (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w) :
    MazurProof.E_N12_DegenerateParameter u := by
  obtain ⟨A, B, C, hBpos, hcop, hu, hC⟩ := integral_model_of_curve_point u w h
  exact N12_rational_point_degenerate_of_square_den_eq_one_of_pell
    hpell u w h A B hu (hden A B C hBpos hcop hC)

/--
Full rational N=12 obstruction curve classification using the nontrivial-
denominator exclusion form of the denominator residual.
-/
theorem N12_rational_points_degenerate_of_pell_and_no_nontrivial_denominator
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (hno : N12NoNontrivialSquareDenominatorResidual)
    (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w) :
    MazurProof.E_N12_DegenerateParameter u :=
  N12_rational_points_degenerate_of_pell_and_denominator hpell
    (square_denominator_one_residual_of_no_nontrivial hno) u w h

end MazurProof.RationalPointsN12
