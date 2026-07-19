import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsN18

/-!
# Arithmetic reduction for the rational points on `X₁(18)`

This file isolates the arithmetic part of the order-18 obstruction.  It first
uses the order-three Mobius symmetry of the standard genus-two model to move
every noncuspidal rational point into the interval `0 < U < 1`.  It then clears
denominators in lowest terms and obtains a positive primitive integral sextic.

The final norm identity is the starting point for an arithmetic descent:

`C² = P² + 2 Q²`,

where `Q = 2 A D (A + D)` and `A`, `D`, and `A + D` are pairwise coprime.
-/

namespace MazurProof.RationalPointsN18Descent

open RationalPointsN18

noncomputable section

/-! ## The order-three symmetry -/

/-- The first nontrivial element of the order-three Mobius action. -/
def mobius₁ (U : ℚ) : ℚ := 1 / (1 - U)

/-- The second nontrivial element of the order-three Mobius action. -/
def mobius₂ (U : ℚ) : ℚ := (U - 1) / U

theorem mobius₁_f18 (U : ℚ) (hU : U ≠ 1) :
    (1 - U) ^ 6 * hyperellipticF18 (mobius₁ U) = hyperellipticF18 U := by
  simp only [mobius₁, hyperellipticF18]
  field_simp [sub_ne_zero.mpr hU]
  ring

theorem mobius₂_f18 (U : ℚ) (hU : U ≠ 0) :
    U ^ 6 * hyperellipticF18 (mobius₂ U) = hyperellipticF18 U := by
  simp only [mobius₂, hyperellipticF18]
  field_simp [hU]
  ring

theorem mobius₁_curve_point {U Y : ℚ} (hU : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    (Y / (1 - U) ^ 3) ^ 2 = hyperellipticF18 (mobius₁ U) := by
  have hden : 1 - U ≠ 0 := sub_ne_zero.mpr hU.symm
  apply (mul_left_cancel₀ (pow_ne_zero 6 hden) : _)
  calc
    (1 - U) ^ 6 * (Y / (1 - U) ^ 3) ^ 2 = Y ^ 2 := by
      field_simp [hden]
    _ = hyperellipticF18 U := hY
    _ = (1 - U) ^ 6 * hyperellipticF18 (mobius₁ U) :=
      (mobius₁_f18 U hU).symm

theorem mobius₂_curve_point {U Y : ℚ} (hU : U ≠ 0)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    (Y / U ^ 3) ^ 2 = hyperellipticF18 (mobius₂ U) := by
  apply (mul_left_cancel₀ (pow_ne_zero 6 hU) : _)
  calc
    U ^ 6 * (Y / U ^ 3) ^ 2 = Y ^ 2 := by
      field_simp [hU]
    _ = hyperellipticF18 U := hY
    _ = U ^ 6 * hyperellipticF18 (mobius₂ U) :=
      (mobius₂_f18 U hU).symm

/-- Every noncuspidal rational point has an order-three translate whose first
coordinate lies strictly between zero and one. -/
theorem normalize_curve_point {U Y : ℚ} (hU0 : U ≠ 0) (hU1 : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    ∃ u y : ℚ, 0 < u ∧ u < 1 ∧ y ^ 2 = hyperellipticF18 u := by
  rcases lt_trichotomy U 0 with hneg | hzero | hpos
  · have hden : 0 < 1 - U := by linarith
    refine ⟨mobius₁ U, Y / (1 - U) ^ 3, ?_, ?_, mobius₁_curve_point hU1 hY⟩
    · simp only [mobius₁]
      positivity
    · simp only [mobius₁]
      exact (div_lt_one hden).mpr (by linarith)
  · exact (hU0 hzero).elim
  · rcases lt_trichotomy U 1 with hlt | hone | hgt
    · exact ⟨U, Y, hpos, hlt, hY⟩
    · exact (hU1 hone).elim
    · refine ⟨mobius₂ U, Y / U ^ 3, ?_, ?_, mobius₂_curve_point hU0 hY⟩
      · simp only [mobius₂]
        exact div_pos (sub_pos.mpr hgt) hpos
      · simp only [mobius₂]
        exact (div_lt_one hpos).mpr (by linarith)

/-! ## Clearing denominators -/

/-- The homogeneous integral sextic associated to `hyperellipticF18`. -/
def F18Hom (A B : ℤ) : ℤ :=
  A ^ 6 - 4 * A ^ 5 * B + 10 * A ^ 4 * B ^ 2 - 10 * A ^ 3 * B ^ 3
    + 5 * A ^ 2 * B ^ 4 - 2 * A * B ^ 5 + B ^ 6

theorem F18Hom_clear_denominators (A B : ℤ) (hB : B ≠ 0) :
    (B : ℚ) ^ 6 * hyperellipticF18 ((A : ℚ) / (B : ℚ)) = (F18Hom A B : ℚ) := by
  simp only [hyperellipticF18, F18Hom]
  push_cast
  field_simp [hB]

/-- A normalized rational point produces a square value of the primitive
homogeneous sextic. -/
theorem normalized_integral_model {u y : ℚ} (hu0 : 0 < u) (hu1 : u < 1)
    (hy : y ^ 2 = hyperellipticF18 u) :
    ∃ A B C : ℤ,
      0 < A ∧ A < B ∧ Int.gcd A B = 1 ∧
      u = (A : ℚ) / (B : ℚ) ∧ C ^ 2 = F18Hom A B := by
  let A : ℤ := u.num
  let B : ℤ := (u.den : ℤ)
  have hApos : 0 < A := by
    dsimp [A]
    exact Rat.num_pos.mpr hu0
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hAB : A < B := by
    dsimp [A, B]
    exact Rat.num_lt_denom_iff.mpr hu1
  have hcop : Int.gcd A B = 1 := by
    dsimp [A, B]
    simpa [Int.gcd, Int.natAbs_natCast] using u.reduced
  have hu : u = (A : ℚ) / (B : ℚ) := by
    dsimp [A, B]
    push_cast
    exact (Rat.num_div_den u).symm
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (F18Hom A B : ℚ) := by
    calc
      (y * (B : ℚ) ^ 3) ^ 2 = y ^ 2 * (B : ℚ) ^ 6 := by ring
      _ = hyperellipticF18 u * (B : ℚ) ^ 6 := by rw [hy]
      _ = (B : ℚ) ^ 6 * hyperellipticF18 ((A : ℚ) / (B : ℚ)) := by
        rw [hu]
        ring
      _ = (F18Hom A B : ℚ) := F18Hom_clear_denominators A B hBne
  have hsquare : IsSquare (F18Hom A B : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsquare
  obtain ⟨C, hC⟩ := hsquare
  refine ⟨A, B, C, hApos, hAB, hcop, hu, ?_⟩
  rw [sq]
  exact hC.symm

/-! ## The positive primitive descent equation -/

/-- Substitute `B = A + D`, where normalization gives `A,D > 0`. -/
def F18Positive (A D : ℤ) : ℤ :=
  A ^ 6 + 2 * A ^ 5 * D + 5 * A ^ 4 * D ^ 2 + 10 * A ^ 3 * D ^ 3
    + 10 * A ^ 2 * D ^ 4 + 4 * A * D ^ 5 + D ^ 6

/-- The real component in the norm-form presentation of `F18Positive`. -/
def normReal (A D : ℤ) : ℤ :=
  -A ^ 3 - A ^ 2 * D + 2 * A * D ^ 2 + D ^ 3

/-- The imaginary component in the norm-form presentation of `F18Positive`. -/
def normImag (A D : ℤ) : ℤ := 2 * A * D * (A + D)

theorem F18Hom_substitution (A D : ℤ) :
    F18Hom A (A + D) = F18Positive A D := by
  simp only [F18Hom, F18Positive]
  ring

theorem F18Positive_square_completion (A D : ℤ) :
    F18Positive A D =
      (A ^ 3 + A ^ 2 * D - D ^ 3) ^ 2 + 4 * A * D ^ 2 * (A + D) ^ 3 := by
  simp only [F18Positive]
  ring

theorem F18Positive_norm (A D : ℤ) :
    F18Positive A D = normReal A D ^ 2 + 2 * normImag A D ^ 2 := by
  simp only [F18Positive, normReal, normImag]
  ring

theorem gcd_sub_right (A B : ℤ) (hcop : Int.gcd A B = 1) :
    Int.gcd A (B - A) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
  simpa [sub_eq_add_neg] using hcop.add_mul_right_right (-1)

theorem gcd_sum_right (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Int.gcd A (A + D) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
  simpa [add_comm] using hcop.add_mul_right_right 1

theorem gcd_sum_left (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Int.gcd D (A + D) = 1 := by
  rw [Int.gcd_comm A D] at hcop
  simpa [add_comm] using gcd_sum_right D A hcop

theorem normReal_coprime_A (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Int.gcd (normReal A D) A = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
  have hbase : IsCoprime (D ^ 3) A := hcop.symm.pow_left
  rw [show normReal A D =
      D ^ 3 + A * (-A ^ 2 - A * D + 2 * D ^ 2) by
    unfold normReal
    ring]
  exact hbase.add_mul_left_left (-A ^ 2 - A * D + 2 * D ^ 2)

theorem normReal_coprime_D (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Int.gcd (normReal A D) D = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
  have hbase : IsCoprime (-A ^ 3) D := hcop.pow_left.neg_left
  rw [show normReal A D =
      -A ^ 3 + D * (-A ^ 2 + 2 * A * D + D ^ 2) by
    unfold normReal
    ring]
  exact hbase.add_mul_left_left (-A ^ 2 + 2 * A * D + D ^ 2)

theorem normReal_coprime_sum (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Int.gcd (normReal A D) (A + D) = 1 := by
  have hcopAS : Int.gcd A (A + D) = 1 := gcd_sum_right A D hcop
  rw [← Int.isCoprime_iff_gcd_eq_one] at hcopAS ⊢
  have hbase : IsCoprime (A ^ 3) (A + D) := hcopAS.pow_left
  rw [show normReal A D =
      A ^ 3 + (A + D) * (-2 * A ^ 2 + A * D + D ^ 2) by
    unfold normReal
    ring]
  exact hbase.add_mul_left_left (-2 * A ^ 2 + A * D + D ^ 2)

theorem normReal_coprime_product (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Int.gcd (normReal A D) (A * D * (A + D)) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hA : IsCoprime (normReal A D) A :=
    Int.isCoprime_iff_gcd_eq_one.mpr (normReal_coprime_A A D hcop)
  have hD : IsCoprime (normReal A D) D :=
    Int.isCoprime_iff_gcd_eq_one.mpr (normReal_coprime_D A D hcop)
  have hS : IsCoprime (normReal A D) (A + D) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (normReal_coprime_sum A D hcop)
  exact (hA.mul_right hD).mul_right hS

theorem two_dvd_triple_product (A D : ℤ) :
    (2 : ℤ) ∣ A * D * (A + D) := by
  rcases Int.even_or_odd A with hA | hA
  · exact ((hA.mul_right D).mul_right (A + D)).two_dvd
  · rcases Int.even_or_odd D with hD | hD
    · exact ((hD.mul_left A).mul_right (A + D)).two_dvd
    · exact ((hA.add_odd hD).mul_left (A * D)).two_dvd

theorem normReal_odd (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Odd (normReal A D) := by
  have hprod : IsCoprime (normReal A D) (A * D * (A + D)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (normReal_coprime_product A D hcop)
  have htwo : IsCoprime (normReal A D) 2 :=
    hprod.of_isCoprime_of_dvd_right (two_dvd_triple_product A D)
  exact Int.isCoprime_two_right.mp htwo

theorem norm_components_coprime (A D : ℤ) (hcop : Int.gcd A D = 1) :
    Int.gcd (normReal A D) (normImag A D) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hprod : IsCoprime (normReal A D) (A * D * (A + D)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (normReal_coprime_product A D hcop)
  have htwo : IsCoprime (normReal A D) 2 :=
    hprod.of_isCoprime_of_dvd_right (two_dvd_triple_product A D)
  have h := htwo.mul_right hprod
  convert h using 1
  simp only [normImag]
  ring

/-! ## Primitive norm factorization -/

/-- Elementary factorization of a primitive solution of
`C² = P² + 2 Q²` when `P` is odd and `Q` is even.  The two factors
`(C-P)/2` and `(C+P)/2` are themselves coprime, and their product is twice a
square.  This is the integral front end of the `ℤ[√-2]` parametrization. -/
theorem primitive_norm_split {C P Q : ℤ}
    (hPQ : Int.gcd P Q = 1) (hPodd : Odd P) (hQeven : Even Q)
    (hcurve : C ^ 2 = P ^ 2 + 2 * Q ^ 2) :
    ∃ R S M : ℤ,
      Q = 2 * M ∧ C = R + S ∧ P = S - R ∧
      Int.gcd R S = 1 ∧ R * S = 2 * M ^ 2 := by
  have hPQ' : IsCoprime P Q := Int.isCoprime_iff_gcd_eq_one.mpr hPQ
  have hPtwo : IsCoprime P 2 := Int.isCoprime_two_right.mpr hPodd
  have hPterm : IsCoprime P (2 * Q ^ 2) := hPtwo.mul_right hPQ'.pow_right
  have hPCsq : IsCoprime P (C ^ 2) := by
    rw [hcurve]
    simpa [pow_two, add_comm] using hPterm.add_mul_left_right P
  have hPC : IsCoprime P C :=
    (IsCoprime.pow_right_iff (by norm_num : 0 < 2)).mp hPCsq
  have hCsqOdd : Odd (C ^ 2) := by
    rw [hcurve]
    exact hPodd.pow.add_even (even_two_mul (Q ^ 2))
  have hCodd : Odd C := (Int.odd_pow' (by norm_num : 2 ≠ 0)).mp hCsqOdd
  obtain ⟨R, hR⟩ := even_iff_exists_two_mul.mp (hCodd.sub_odd hPodd)
  obtain ⟨S, hS⟩ := even_iff_exists_two_mul.mp (hCodd.add_odd hPodd)
  obtain ⟨M, hM⟩ := even_iff_exists_two_mul.mp hQeven
  have hC : C = R + S := by linarith
  have hP : P = S - R := by linarith
  have hRS : R * S = 2 * M ^ 2 := by
    rw [hC, hP, hM] at hcurve
    nlinarith [hcurve]
  have hcopRS : Int.gcd R S = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    rcases hPC.symm with ⟨a, b, hab⟩
    refine ⟨a - b, a + b, ?_⟩
    rw [hC, hP] at hab
    linear_combination hab
  exact ⟨R, S, M, hM, hC, hP, hcopRS, hRS⟩

theorem positive_factor_square_of_coprime {a b c : ℤ}
    (ha : 0 < a) (hcop : IsCoprime a b) (hprod : a * b = c ^ 2) :
    ∃ x : ℤ, a = x ^ 2 := by
  obtain ⟨x, hx | hx⟩ := Int.sq_of_isCoprime hcop hprod
  · exact ⟨x, hx⟩
  · exfalso
    nlinarith [sq_nonneg x]

/-- Coprime positive factors whose product is twice a square split into a
square and twice a square.  The signs of the square roots are chosen so that
their product is exactly `M`. -/
theorem positive_coprime_twice_square_split {R S M : ℤ}
    (hRpos : 0 < R) (hSpos : 0 < S) (hcop : Int.gcd R S = 1)
    (hprod : R * S = 2 * M ^ 2) :
    (∃ e f : ℤ, R = 2 * f ^ 2 ∧ S = e ^ 2 ∧ M = e * f) ∨
    (∃ e f : ℤ, R = f ^ 2 ∧ S = 2 * e ^ 2 ∧ M = e * f) := by
  have htwo : (2 : ℤ) ∣ R * S := by
    rw [hprod]
    exact dvd_mul_right 2 (M ^ 2)
  rcases Int.Prime.dvd_mul' Nat.prime_two htwo with htwoR | htwoS
  · obtain ⟨R₀, hR₀⟩ := htwoR
    have hR₀pos : 0 < R₀ := by
      rw [hR₀] at hRpos
      nlinarith
    have hcop' : IsCoprime R S := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    rw [hR₀] at hcop'
    have hcop₀ : IsCoprime R₀ S := hcop'.of_mul_left_right
    have hprod₀ : R₀ * S = M ^ 2 := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      calc
        (2 : ℤ) * (R₀ * S) = R * S := by rw [hR₀]; ring
        _ = 2 * M ^ 2 := hprod
    obtain ⟨f, hf⟩ := positive_factor_square_of_coprime hR₀pos hcop₀ hprod₀
    obtain ⟨e, he⟩ := positive_factor_square_of_coprime hSpos hcop₀.symm (by
      rw [mul_comm]
      exact hprod₀)
    have hMsq : M ^ 2 = (e * f) ^ 2 := by
      calc
        M ^ 2 = R₀ * S := hprod₀.symm
        _ = (e * f) ^ 2 := by rw [hf, he]; ring
    rcases eq_or_eq_neg_of_sq_eq_sq M (e * f) hMsq with hM | hM
    · left
      exact ⟨e, f, by norm_num [hR₀, hf], he, hM⟩
    · left
      refine ⟨-e, f, ?_, ?_, ?_⟩
      · norm_num [hR₀, hf]
      · calc S = e ^ 2 := he
          _ = (-e) ^ 2 := by ring
      · calc M = -(e * f) := hM
          _ = (-e) * f := by ring
  · obtain ⟨S₀, hS₀⟩ := htwoS
    have hS₀pos : 0 < S₀ := by
      rw [hS₀] at hSpos
      nlinarith
    have hcop' : IsCoprime R S := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    rw [hS₀] at hcop'
    have hcop₀ : IsCoprime R S₀ := hcop'.of_mul_right_right
    have hprod₀ : R * S₀ = M ^ 2 := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      calc
        (2 : ℤ) * (R * S₀) = R * S := by rw [hS₀]; ring
        _ = 2 * M ^ 2 := hprod
    obtain ⟨f, hf⟩ := positive_factor_square_of_coprime hRpos hcop₀ hprod₀
    obtain ⟨e, he⟩ := positive_factor_square_of_coprime hS₀pos hcop₀.symm (by
      rw [mul_comm]
      exact hprod₀)
    have hMsq : M ^ 2 = (e * f) ^ 2 := by
      calc
        M ^ 2 = R * S₀ := hprod₀.symm
        _ = (e * f) ^ 2 := by rw [hf, he]; ring
    rcases eq_or_eq_neg_of_sq_eq_sq M (e * f) hMsq with hM | hM
    · right
      exact ⟨e, f, hf, by norm_num [hS₀, he], hM⟩
    · right
      refine ⟨-e, f, ?_, ?_, ?_⟩
      · exact hf
      · calc S = 2 * S₀ := hS₀
          _ = 2 * (-e) ^ 2 := by rw [he]; ring
      · calc M = -(e * f) := hM
          _ = (-e) * f := by ring

theorem positive_model_primitive_split {A D C : ℤ}
    (hcop : Int.gcd A D = 1)
    (hcurve : C ^ 2 = normReal A D ^ 2 + 2 * normImag A D ^ 2) :
    ∃ R S : ℤ,
      C = R + S ∧ normReal A D = S - R ∧ Int.gcd R S = 1 ∧
      R * S = 2 * (A * D * (A + D)) ^ 2 := by
  have hQeven : Even (normImag A D) := by
    simp only [normImag]
    simpa [mul_assoc] using even_two_mul (A * D * (A + D))
  obtain ⟨R, S, M, hM, hC, hP, hRS, hprod⟩ :=
    primitive_norm_split (norm_components_coprime A D hcop)
      (normReal_odd A D hcop) hQeven hcurve
  have hMeq : M = A * D * (A + D) := by
    simp only [normImag] at hM
    linarith
  subst M
  exact ⟨R, S, hC, hP, hRS, hprod⟩

/-- A positive primitive solution of the N=18 sextic has the expected
primitive `ℤ[√-2]` parametrization.  The two alternatives record which of the
coprime half-sum factors contains the unique factor `2`. -/
theorem positive_model_norm_parametrization {A D C : ℤ}
    (hA : 0 < A) (hD : 0 < D) (hcop : Int.gcd A D = 1)
    (hcurve : C ^ 2 = normReal A D ^ 2 + 2 * normImag A D ^ 2) :
    ∃ e f : ℤ,
      Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      ((normReal A D = e ^ 2 - 2 * f ^ 2 ∧
          |C| = e ^ 2 + 2 * f ^ 2) ∨
       (normReal A D = 2 * e ^ 2 - f ^ 2 ∧
          |C| = 2 * e ^ 2 + f ^ 2)) := by
  have hcurveAbs : |C| ^ 2 =
      normReal A D ^ 2 + 2 * normImag A D ^ 2 := by
    simpa only [sq_abs] using hcurve
  obtain ⟨R, S, hC, hP, hcopRS, hprod⟩ :=
    positive_model_primitive_split hcop hcurveAbs
  have hQpos : 0 < normImag A D := by
    simp only [normImag]
    positivity
  have hsq : normReal A D ^ 2 < |C| ^ 2 := by
    rw [hcurveAbs]
    nlinarith [sq_pos_of_pos hQpos]
  have hbounds : -|C| < normReal A D ∧ normReal A D < |C| :=
    abs_lt_of_sq_lt_sq' hsq (abs_nonneg C)
  have hRpos : 0 < R := by nlinarith [hbounds.2]
  have hSpos : 0 < S := by nlinarith [hbounds.1]
  rcases positive_coprime_twice_square_split hRpos hSpos hcopRS hprod with
      hfirst | hsecond
  · obtain ⟨e, f, hR, hS, hM⟩ := hfirst
    have hcop' : IsCoprime R S := Int.isCoprime_iff_gcd_eq_one.mpr hcopRS
    rw [hR, hS] at hcop'
    have hcopSquares : IsCoprime (f ^ 2) (e ^ 2) := hcop'.of_mul_left_right
    have hcopFE : IsCoprime f e :=
      (IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)).mp hcopSquares
    have hcopEF : Int.gcd e f = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hcopFE.symm
    refine ⟨e, f, hcopEF, hM.symm, Or.inl ⟨?_, ?_⟩⟩
    · calc
        normReal A D = S - R := hP
        _ = e ^ 2 - 2 * f ^ 2 := by rw [hR, hS]
    · calc
        |C| = R + S := hC
        _ = e ^ 2 + 2 * f ^ 2 := by rw [hR, hS]; ring
  · obtain ⟨e, f, hR, hS, hM⟩ := hsecond
    have hcop' : IsCoprime R S := Int.isCoprime_iff_gcd_eq_one.mpr hcopRS
    rw [hR, hS] at hcop'
    have hcopSquares : IsCoprime (f ^ 2) (e ^ 2) := hcop'.of_mul_right_right
    have hcopFE : IsCoprime f e :=
      (IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)).mp hcopSquares
    have hcopEF : Int.gcd e f = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hcopFE.symm
    refine ⟨e, f, hcopEF, hM.symm, Or.inr ⟨?_, ?_⟩⟩
    · calc
        normReal A D = S - R := hP
        _ = 2 * e ^ 2 - f ^ 2 := by rw [hR, hS]
    · calc
        |C| = R + S := hC
        _ = 2 * e ^ 2 + f ^ 2 := by rw [hR, hS]; ring

/-- The roots in the norm parametrization can be chosen strictly positive. -/
theorem positive_model_norm_parametrization_pos {A D C : ℤ}
    (hA : 0 < A) (hD : 0 < D) (hcop : Int.gcd A D = 1)
    (hcurve : C ^ 2 = normReal A D ^ 2 + 2 * normImag A D ^ 2) :
    ∃ e f : ℤ,
      0 < e ∧ 0 < f ∧ Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      ((normReal A D = e ^ 2 - 2 * f ^ 2 ∧
          |C| = e ^ 2 + 2 * f ^ 2) ∨
       (normReal A D = 2 * e ^ 2 - f ^ 2 ∧
          |C| = 2 * e ^ 2 + f ^ 2)) := by
  obtain ⟨e, f, hcopEF, hmul, hforms⟩ :=
    positive_model_norm_parametrization hA hD hcop hcurve
  have hMpos : 0 < A * D * (A + D) := by positivity
  have hprodne : e * f ≠ 0 := by rw [hmul]; exact ne_of_gt hMpos
  have he : e ≠ 0 := (mul_ne_zero_iff.mp hprodne).1
  have hf : f ≠ 0 := (mul_ne_zero_iff.mp hprodne).2
  have hcopAbs : Int.gcd |e| |f| = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    have hef : IsCoprime e f := Int.isCoprime_iff_gcd_eq_one.mpr hcopEF
    exact hef.abs_left.abs_right
  have hmulAbs : |e| * |f| = A * D * (A + D) := by
    rw [← abs_mul, hmul, abs_of_pos hMpos]
  refine ⟨|e|, |f|, abs_pos.mpr he, abs_pos.mpr hf, hcopAbs, hmulAbs, ?_⟩
  simpa only [sq_abs] using hforms

/-! ## Prime-by-prime allocation of the three coprime factors -/

theorem prime_not_dvd_both_of_gcd_one {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hcop : Int.gcd a b = 1) (hpa : (p : ℤ) ∣ a) :
    ¬(p : ℤ) ∣ b := by
  intro hpb
  have hpOneZ : (p : ℤ) ∣ (1 : ℤ) := by
    simpa [hcop] using Int.dvd_coe_gcd hpa hpb
  have hpOne : p ∣ 1 := by exact_mod_cast hpOneZ
  exact hp.not_dvd_one hpOne

/-- Every prime factor of a product `e*f` with `gcd(e,f)=1` occurs in exactly
one of the two roots. -/
theorem prime_allocated_to_exactly_one_root {p : ℕ} {e f M : ℤ}
    (hp : p.Prime) (hcop : Int.gcd e f = 1) (hmul : e * f = M)
    (hpM : (p : ℤ) ∣ M) :
    ((p : ℤ) ∣ e ∧ ¬(p : ℤ) ∣ f) ∨
    ((p : ℤ) ∣ f ∧ ¬(p : ℤ) ∣ e) := by
  have hpProd : (p : ℤ) ∣ e * f := by rwa [hmul]
  rcases Int.Prime.dvd_mul' hp hpProd with hpe | hpf
  · exact Or.inl ⟨hpe, prime_not_dvd_both_of_gcd_one hp hcop hpe⟩
  · exact Or.inr ⟨hpf,
      prime_not_dvd_both_of_gcd_one hp (by simpa [Int.gcd_comm] using hcop) hpf⟩

/-- A prime divisor of `A*D*(A+D)` belongs to exactly one of its three
pairwise-coprime factors. -/
theorem prime_allocated_to_exactly_one_factor {p : ℕ} {A D : ℤ}
    (hp : p.Prime) (hcopAD : Int.gcd A D = 1)
    (hcopAS : Int.gcd A (A + D) = 1) (hcopDS : Int.gcd D (A + D) = 1)
    (hpM : (p : ℤ) ∣ A * D * (A + D)) :
    ((p : ℤ) ∣ A ∧ ¬(p : ℤ) ∣ D ∧ ¬(p : ℤ) ∣ A + D) ∨
    ((p : ℤ) ∣ D ∧ ¬(p : ℤ) ∣ A ∧ ¬(p : ℤ) ∣ A + D) ∨
    ((p : ℤ) ∣ A + D ∧ ¬(p : ℤ) ∣ A ∧ ¬(p : ℤ) ∣ D) := by
  rcases Int.Prime.dvd_mul' hp hpM with hpAD | hpS
  · rcases Int.Prime.dvd_mul' hp hpAD with hpA | hpD
    · exact Or.inl ⟨hpA,
        prime_not_dvd_both_of_gcd_one hp hcopAD hpA,
        prime_not_dvd_both_of_gcd_one hp hcopAS hpA⟩
    · exact Or.inr (Or.inl ⟨hpD,
        prime_not_dvd_both_of_gcd_one hp (by simpa [Int.gcd_comm] using hcopAD) hpD,
        prime_not_dvd_both_of_gcd_one hp hcopDS hpD⟩)
  · exact Or.inr (Or.inr ⟨hpS,
      prime_not_dvd_both_of_gcd_one hp (by simpa [Int.gcd_comm] using hcopAS) hpS,
      prime_not_dvd_both_of_gcd_one hp (by simpa [Int.gcd_comm] using hcopDS) hpS⟩)

/-! ## The first local restriction -/

/-- Over `ZMod 5`, a square value of the positive sextic forces one of the
three homogeneous cusp factors to vanish. -/
theorem square_mod_five_forces_cusp (a d c : ZMod 5)
    (h : c ^ 2 =
      a ^ 6 + 2 * a ^ 5 * d + 5 * a ^ 4 * d ^ 2 + 10 * a ^ 3 * d ^ 3
        + 10 * a ^ 2 * d ^ 4 + 4 * a * d ^ 5 + d ^ 6) :
    a = 0 ∨ d = 0 ∨ a + d = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra hcusp
  push Not at hcusp
  obtain ⟨ha, hd, hs⟩ := hcusp
  have ha4 : a ^ 4 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one ha
  have hd4 : d ^ 4 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hd
  have hfive : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
  have hpoly :
      a ^ 6 + 2 * a ^ 5 * d + 5 * a ^ 4 * d ^ 2 + 10 * a ^ 3 * d ^ 3
          + 10 * a ^ 2 * d ^ 4 + 4 * a * d ^ 5 + d ^ 6 =
        a ^ 2 + a * d + d ^ 2 := by
    linear_combination
      a ^ 2 * ha4 + 2 * a * d * ha4 + 4 * a * d * hd4 + d ^ 2 * hd4 +
      (a * d + a ^ 4 * d ^ 2 + 2 * a ^ 3 * d ^ 3 + 2 * a ^ 2 * d ^ 4) * hfive
  have hred : c ^ 2 = a ^ 2 + a * d + d ^ 2 := h.trans hpoly
  let x : ZMod 5 := a / d
  let z : ZMod 5 := c / d
  have hx0 : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero ha hd
  have hxplus : x + 1 ≠ 0 := by
    have hsum : x + 1 = (a + d) / d := by
      dsimp [x]
      field_simp [hd]
    rw [hsum]
    exact div_ne_zero hs hd
  have hnorm : z ^ 2 = x ^ 2 + x + 1 := by
    dsimp [x, z]
    field_simp [hd]
    linear_combination hred
  have hx4 : x ^ 4 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hfactor : (x - 1) * (x + 1) * (x ^ 2 + 1) = 0 := by
    calc
      (x - 1) * (x + 1) * (x ^ 2 + 1) = x ^ 4 - 1 := by ring
      _ = 0 := by rw [hx4]; ring
  have htwo : (2 : ZMod 5) ≠ 0 := by
    intro htwozero
    have honezero : (1 : ZMod 5) = 0 := by
      linear_combination hfive - 2 * htwozero
    exact one_ne_zero honezero
  have hthree : (3 : ZMod 5) ≠ 0 := by
    intro hthreezero
    have honezero : (1 : ZMod 5) = 0 := by
      linear_combination 2 * hthreezero - hfive
    exact one_ne_zero honezero
  have hone_four : (1 : ZMod 5) ≠ 4 := by
    intro h14
    have hthreezero : (3 : ZMod 5) = 0 := by
      calc
        (3 : ZMod 5) = 4 - 1 := by ring
        _ = 0 := by rw [← h14]; ring
    exact hthree hthreezero
  have hone_negone : (1 : ZMod 5) ≠ -1 := by
    intro h1n
    have htwozero : (2 : ZMod 5) = 0 := by
      calc
        (2 : ZMod 5) = 1 + 1 := by ring
        _ = -1 + 1 := congrArg (· + 1) h1n
        _ = 0 := by ring
    exact htwo htwozero
  rcases mul_eq_zero.mp hfactor with hpair | hquad
  · rcases mul_eq_zero.mp hpair with hxone | hxneg
    · have hx : x = 1 := sub_eq_zero.mp hxone
      have hzsq : z ^ 2 = 3 := by
        rw [hx] at hnorm
        linear_combination hnorm
      have hz0 : z ≠ 0 := by
        intro hz
        rw [hz, zero_pow (by norm_num : 2 ≠ 0)] at hzsq
        exact hthree hzsq.symm
      have hz4 : z ^ 4 = 1 := by
        simpa using ZMod.pow_card_sub_one_eq_one hz0
      have hz4' : z ^ 4 = 4 := by
        calc
          z ^ 4 = (z ^ 2) ^ 2 := by ring
          _ = (3 : ZMod 5) ^ 2 := by rw [hzsq]
          _ = 4 := by linear_combination hfive
      exact hone_four (hz4.symm.trans hz4')
    · exact hxplus hxneg
  · have hzsq : z ^ 2 = x := by linear_combination hnorm + hquad
    have hz0 : z ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by norm_num : 2 ≠ 0)] at hzsq
      exact hx0 hzsq.symm
    have hz4 : z ^ 4 = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one hz0
    have hz4' : z ^ 4 = -1 := by
      calc
        z ^ 4 = (z ^ 2) ^ 2 := by ring
        _ = x ^ 2 := by rw [hzsq]
        _ = -1 := by linear_combination hquad
    exact hone_negone (hz4.symm.trans hz4')

theorem five_dvd_cusp_product_of_square {A D C : ℤ}
    (hC : C ^ 2 = F18Positive A D) :
    (5 : ℤ) ∣ A * D * (A + D) := by
  have hcast := congrArg (fun z : ℤ => (z : ZMod 5)) hC
  have hmod : (C : ZMod 5) ^ 2 =
      (A : ZMod 5) ^ 6 + 2 * (A : ZMod 5) ^ 5 * (D : ZMod 5)
        + 5 * (A : ZMod 5) ^ 4 * (D : ZMod 5) ^ 2
        + 10 * (A : ZMod 5) ^ 3 * (D : ZMod 5) ^ 3
        + 10 * (A : ZMod 5) ^ 2 * (D : ZMod 5) ^ 4
        + 4 * (A : ZMod 5) * (D : ZMod 5) ^ 5 + (D : ZMod 5) ^ 6 := by
    simpa [F18Positive] using hcast
  have hcusp := square_mod_five_forces_cusp (A : ZMod 5) (D : ZMod 5)
    (C : ZMod 5) hmod
  have hzero : ((A * D * (A + D) : ℤ) : ZMod 5) = 0 := by
    push_cast
    rcases hcusp with hA | hD | hS
    · rw [hA]
      ring
    · rw [hD]
      ring
    · rw [hS]
      ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (A * D * (A + D)) 5).mp hzero

/-- Strong denominator-cleared consequence of a noncuspidal rational point:
the three positive factors are pairwise coprime and their sextic norm is a
square. -/
theorem noncuspidal_point_to_primitive_norm {U Y : ℚ}
    (hU0 : U ≠ 0) (hU1 : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    ∃ A D C : ℤ,
      0 < A ∧ 0 < D ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧ Int.gcd D (A + D) = 1 ∧
      Odd (normReal A D) ∧ Int.gcd (normReal A D) (normImag A D) = 1 ∧
      C ^ 2 = F18Positive A D ∧
      C ^ 2 = normReal A D ^ 2 + 2 * normImag A D ^ 2 := by
  obtain ⟨u, y, hu0, hu1, hy⟩ := normalize_curve_point hU0 hU1 hY
  obtain ⟨A, B, C, hA, hAB, hcopAB, hu, hC⟩ :=
    normalized_integral_model hu0 hu1 hy
  let D : ℤ := B - A
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hB : B = A + D := by
    dsimp [D]
    ring
  have hcopAD : Int.gcd A D = 1 := by
    dsimp [D]
    exact gcd_sub_right A B hcopAB
  have hcopAS : Int.gcd A (A + D) = 1 := gcd_sum_right A D hcopAD
  have hcopDS : Int.gcd D (A + D) = 1 := gcd_sum_left A D hcopAD
  have hPodd : Odd (normReal A D) := normReal_odd A D hcopAD
  have hPQ : Int.gcd (normReal A D) (normImag A D) = 1 :=
    norm_components_coprime A D hcopAD
  have hCpos : C ^ 2 = F18Positive A D := by
    rw [hB] at hC
    exact hC.trans (F18Hom_substitution A D)
  refine ⟨A, D, C, hA, hD, hcopAD, hcopAS, hcopDS, hPodd, hPQ, hCpos, ?_⟩
  calc
    C ^ 2 = F18Positive A D := hCpos
    _ = normReal A D ^ 2 + 2 * normImag A D ^ 2 := F18Positive_norm A D

/-- The complete elementary descent front end, starting directly from a
noncuspidal rational point on the standard genus-two model. -/
theorem noncuspidal_point_to_norm_parametrization {U Y : ℚ}
    (hU0 : U ≠ 0) (hU1 : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    ∃ A D C e f : ℤ,
      0 < A ∧ 0 < D ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧ Int.gcd D (A + D) = 1 ∧
      Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      ((normReal A D = e ^ 2 - 2 * f ^ 2 ∧ |C| = e ^ 2 + 2 * f ^ 2) ∨
       (normReal A D = 2 * e ^ 2 - f ^ 2 ∧ |C| = 2 * e ^ 2 + f ^ 2)) := by
  obtain ⟨A, D, C, hA, hD, hcop, hcopAS, hcopDS, hPodd, hPQ, hCF, hcurve⟩ :=
    noncuspidal_point_to_primitive_norm hU0 hU1 hY
  obtain ⟨e, f, hcopEF, hmul, hforms⟩ :=
    positive_model_norm_parametrization hA hD hcop hcurve
  exact ⟨A, D, C, e, f, hA, hD, hcop, hcopAS, hcopDS, hcopEF, hmul, hforms⟩

/-- Strongest elementary descent package currently extracted from a
noncuspidal point.  In addition to the positive primitive norm parameters, it
records the exact prime-by-prime allocation forced at `5`. -/
theorem noncuspidal_point_to_five_descent {U Y : ℚ}
    (hU0 : U ≠ 0) (hU1 : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    ∃ A D C e f : ℤ,
      0 < A ∧ 0 < D ∧ 0 < e ∧ 0 < f ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧ Int.gcd D (A + D) = 1 ∧
      Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      ((normReal A D = e ^ 2 - 2 * f ^ 2 ∧ |C| = e ^ 2 + 2 * f ^ 2) ∨
       (normReal A D = 2 * e ^ 2 - f ^ 2 ∧ |C| = 2 * e ^ 2 + f ^ 2)) ∧
      (((5 : ℤ) ∣ e ∧ ¬(5 : ℤ) ∣ f) ∨ ((5 : ℤ) ∣ f ∧ ¬(5 : ℤ) ∣ e)) ∧
      (((5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A + D) ∨
       ((5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ A + D) ∨
       ((5 : ℤ) ∣ A + D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D)) := by
  obtain ⟨A, D, C, hA, hD, hcop, hcopAS, hcopDS, hPodd, hPQ, hCF, hcurve⟩ :=
    noncuspidal_point_to_primitive_norm hU0 hU1 hY
  obtain ⟨e, f, he, hf, hcopEF, hmul, hforms⟩ :=
    positive_model_norm_parametrization_pos hA hD hcop hcurve
  have hfive : (5 : ℤ) ∣ A * D * (A + D) :=
    five_dvd_cusp_product_of_square hCF
  have hroot := prime_allocated_to_exactly_one_root Nat.prime_five hcopEF hmul hfive
  have hfactor := prime_allocated_to_exactly_one_factor Nat.prime_five
    hcop hcopAS hcopDS hfive
  exact ⟨A, D, C, e, f, hA, hD, he, hf, hcop, hcopAS, hcopDS,
    hcopEF, hmul, hforms, hroot, hfactor⟩

end

/-! ## Reverse bridge: five-descent data → noncuspidal rational point -/

section ReverseBridge

open RationalPointsN18

/-- Both descent forms give `C² = F18Positive A D`: the form identity
`(e²±2f²)² = (e²∓2f²)² + 8(ef)²` combined with `normImag = 2·ef`. -/
theorem C_sq_eq_F18Positive {A D C e f : ℤ}
    (hef : e * f = A * D * (A + D))
    (hforms : (normReal A D = e ^ 2 - 2 * f ^ 2 ∧ |C| = e ^ 2 + 2 * f ^ 2) ∨
              (normReal A D = 2 * e ^ 2 - f ^ 2 ∧ |C| = 2 * e ^ 2 + f ^ 2)) :
    C ^ 2 = F18Positive A D := by
  have hsq : C ^ 2 = |C| ^ 2 := (sq_abs C).symm
  rw [hsq, F18Positive_norm]
  have himag : normImag A D = 2 * (e * f) := by
    simp only [normImag]
    nlinarith [hef]
  rw [himag]
  rcases hforms with ⟨hN, hC⟩ | ⟨hN, hC⟩ <;> rw [hC, hN] <;> ring

/-- Five-descent data produces a noncuspidal rational point on `X₁(18)`. -/
theorem five_descent_to_noncuspidal {A D C e f : ℤ}
    (hA : 0 < A) (hD : 0 < D)
    (hef : e * f = A * D * (A + D))
    (hforms : (normReal A D = e ^ 2 - 2 * f ^ 2 ∧ |C| = e ^ 2 + 2 * f ^ 2) ∨
              (normReal A D = 2 * e ^ 2 - f ^ 2 ∧ |C| = 2 * e ^ 2 + f ^ 2)) :
    ∃ U Y : ℚ, U ≠ 0 ∧ U ≠ 1 ∧ Y ^ 2 = hyperellipticF18 U := by
  set B := A + D with hB_def
  have hBpos : (0 : ℤ) < B := by omega
  have hBne : (B : ℤ) ≠ 0 := ne_of_gt hBpos
  have hBneQ : ((B : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBne
  have hCsq := C_sq_eq_F18Positive hef hforms
  refine ⟨(A : ℚ) / (B : ℚ), (C : ℚ) / (B : ℚ) ^ 3, ?_, ?_, ?_⟩
  · exact div_ne_zero (Int.cast_ne_zero.mpr (ne_of_gt hA)) hBneQ
  · intro h
    have hAeqB : (A : ℚ) = (B : ℚ) := by
      rwa [div_eq_iff hBneQ, one_mul] at h
    have : A = B := by exact_mod_cast hAeqB
    omega
  · have h6ne : (B : ℚ) ^ 6 ≠ 0 := pow_ne_zero 6 hBneQ
    rw [div_pow, show ((B : ℚ) ^ 3) ^ 2 = (B : ℚ) ^ 6 from by ring,
      div_eq_iff h6ne, mul_comm]
    have hclear := F18Hom_clear_denominators A B hBne
    rw [hclear]
    have hFsub : C ^ 2 = F18Hom A B := by
      rw [hB_def, F18Hom_substitution]; exact hCsq
    exact_mod_cast hFsub

end ReverseBridge

end MazurProof.RationalPointsN18Descent
