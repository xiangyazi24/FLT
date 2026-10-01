import FLT.Assumptions.MazurProof.TateOrder16Cyclic
import scratch.FermatFourthDifferenceN16

/-!
# Rational points on the split model of `X₁(16)`

The optimized affine model is

`y² + (x³ + x² - x + 1)y + x² = 0`.

Completing the square gives the split genus-two model

`Y² = (x²-1)(x²+1)(x²+2x-1)`.

This file proves that its rational `x`-coordinates are `-1, 0, 1` by an
integer factor descent.  The opposite-parity branch uses Fermat's classical
descent for `X⁴-Y⁴=Z²`; the odd/odd branch reduces to Mathlib's
`not_fermat_42` through `X⁴-Y⁴=2Z²`.
-/

namespace MazurProof.RationalPointsX116

def factorP (A B : ℤ) : ℤ := A ^ 2 - B ^ 2
def factorQ (A B : ℤ) : ℤ := A ^ 2 + B ^ 2
def factorR (A B : ℤ) : ℤ := A ^ 2 + 2 * A * B - B ^ 2

def hyperellipticF16 (x : ℚ) : ℚ :=
  (x - 1) * (x + 1) * (x ^ 2 + 1) * (x ^ 2 + 2 * x - 1)

def optimizedX116 (x y : ℚ) : Prop :=
  y ^ 2 + (x ^ 3 + x ^ 2 - x + 1) * y + x ^ 2 = 0

theorem complete_square (x y : ℚ) (h : optimizedX116 x y) :
    (2 * y + (x ^ 3 + x ^ 2 - x + 1)) ^ 2 = hyperellipticF16 x := by
  unfold optimizedX116 at h
  unfold hyperellipticF16
  nlinarith [h]

private theorem odd_sq_eight_mul_add_one {n : ℤ} (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  rcases Int.two_dvd_mul_add_one t with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
    _ = 4 * (2 * u) + 1 := by rw [hu]
    _ = 8 * u + 1 := by ring

private theorem not_square_two_mul_odd {z n : ℤ} (hn : Odd n) :
    z ^ 2 ≠ 2 * n := by
  intro h
  rcases hn with ⟨k, rfl⟩
  rcases Int.even_or_odd z with hz | hz
  · rcases hz with ⟨w, rfl⟩
    have hsq : (w + w) ^ 2 = 4 * w ^ 2 := by ring
    rw [hsq] at h
    omega
  · rcases hz with ⟨w, rfl⟩
    have hsq : (2 * w + 1) ^ 2 = 4 * (w ^ 2 + w) + 1 := by ring
    rw [hsq] at h
    omega

private theorem odd_ne_zero {n : ℤ} (hn : Odd n) : n ≠ 0 := by
  intro h
  rw [h] at hn
  exact (by simpa using hn : False)

private theorem normalized_R_coprime_P
    {A B P0 R0 : ℤ}
    (hAB : Int.gcd A B = 1)
    (hRodd : Odd R0)
    (hPdvd : P0 ∣ factorP A B)
    (hRdvd : R0 ∣ factorR A B) :
    IsCoprime R0 P0 := by
  have hAB' : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hAB
  have hRtwo : IsCoprime R0 (2 : ℤ) := Int.isCoprime_two_right.mpr hRodd
  refine isCoprime_of_prime_dvd ?_ ?_
  · rintro ⟨hR0, _⟩
    exact odd_ne_zero hRodd hR0
  · intro p hp hpR0 hpP0
    have hpR : p ∣ factorR A B := dvd_trans hpR0 hRdvd
    have hpP : p ∣ factorP A B := dvd_trans hpP0 hPdvd
    have hp2 : ¬p ∣ (2 : ℤ) := by
      intro hp2
      exact hp.not_unit (hRtwo.isUnit_of_dvd' hpR0 hp2)
    have hp2AB : p ∣ 2 * (A * B) := by
      have hsub := dvd_sub hpR hpP
      have heq : factorR A B - factorP A B = 2 * (A * B) := by
        simp only [factorR, factorP]
        ring
      rwa [heq] at hsub
    have hpAB : p ∣ A * B := (hp.dvd_mul.mp hp2AB).resolve_left hp2
    rcases hp.dvd_mul.mp hpAB with hpA | hpB
    · have hpA2 : p ∣ A ^ 2 := dvd_pow hpA (by norm_num : (2 : ℕ) ≠ 0)
      have hpB2 : p ∣ B ^ 2 := by
        have h := dvd_sub hpA2 hpP
        have heq : A ^ 2 - factorP A B = B ^ 2 := by
          simp only [factorP]
          ring
        rwa [heq] at h
      have hpB' : p ∣ B := hp.dvd_of_dvd_pow hpB2
      exact hp.not_unit (hAB'.isUnit_of_dvd' hpA hpB')
    · have hpB2 : p ∣ B ^ 2 := dvd_pow hpB (by norm_num : (2 : ℕ) ≠ 0)
      have hpA2 : p ∣ A ^ 2 := by
        have h := dvd_add hpP hpB2
        have heq : factorP A B + B ^ 2 = A ^ 2 := by
          simp only [factorP]
          ring
        rwa [heq] at h
      have hpA' : p ∣ A := hp.dvd_of_dvd_pow hpA2
      exact hp.not_unit (hAB'.isUnit_of_dvd' hpA' hpB)

private theorem normalized_R_coprime_Q
    {A B Q0 R0 : ℤ}
    (hAB : Int.gcd A B = 1)
    (hRodd : Odd R0)
    (hQdvd : Q0 ∣ factorQ A B)
    (hRdvd : R0 ∣ factorR A B) :
    IsCoprime R0 Q0 := by
  have hAB' : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hAB
  have hRtwo : IsCoprime R0 (2 : ℤ) := Int.isCoprime_two_right.mpr hRodd
  refine isCoprime_of_prime_dvd ?_ ?_
  · rintro ⟨hR0, _⟩
    exact odd_ne_zero hRodd hR0
  · intro p hp hpR0 hpQ0
    have hpR : p ∣ factorR A B := dvd_trans hpR0 hRdvd
    have hpQ : p ∣ factorQ A B := dvd_trans hpQ0 hQdvd
    have hp2 : ¬p ∣ (2 : ℤ) := by
      intro hp2
      exact hp.not_unit (hRtwo.isUnit_of_dvd' hpR0 hp2)
    have hpDiff : p ∣ 2 * (B * (A - B)) := by
      have hsub := dvd_sub hpR hpQ
      have heq : factorR A B - factorQ A B = 2 * (B * (A - B)) := by
        simp only [factorR, factorQ]
        ring
      rwa [heq] at hsub
    have hpBA : p ∣ B * (A - B) := (hp.dvd_mul.mp hpDiff).resolve_left hp2
    rcases hp.dvd_mul.mp hpBA with hpB | hpAmB
    · have hpB2 : p ∣ B ^ 2 := dvd_pow hpB (by norm_num : (2 : ℕ) ≠ 0)
      have hpA2 : p ∣ A ^ 2 := by
        have h := dvd_sub hpQ hpB2
        have heq : factorQ A B - B ^ 2 = A ^ 2 := by
          simp only [factorQ]
          ring
        rwa [heq] at h
      have hpA : p ∣ A := hp.dvd_of_dvd_pow hpA2
      exact hp.not_unit (hAB'.isUnit_of_dvd' hpA hpB)
    · have hpAmB2 : p ∣ (A - B) ^ 2 :=
        dvd_pow hpAmB (by norm_num : (2 : ℕ) ≠ 0)
      have hp2AB : p ∣ 2 * (A * B) := by
        have h := dvd_sub hpQ hpAmB2
        have heq : factorQ A B - (A - B) ^ 2 = 2 * (A * B) := by
          simp only [factorQ]
          ring
        rwa [heq] at h
      have hpAB : p ∣ A * B := (hp.dvd_mul.mp hp2AB).resolve_left hp2
      rcases hp.dvd_mul.mp hpAB with hpA | hpB
      · have hpB : p ∣ B := by
          have h := dvd_sub hpA hpAmB
          simpa only [show A - (A - B) = B by ring] using h
        exact hp.not_unit (hAB'.isUnit_of_dvd' hpA hpB)
      · have hpA : p ∣ A := by
          have h := dvd_add hpAmB hpB
          simpa only [show A - B + B = A by ring] using h
        exact hp.not_unit (hAB'.isUnit_of_dvd' hpA hpB)

private theorem square_int_of_rational_square
    {N : ℤ} {q : ℚ} (h : q ^ 2 = (N : ℚ)) :
    ∃ z : ℤ, z ^ 2 = N := by
  have hs : IsSquare (N : ℚ) := ⟨q, by rw [← sq]; exact h.symm⟩
  rw [Rat.isSquare_intCast_iff] at hs
  obtain ⟨z, hz⟩ := hs
  exact ⟨z, by rw [sq]; exact hz.symm⟩

private theorem fourth_product (A B : ℤ) :
    factorP A B * factorQ A B = A ^ 4 - B ^ 4 := by
  unfold factorP factorQ
  ring

private theorem opposite_parity_branch
    {A B C : ℤ}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hopposite : (Even A ∧ Odd B) ∨ (Odd A ∧ Even B))
    (hcurve : C ^ 2 = factorP A B * factorQ A B * factorR A B) :
    A = B ∨ A = -B := by
  have hPodd : Odd (factorP A B) := by
    rcases hopposite with ⟨hAe, hBo⟩ | ⟨hAo, hBe⟩
    · exact (hAe.pow_of_ne_zero (by norm_num)).sub_odd hBo.pow
    · exact hAo.pow.sub_even (hBe.pow_of_ne_zero (by norm_num))
  have hRodd : Odd (factorR A B) := by
    have htwoAB : Even (2 * (A * B)) := even_two_mul (A * B)
    rw [show factorR A B = factorP A B + 2 * (A * B) by
      simp only [factorR, factorP]; ring]
    exact hPodd.add_even htwoAB
  have hRP : IsCoprime (factorR A B) (factorP A B) :=
    normalized_R_coprime_P hAB hRodd (dvd_refl _) (dvd_refl _)
  have hRQ : IsCoprime (factorR A B) (factorQ A B) :=
    normalized_R_coprime_Q hAB hRodd (dvd_refl _) (dvd_refl _)
  have hRprod : IsCoprime (factorR A B) (factorP A B * factorQ A B) :=
    hRP.mul_right hRQ
  have hprod : (factorP A B * factorQ A B) * factorR A B = C ^ 2 := by
    calc
      (factorP A B * factorQ A B) * factorR A B =
          factorP A B * factorQ A B * factorR A B := by ring
      _ = C ^ 2 := hcurve.symm
  obtain ⟨Z, hZ | hZ⟩ := Int.sq_of_isCoprime hRprod.symm hprod
  · rw [fourth_product] at hZ
    by_cases hZ0 : Z = 0
    · have hsq : A ^ 2 = B ^ 2 := by
        rw [hZ0] at hZ
        nlinarith [sq_nonneg (A ^ 2 + B ^ 2)]
      exact eq_or_eq_neg_of_sq_eq_sq A B hsq
    · exact False.elim
        ((Scratch.FermatFourthDifferenceN16.no_coprime_fourth_difference
          hA0 hB0 hZ0 hAB) hZ.symm)
  · rw [fourth_product] at hZ
    by_cases hZ0 : Z = 0
    · have hsq : A ^ 2 = B ^ 2 := by
        rw [hZ0] at hZ
        nlinarith [sq_nonneg (A ^ 2 + B ^ 2)]
      exact eq_or_eq_neg_of_sq_eq_sq A B hsq
    · exact False.elim
        ((Scratch.FermatFourthDifferenceN16.no_coprime_fourth_difference
          hB0 hA0 hZ0 (by simpa [Int.gcd_comm] using hAB)) (by
            nlinarith [hZ]))

private theorem odd_branch
    {A B C : ℤ}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hAodd : Odd A) (hBodd : Odd B)
    (hcurve : C ^ 2 = factorP A B * factorQ A B * factorR A B) :
    A = B ∨ A = -B := by
  obtain ⟨a, ha⟩ := odd_sq_eight_mul_add_one hAodd
  obtain ⟨b, hb⟩ := odd_sq_eight_mul_add_one hBodd
  let P8 : ℤ := a - b
  let Q2 : ℤ := 4 * (a + b) + 1
  let R2 : ℤ := 4 * (a - b) + A * B
  have hP : factorP A B = 8 * P8 := by
    simp only [factorP, P8]
    rw [ha, hb]
    ring
  have hQ : factorQ A B = 2 * Q2 := by
    simp only [factorQ, Q2]
    rw [ha, hb]
    ring
  have hR : factorR A B = 2 * R2 := by
    simp only [factorR, R2]
    rw [ha, hb]
    ring
  have hQodd : Odd Q2 := by
    refine ⟨2 * (a + b), ?_⟩
    simp only [Q2]
    ring
  have hRodd : Odd R2 := by
    have hfour : Even (4 * (a - b)) := ⟨2 * (a - b), by ring⟩
    exact hfour.add_odd (hAodd.mul hBodd)
  have hscaled4 : ((C : ℚ) / 4) ^ 2 = (2 * P8 * Q2 * R2 : ℤ) := by
    have hcurveQ : (C : ℚ) ^ 2 =
        (factorP A B : ℚ) * factorQ A B * factorR A B := by
      exact_mod_cast hcurve
    calc
      ((C : ℚ) / 4) ^ 2 = (C : ℚ) ^ 2 / 16 := by ring
      _ = ((factorP A B : ℚ) * factorQ A B * factorR A B) / 16 := by rw [hcurveQ]
      _ = (2 * P8 * Q2 * R2 : ℤ) := by
        rw [hP, hQ, hR]
        push_cast
        ring
  obtain ⟨D, hD⟩ := square_int_of_rational_square hscaled4
  have hP8even : Even P8 := by
    rcases Int.even_or_odd P8 with h | h
    · exact h
    · have hoddProd : Odd (P8 * Q2 * R2) := (h.mul hQodd).mul hRodd
      exfalso
      exact (not_square_two_mul_odd hoddProd) (by nlinarith [hD])
  rcases hP8even with ⟨P16, hP16⟩
  have hP' : factorP A B = 16 * P16 := by
    rw [hP, hP16]
    ring
  have hscaled8 : ((C : ℚ) / 8) ^ 2 = (P16 * Q2 * R2 : ℤ) := by
    have hcurveQ : (C : ℚ) ^ 2 =
        (factorP A B : ℚ) * factorQ A B * factorR A B := by
      exact_mod_cast hcurve
    calc
      ((C : ℚ) / 8) ^ 2 = (C : ℚ) ^ 2 / 64 := by ring
      _ = ((factorP A B : ℚ) * factorQ A B * factorR A B) / 64 := by rw [hcurveQ]
      _ = (P16 * Q2 * R2 : ℤ) := by
        rw [hP', hQ, hR]
        push_cast
        ring
  obtain ⟨D8, hD8⟩ := square_int_of_rational_square hscaled8
  have hRP : IsCoprime R2 P16 :=
    normalized_R_coprime_P hAB hRodd
      ⟨16, by rw [hP']; ring⟩ ⟨2, by rw [hR]; ring⟩
  have hRQ : IsCoprime R2 Q2 :=
    normalized_R_coprime_Q hAB hRodd
      ⟨2, by rw [hQ]; ring⟩ ⟨2, by rw [hR]; ring⟩
  have hRprod : IsCoprime R2 (P16 * Q2) := hRP.mul_right hRQ
  have hprod : (P16 * Q2) * R2 = D8 ^ 2 := by
    calc
      (P16 * Q2) * R2 = P16 * Q2 * R2 := by ring
      _ = D8 ^ 2 := hD8.symm
  obtain ⟨Z, hZ | hZ⟩ := Int.sq_of_isCoprime hRprod.symm hprod
  · have hdiff : A ^ 4 - B ^ 4 = 2 * (4 * Z) ^ 2 := by
      calc
        A ^ 4 - B ^ 4 = factorP A B * factorQ A B := (fourth_product A B).symm
        _ = (16 * P16) * (2 * Q2) := by rw [hP', hQ]
        _ = 32 * (P16 * Q2) := by ring
        _ = 2 * (4 * Z) ^ 2 := by rw [hZ]; ring
    by_cases hZ0 : Z = 0
    · have hsq : A ^ 2 = B ^ 2 := by
        rw [hZ0] at hdiff
        nlinarith [sq_nonneg (A ^ 2 + B ^ 2)]
      exact eq_or_eq_neg_of_sq_eq_sq A B hsq
    · exact False.elim
        ((Scratch.FermatFourthDifferenceN16.no_twice_square_fourth_difference
          hA0 hB0 (mul_ne_zero (by norm_num) hZ0) hAodd hBodd) hdiff)
  · have hdiff : B ^ 4 - A ^ 4 = 2 * (4 * Z) ^ 2 := by
      calc
        B ^ 4 - A ^ 4 = -(factorP A B * factorQ A B) := by
          rw [fourth_product]
          ring
        _ = -((16 * P16) * (2 * Q2)) := by rw [hP', hQ]
        _ = -(32 * (P16 * Q2)) := by ring
        _ = 2 * (4 * Z) ^ 2 := by rw [hZ]; ring
    by_cases hZ0 : Z = 0
    · have hsq : A ^ 2 = B ^ 2 := by
        rw [hZ0] at hdiff
        nlinarith [sq_nonneg (A ^ 2 + B ^ 2)]
      exact eq_or_eq_neg_of_sq_eq_sq A B hsq
    · exact False.elim
        ((Scratch.FermatFourthDifferenceN16.no_twice_square_fourth_difference
          hB0 hA0 (mul_ne_zero (by norm_num) hZ0) hBodd hAodd) hdiff)

theorem primitive_integer_x_cusp
    {A B C : ℤ} (hBpos : 0 < B) (hAB : Int.gcd A B = 1)
    (hcurve : C ^ 2 = factorP A B * factorQ A B * factorR A B) :
    A = 0 ∨ A = B ∨ A = -B := by
  by_cases hA0 : A = 0
  · exact Or.inl hA0
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  rcases Int.even_or_odd A with hAe | hAo
  · rcases Int.even_or_odd B with hBe | hBo
    · exfalso
      have h2g : (2 : ℤ) ∣ (Int.gcd A B : ℤ) :=
        Int.dvd_coe_gcd hAe.two_dvd hBe.two_dvd
      rw [hAB] at h2g
      norm_num at h2g
    · exact Or.inr (opposite_parity_branch hA0 hB0 hAB (Or.inl ⟨hAe, hBo⟩) hcurve)
  · rcases Int.even_or_odd B with hBe | hBo
    · exact Or.inr (opposite_parity_branch hA0 hB0 hAB (Or.inr ⟨hAo, hBe⟩) hcurve)
    · exact Or.inr (odd_branch hA0 hB0 hAB hAo hBo hcurve)

theorem rational_hyperelliptic_x_cusp
    (x Y : ℚ) (hcurve : Y ^ 2 = hyperellipticF16 x) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  let A : ℤ := x.num
  let B : ℤ := x.den
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hBq : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  have hx : x = (A : ℚ) / (B : ℚ) := by
    simp only [A, B]
    exact (Rat.num_div_den x).symm
  have hAB : Int.gcd A B = 1 := by
    simp only [A, B, Int.gcd, Int.natAbs_natCast]
    exact x.reduced
  let N : ℤ := factorP A B * factorQ A B * factorR A B
  have hrat : (Y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at hcurve
    push_cast [N, factorP, factorQ, factorR, hyperellipticF16] at hcurve ⊢
    field_simp [hBq] at hcurve ⊢
    nlinarith
  obtain ⟨C, hC⟩ := square_int_of_rational_square hrat
  have hcusp := primitive_integer_x_cusp hBpos hAB (by simpa [N] using hC)
  rcases hcusp with hA | hA | hA
  · right; left
    rw [hx, hA]
    simp
  · right; right
    rw [hx, hA]
    field_simp [hBq]
  · left
    rw [hx, hA]
    field_simp [hBq]
    norm_num

theorem optimized_x_cusp (x y : ℚ) (h : optimizedX116 x y) :
    x = -1 ∨ x = 0 ∨ x = 1 :=
  rational_hyperelliptic_x_cusp x (2 * y + (x ^ 3 + x ^ 2 - x + 1))
    (complete_square x y h)

/-! ## The verified birational map from the Tate equation -/

/-- Sutherland's raw affine equation for `X₁(16)`. -/
def rawF16 (r s : ℚ) : ℚ :=
  r ^ 3 * s ^ 2 - 4 * r ^ 3 * s + 2 * r ^ 3 + 3 * r ^ 2 * s ^ 2 +
    2 * r ^ 2 * s - 2 * r ^ 2 - r * s ^ 5 + 4 * r * s ^ 4 -
    10 * r * s ^ 3 + 6 * r * s ^ 2 - 3 * r * s + r + s ^ 4

def rawChartDenominator (r s : ℚ) : ℚ := r - s ^ 2 + s - 1

def rawModelX (r s : ℚ) : ℚ :=
  -(r - s) * (s - 1) / rawChartDenominator r s

def rawModelY (r s : ℚ) : ℚ :=
  (r * s ^ 2 - 3 * r * s + r + s ^ 2) / rawChartDenominator r s

/-- The homogeneous Tate equation becomes the raw `X₁(16)` equation under
`b = r s (r-1)` and `c = s (r-1)`. -/
theorem phi16_raw_identity (r s : ℚ) :
    KubertBridgeN16.Phi16 (r * s * (r - 1)) (s * (r - 1)) =
      s ^ 8 * (r - 1) ^ 13 * rawF16 r s := by
  unfold KubertBridgeN16.Phi16 rawF16
  ring

private theorem phi16_self (b : ℚ) :
    KubertBridgeN16.Phi16 b b = -b ^ 13 := by
  unfold KubertBridgeN16.Phi16
  ring

/-- A nondegenerate Tate datum lands on the raw affine model. -/
theorem raw_point_of_X116Datum {b c : ℚ}
    (h : TateOrder16Cyclic.X116Datum b c) :
    ∃ r s : ℚ, r ≠ 1 ∧ s ≠ 0 ∧ rawF16 r s = 0 := by
  rcases h with ⟨hb, hc, _, hPhi⟩
  have hbc : b ≠ c := by
    intro hbc
    subst c
    rw [phi16_self] at hPhi
    exact (neg_ne_zero.mpr (pow_ne_zero 13 hb)) hPhi
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hcRecover : c = s * (r - 1) := by
    dsimp only [r, s]
    field_simp [hc, hbc]
    <;> ring
  have hbRecover : b = r * s * (r - 1) := by
    dsimp only [r, s]
    field_simp [hc, hbc]
    <;> ring
  have hs : s ≠ 0 := by
    dsimp only [s]
    exact div_ne_zero (pow_ne_zero 2 hc) (sub_ne_zero.mpr hbc)
  have hr : r ≠ 1 := by
    intro hr
    apply hc
    rw [hcRecover, hr]
    ring
  have hPhiRaw :
      KubertBridgeN16.Phi16 (r * s * (r - 1)) (s * (r - 1)) = 0 := by
    rw [← hbRecover, ← hcRecover]
    exact hPhi
  rw [phi16_raw_identity] at hPhiRaw
  have hpref : s ^ 8 * (r - 1) ^ 13 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 8 hs) (pow_ne_zero 13 (sub_ne_zero.mpr hr))
  exact ⟨r, s, hr, hs, (mul_eq_zero.mp hPhiRaw).resolve_left hpref⟩

private theorem rawF16_on_exceptional_chart (s : ℚ) :
    rawF16 (s ^ 2 - s + 1) s = (s - 1) ^ 8 := by
  unfold rawF16
  ring

theorem rawChartDenominator_ne_zero {r s : ℚ}
    (hr : r ≠ 1) (hF : rawF16 r s = 0) :
    rawChartDenominator r s ≠ 0 := by
  intro hD
  have hrs : r = s ^ 2 - s + 1 := by
    unfold rawChartDenominator at hD
    linarith
  have hid := rawF16_on_exceptional_chart s
  rw [← hrs, hF] at hid
  have hs1sub : s - 1 = 0 :=
    (pow_eq_zero_iff (by norm_num : (8 : ℕ) ≠ 0)).mp hid.symm
  apply hr
  rw [hrs]
  nlinarith

/-- The inverse rational map satisfies the optimized affine equation on the
nonexceptional raw chart. -/
theorem raw_to_optimized {r s : ℚ}
    (hF : rawF16 r s = 0) (hD : rawChartDenominator r s ≠ 0) :
    optimizedX116 (rawModelX r s) (rawModelY r s) := by
  unfold optimizedX116 rawModelX rawModelY
  field_simp [hD]
  unfold rawF16 at hF
  unfold rawChartDenominator
  linear_combination (-(s - 1) ^ 2 * (r * s - 2 * r + 1)) * hF

private theorem rawF16_at_s_one (r : ℚ) :
    rawF16 r 1 = -(r - 1) ^ 3 := by
  unfold rawF16
  ring

private theorem rawF16_on_diagonal (s : ℚ) :
    rawF16 s s = -s * (s - 1) ^ 5 := by
  unfold rawF16
  ring

private theorem rawF16_at_x_neg_one_parameter (s : ℚ) (hden : 2 - s ≠ 0) :
    (2 - s) ^ 3 * rawF16 (1 / (2 - s)) s = -2 * (s - 1) ^ 7 := by
  unfold rawF16
  field_simp [hden]
  <;> ring

private theorem rawF16_at_x_one_parameter (s : ℚ) (hs : s ≠ 0) :
    s ^ 3 * rawF16 ((2 * s ^ 2 - 2 * s + 1) / s) s =
      -2 * (s - 1) ^ 9 := by
  unfold rawF16
  field_simp [hs]
  <;> ring

private theorem rawModelX_ne_zero {r s : ℚ}
    (hr : r ≠ 1) (hs : s ≠ 0) (hF : rawF16 r s = 0)
    (hD : rawChartDenominator r s ≠ 0) :
    rawModelX r s ≠ 0 := by
  intro hx
  unfold rawModelX at hx
  field_simp [hD] at hx
  have hprod : (r - s) * (s - 1) = 0 := by
    nlinarith [hx]
  rcases mul_eq_zero.mp hprod with hrs | hs1
  · have hrs' : r = s := sub_eq_zero.mp hrs
    rw [hrs'] at hF hr
    have hid := rawF16_on_diagonal s
    rw [hF] at hid
    have hp : (s - 1) ^ 5 = 0 := by
      have := (mul_eq_zero.mp (show s * (s - 1) ^ 5 = 0 by nlinarith [hid])).resolve_left hs
      exact this
    have hs1' : s - 1 = 0 :=
      (pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hp
    exact hr (by linarith)
  · have hs1' : s = 1 := by linarith
    rw [hs1'] at hF
    have hid := rawF16_at_s_one r
    rw [hF] at hid
    have hr1sub : r - 1 = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp (neg_eq_zero.mp hid.symm)
    exact hr (by linarith)

private theorem rawModelX_ne_neg_one {r s : ℚ}
    (hr : r ≠ 1) (hF : rawF16 r s = 0)
    (hD : rawChartDenominator r s ≠ 0) :
    rawModelX r s ≠ -1 := by
  intro hx
  unfold rawModelX at hx
  field_simp [hD] at hx
  have hrel : r * s - 2 * r + 1 = 0 := by
    unfold rawChartDenominator at hx
    linear_combination -hx
  have hden : 2 - s ≠ 0 := by
    intro hzero
    have hs2 : s = 2 := by linarith
    rw [hs2] at hrel
    linarith
  have hrFormula : r = 1 / (2 - s) := by
    field_simp [hden]
    linear_combination -hrel
  have hid := rawF16_at_x_neg_one_parameter s hden
  rw [← hrFormula, hF] at hid
  have hp : (s - 1) ^ 7 = 0 := by nlinarith [hid]
  have hs1sub : s - 1 = 0 :=
    (pow_eq_zero_iff (by norm_num : (7 : ℕ) ≠ 0)).mp hp
  apply hr
  nlinarith [hrel]

private theorem rawModelX_ne_one {r s : ℚ}
    (hr : r ≠ 1) (hs : s ≠ 0) (hF : rawF16 r s = 0)
    (hD : rawChartDenominator r s ≠ 0) :
    rawModelX r s ≠ 1 := by
  intro hx
  unfold rawModelX at hx
  field_simp [hD] at hx
  have hrel : r * s - 2 * s ^ 2 + 2 * s - 1 = 0 := by
    unfold rawChartDenominator at hx
    linear_combination -hx
  have hrFormula : r = (2 * s ^ 2 - 2 * s + 1) / s := by
    field_simp [hs]
    linear_combination hrel
  have hid := rawF16_at_x_one_parameter s hs
  rw [← hrFormula, hF] at hid
  have hp : (s - 1) ^ 9 = 0 := by nlinarith [hid]
  have hs1sub : s - 1 = 0 :=
    (pow_eq_zero_iff (by norm_num : (9 : ℕ) ≠ 0)).mp hp
  apply hr
  nlinarith [hrel]

/-- The genuine restated order-`16` seam: the nondegenerate affine Tate model
of `X₁(16)` has no rational point. -/
theorem no_X116Datum :
    ¬ ∃ b c : ℚ, TateOrder16Cyclic.X116Datum b c := by
  rintro ⟨b, c, hdatum⟩
  obtain ⟨r, s, hr, hs, hF⟩ := raw_point_of_X116Datum hdatum
  have hD := rawChartDenominator_ne_zero hr hF
  have hmodel := raw_to_optimized hF hD
  rcases optimized_x_cusp (rawModelX r s) (rawModelY r s) hmodel with hx | hx | hx
  · exact rawModelX_ne_neg_one hr hF hD hx
  · exact rawModelX_ne_zero hr hs hF hD hx
  · exact rawModelX_ne_one hr hs hF hD hx

end MazurProof.RationalPointsX116
