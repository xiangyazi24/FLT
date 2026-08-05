import FLT.Assumptions.MazurProof.RationalPointsX135Descent
import FLT.Assumptions.MazurProof.XDelta19GoodIsogeny

/-!
# The rational-flex cubeclasses on the good level-nineteen model

For

`y² = x³ + (8x+76)²`,

the factors `y-(8x+76)` and `y+(8x+76)` have product `x³`.
After a two-adic integral normalization, their only possible common
prime is nineteen.  It follows that the first factor has one of the
three rational cubeclasses `1`, `19`, and `19²`.
-/

namespace MazurProof.XDelta19GoodDescent

open MazurProof.RationalPointsX135
open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny

noncomputable section

/-! ## Two-adic normalization -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A finite two-adic certificate for the even-numerator branch of the
good model. -/
private theorem even_good_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 + 1216 * A * B ^ 4 +
          5776 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  decide

/-- The finite two-adic certificate lifts to the required integer
divisibilities. -/
private theorem even_good_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 +
      1216 * A * B ^ 4 + 5776 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 8 * A * B - 76 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 8 * A * B + 76 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      64 * (A : ZMod 32) ^ 2 * B ^ 2 +
      1216 * (A : ZMod 32) * B ^ 4 + 5776 * (B : ZMod 32) ^ 6 := by
    have h' := congrArg (fun n : ℤ => (n : ZMod 32)) hmodel
    push_cast at h'
    exact h'
  have hA2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (A : ZMod 32) = 0 := by
    have hz : (A : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd A 2).mpr hA
    simpa [ZMod.castHom_apply] using hz
  have hB2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (B : ZMod 32) ≠ 0 := by
    intro hz
    apply hB
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp
    simpa [ZMod.castHom_apply] using hz
  have hc := even_good_model_mod_thirtyTwo (A : ZMod 32)
    (B : ZMod 32) (C : ZMod 32) hA2 hB2 h32
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C - 8 * A * B - 76 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 8 * A * B + 76 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Primitive integral flex coordinates in which the two descent factors
have cube product and can share only the prime nineteen. -/
theorem good_flex_integral_model {x y : ℚ}
    (h : OnGood x y) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (8 * x + 76) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 8 * M * D + 19 * D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((64 : ℤ) : ℚ) * x ^ 2 +
      ((1216 : ℤ) : ℚ) * x + (5776 : ℤ) := by
    unfold OnGood at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 64 1216 5776 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 8 * A * B - 76 * B ^ 3) *
          (C + 8 * A * B + 76 * B ^ 3) = A ^ 3 := by
    calc
      (C - 8 * A * B - 76 * B ^ 3) *
          (C + 8 * A * B + 76 * B ^ 3) =
          C ^ 2 - (8 * A * B + 76 * B ^ 3) ^ 2 := by ring
      _ = A ^ 3 := by linear_combination hmodel
  rcases A.even_or_odd with hAeven | hAodd
  · have hA2 : (2 : ℤ) ∣ A := hAeven.two_dvd
    have hcop2B : IsCoprime (2 : ℤ) B :=
      hcopI.of_isCoprime_of_dvd_left hA2
    have hBodd : Odd B := Int.isCoprime_two_left.mp hcop2B
    obtain ⟨hA4, hN8, hP8⟩ :=
      even_good_model_divisibility hA2 (by
        rw [← even_iff_two_dvd]
        exact Int.not_even_iff_odd.mpr hBodd) hmodel
    obtain ⟨M, hM⟩ := hA4
    obtain ⟨R, hR⟩ := hN8
    obtain ⟨S, hS⟩ := hP8
    have hcopMD : IsCoprime M B := by
      rw [hM] at hcopI
      exact hcopI.of_mul_left_right
    have hprod : R * S = M ^ 3 := by
      rw [hR, hS, hM] at hprodRaw
      ring_nf at hprodRaw ⊢
      omega
    have hlin : S = R + 8 * M * B + 19 * B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 8 * M * B + 19 * B ^ 3) := by
        calc
          8 * S = C + 8 * A * B + 76 * B ^ 3 := hS.symm
          _ = (C - 8 * A * B - 76 * B ^ 3) +
              8 * (8 * M * B + 19 * B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (8 * M * B + 19 * B ^ 3) := by rw [hR]
          _ = 8 * (R + 8 * M * B + 19 * B ^ 3) := by ring
      omega
    refine ⟨M, B, R, S, hBpos,
      Int.isCoprime_iff_gcd_eq_one.mp hcopMD, ?_, ?_, hprod, hlin⟩
    · rw [hx, hM]
      push_cast
      ring
    · rw [hx, hy, hM]
      push_cast
      field_simp [hBneQ]
      have hR' := hR
      rw [hM] at hR'
      have hR'' := congrArg (fun n : ℤ => (n : ℚ)) hR'
      push_cast at hR''
      linear_combination hR''
  · have hcopA2 : IsCoprime A (2 : ℤ) :=
      Int.isCoprime_two_right.mpr hAodd
    have hcopAD : IsCoprime A (2 * B) := hcopA2.mul_right hcopI
    refine ⟨A, 2 * B, C - 8 * A * B - 76 * B ^ 3,
      C + 8 * A * B + 76 * B ^ 3, by positivity,
      Int.isCoprime_iff_gcd_eq_one.mp hcopAD, ?_, ?_, hprodRaw, ?_⟩
    · rw [hx]
      push_cast
      field_simp [hBneQ]
      ring
    · rw [hx, hy]
      push_cast
      field_simp [hBneQ]
      ring
    · ring

/-! ## The three possible cubeclasses -/

/-- A prime common to both normalized descent factors must be nineteen. -/
private theorem flex_common_prime_eq_nineteen
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 8 * M * D + 19 * D ^ 3)
    {p : ℕ} (hp : p.Prime) (hpR : (p : ℤ) ∣ R)
    (hpS : (p : ℤ) ∣ S) :
    p = 19 := by
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpPow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpPow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS hpR
  have hpSum : (p : ℤ) ∣ 8 * M * D + 19 * D ^ 3 := by
    rw [hlin] at hpDiff
    have heq :
        (R + 8 * M * D + 19 * D ^ 3) - R =
          8 * M * D + 19 * D ^ 3 := by ring
    rwa [heq] at hpDiff
  have hpFirst : (p : ℤ) ∣ 8 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨8 * k * D, ?_⟩
    rw [hk]
    ring
  have hpTail : (p : ℤ) ∣ 19 * D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    rcases this with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    linear_combination hk
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hpD : ¬(p : ℤ) ∣ D := by
    intro hpD
    exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)
  rcases hpInt.dvd_mul.mp hpTail with hp19 | hpD3
  · have hp19Nat : p ∣ 19 := by exact_mod_cast hp19
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp hp19Nat with
      hp1 | hp19'
    · exact (hp.ne_one hp1).elim
    · exact hp19'
  · exact (hpD (hpInt.dvd_of_dvd_pow hpD3)).elim

/-- If nineteen is not a common factor, the two normalized descent
factors are coprime. -/
private theorem isCoprime_of_common_prime_eq_nineteen {R S : ℤ}
    (hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R →
      (p : ℤ) ∣ S → p = 19)
    (hnotBoth : ¬((19 : ℤ) ∣ R ∧ (19 : ℤ) ∣ S)) :
    IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hcop
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hp19 := hsupport hp hpR' hpS'
  subst p
  exact hnotBoth ⟨hpR', hpS'⟩

/-- The normalized first descent factor has cubeclass `1`, `19`, or
`19²`. -/
theorem flex_factor_cubeclass
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 8 * M * D + 19 * D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 ∨ R = 19 * q ^ 3 ∨ R = 361 * q ^ 3 := by
  have hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R →
      (p : ℤ) ∣ S → p = 19 :=
    fun {_p} hp hpR hpS =>
      flex_common_prime_eq_nineteen hcop hprod hlin hp hpR hpS
  by_cases h19R : (19 : ℤ) ∣ R
  · have h19Mpow : (19 : ℤ) ∣ M ^ 3 := by
      rw [← hprod]
      exact dvd_mul_of_dvd_left h19R S
    have h19M : (19 : ℤ) ∣ M :=
      Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19Mpow
    have h19S : (19 : ℤ) ∣ S := by
      rw [hlin]
      have hmid : (19 : ℤ) ∣ 8 * M * D := by
        rcases h19M with ⟨m, hm⟩
        refine ⟨8 * m * D, ?_⟩
        rw [hm]
        ring
      exact dvd_add (dvd_add h19R hmid) (dvd_mul_right 19 (D ^ 3))
    obtain ⟨R1, hR1⟩ := h19R
    obtain ⟨S1, hS1⟩ := h19S
    obtain ⟨M1, hM1⟩ := h19M
    have hprod1 : R1 * S1 = 19 * M1 ^ 3 := by
      rw [hR1, hS1, hM1] at hprod
      ring_nf at hprod ⊢
      omega
    have hlin1 : S1 = R1 + 8 * M1 * D + D ^ 3 := by
      rw [hR1, hS1, hM1] at hlin
      ring_nf at hlin ⊢
      omega
    have hnotBoth1 : ¬((19 : ℤ) ∣ R1 ∧ (19 : ℤ) ∣ S1) := by
      rintro ⟨h19R1, h19S1⟩
      obtain ⟨r, hr⟩ := h19R1
      obtain ⟨s, hs⟩ := h19S1
      have hM1cube : M1 ^ 3 = 19 * (r * s) := by
        rw [hr, hs] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have h19M1pow : (19 : ℤ) ∣ M1 ^ 3 := ⟨r * s, hM1cube⟩
      have h19M1 : (19 : ℤ) ∣ M1 :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19M1pow
      obtain ⟨m, hm⟩ := h19M1
      have hDcube : D ^ 3 = 19 * (s - r - 8 * m * D) := by
        rw [hr, hs, hm] at hlin1
        ring_nf at hlin1 ⊢
        omega
      have h19Dpow : (19 : ℤ) ∣ D ^ 3 :=
        ⟨s - r - 8 * m * D, hDcube⟩
      have h19D : (19 : ℤ) ∣ D :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19Dpow
      have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have hu : IsUnit (19 : ℤ) :=
        hcopI.isUnit_of_dvd'
          (show (19 : ℤ) ∣ M by exact ⟨M1, hM1⟩) h19D
      rw [Int.isUnit_iff_abs_eq] at hu
      norm_num at hu
    have hcop1 : IsCoprime R1 S1 :=
      isCoprime_of_common_prime_eq_nineteen
        (fun {_p} hp hpR hpS => hsupport hp
          (hR1 ▸ dvd_mul_of_dvd_right hpR 19)
          (hS1 ▸ dvd_mul_of_dvd_right hpS 19)) hnotBoth1
    by_cases h19R1 : (19 : ℤ) ∣ R1
    · obtain ⟨R2, hR2⟩ := h19R1
      have hprod2 : R2 * S1 = M1 ^ 3 := by
        rw [hR2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R2 S1 := by
        rw [hR2] at hcop1
        exact hcop1.of_mul_left_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2
          (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inr ?_)⟩
      rw [hR1, hR2, hq]
      ring
    · have h19S1 : (19 : ℤ) ∣ S1 := by
        have h19prod : (19 : ℤ) ∣ R1 * S1 := by
          rw [hprod1]
          exact dvd_mul_right 19 _
        have hor : (19 : ℤ) ∣ R1 ∨ (19 : ℤ) ∣ S1 :=
          (by norm_num : Prime (19 : ℤ)).dvd_mul.mp h19prod
        exact Or.resolve_left hor h19R1
      obtain ⟨S2, hS2⟩ := h19S1
      have hprod2 : R1 * S2 = M1 ^ 3 := by
        rw [hS2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R1 S2 := by
        rw [hS2] at hcop1
        exact hcop1.of_mul_right_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2
          (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inl ?_)⟩
      rw [hR1, hq]
  · have hcopRS : IsCoprime R S :=
      isCoprime_of_common_prime_eq_nineteen hsupport
        (fun h => h19R h.1)
    obtain ⟨q, hq⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd_left hcopRS
        (show Odd 3 by decide) hprod
    exact ⟨q, Or.inl hq⟩

/-- The rational flex function on the good model has exactly one of the
three candidate cubeclasses `1`, `19`, and `19²`. -/
theorem good_alpha_cubeclass {x y : ℚ} (h : OnGood x y) :
    ∃ r : ℚ,
      y - (8 * x + 76) = r ^ 3 ∨
      y - (8 * x + 76) = 19 * r ^ 3 ∨
      y - (8 * x + 76) = 361 * r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    good_flex_integral_model h
  obtain ⟨q, hq | hq | hq⟩ :=
    flex_factor_cubeclass hcop hprod hlin
  all_goals
    refine ⟨2 * (q : ℚ) / (D : ℚ), ?_⟩
  · left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; right
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring

/-! ## Cubes and translation by the visible flexes -/

/-- A nonzero cube value of the flex function constructs an explicit
preimage under the dual degree-three isogeny. -/
theorem exists_dualThreeIsogeny_preimage_of_alpha_cube
    {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hr : r ^ 3 = y - (8 * x + 76)) (hr0 : r ≠ 0) :
    ∃ Q : QuotientPoint,
      dualThreeIsogenyPoint Q =
        WeierstrassCurve.Affine.Point.some x y h := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hy : y = r ^ 3 + 8 * x + 76 := by
    linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 16 * x + 152) := by
    unfold OnGood at hcurve
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3 * x - 3 * r ^ 2 - 16 * r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r ^ 2 + 16 * r / 3 := by
      dsimp [d] at hd
      linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r ^ 3 = 0 := by
      linarith
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  let s : ℚ := 24 * r / d
  let t : ℚ := 9 * s * r + 24 * s + 36
  have hs : s ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) hr0) hd
  have hquotient : OnQuotient s t := by
    unfold OnQuotient
    dsimp only [t, s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 46656 * hrel
  have hxmap : dualThreeIsogenyX s = x := by
    unfold dualThreeIsogenyX
    dsimp only [s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination -46656 * hrel
  have hymap : dualThreeIsogenyY s t = y := by
    rw [hy]
    unfold dualThreeIsogenyY
    dsimp only [t, s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination
      10077696 * (-2 * r ^ 2 - 8 * r + x) * hrel
  have hquotientns :
      WeierstrassCurve.Affine.Nonsingular quotientCurve s t :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((quotientCurve_equation_iff s t).mpr hquotient)
  let Q : QuotientPoint :=
    WeierstrassCurve.Affine.Point.some s t hquotientns
  refine ⟨Q, ?_⟩
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero hquotientns hs]
  change WeierstrassCurve.Affine.Point.some
      (dualThreeIsogenyX s) (dualThreeIsogenyY s t) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxmap, hymap⟩

/-- Translation by the positive visible flex multiplies the flex
function by the stated rational cube factor. -/
theorem add_goodT_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x 0 y 76
    let X := WeierstrassCurve.Affine.addX goodCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY goodCurve x 0 y L
    Y - (8 * X + 76) =
      -23104 * (y - (8 * x + 76)) / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX goodCurve
  field_simp [hx]
  unfold OnGood at hcurve
  linear_combination -(x ^ 3) * (8 * x + y - 228) * hcurve

/-- Translation by the negative visible flex transforms the conjugate
factor by the stated rational cube factor. -/
theorem add_goodTNeg_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x 0 y (-76)
    let X := WeierstrassCurve.Affine.addX goodCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY goodCurve x 0 y L
    Y - (8 * X + 76) =
      -152 * (y + (8 * x + 76)) ^ 2 / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX goodCurve
  field_simp [hx]
  unfold OnGood at hcurve
  linear_combination -(x ^ 3) * (8 * x + y + 76) * hcurve

end

end MazurProof.XDelta19GoodDescent
