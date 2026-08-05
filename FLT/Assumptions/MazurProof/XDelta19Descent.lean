import FLT.Assumptions.MazurProof.RationalPointsX135Descent
import FLT.Assumptions.MazurProof.XDelta19Model

/-!
# A rational-flex descent on the level-nineteen quotient

On the short model

`y² = x³ + (2x+4)²`,

the two factors `y-(2x+4)` and `y+(2x+4)` have product `x³`.
After putting a rational point in primitive integral coordinates, an exact
two-adic normalization makes these factors coprime.  Consequently the first
factor is itself a rational cube.

This is the elementary descent input for the dual degree-three isogeny.
-/

namespace MazurProof.XDelta19Descent

open MazurProof.RationalPointsX135
open MazurProof.XDelta19Model

noncomputable section

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A finite two-adic certificate for the even-numerator branch of the
integral short model. -/
private theorem even_short_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 4 * A ^ 2 * B ^ 2 + 16 * A * B ^ 4 +
          16 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  decide

/-- The finite certificate lifts to the required integer divisibilities. -/
private theorem even_short_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 4 * A ^ 2 * B ^ 2 +
      16 * A * B ^ 4 + 16 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 2 * A * B - 4 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 2 * A * B + 4 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      4 * (A : ZMod 32) ^ 2 * B ^ 2 + 16 * (A : ZMod 32) * B ^ 4 +
        16 * (B : ZMod 32) ^ 6 := by
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
  have hc := even_short_model_mod_thirtyTwo (A : ZMod 32)
    (B : ZMod 32) (C : ZMod 32) hA2 hB2 h32
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C - 2 * A * B - 4 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 2 * A * B + 4 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Primitive integral flex coordinates in which the two descent factors are
coprime and have cube product. -/
theorem short_flex_integral_model {x y : ℚ}
    (h : OnShort x y) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (2 * x + 4) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 2 * M * D + D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((4 : ℤ) : ℚ) * x ^ 2 +
      ((16 : ℤ) : ℚ) * x + (16 : ℤ) := by
    unfold OnShort at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 4 16 16 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 2 * A * B - 4 * B ^ 3) *
          (C + 2 * A * B + 4 * B ^ 3) = A ^ 3 := by
    calc
      (C - 2 * A * B - 4 * B ^ 3) *
          (C + 2 * A * B + 4 * B ^ 3) =
          C ^ 2 - (2 * A * B + 4 * B ^ 3) ^ 2 := by ring
      _ = A ^ 3 := by linear_combination hmodel
  rcases A.even_or_odd with hAeven | hAodd
  · have hA2 : (2 : ℤ) ∣ A := hAeven.two_dvd
    have hcop2B : IsCoprime (2 : ℤ) B :=
      hcopI.of_isCoprime_of_dvd_left hA2
    have hBodd : Odd B := Int.isCoprime_two_left.mp hcop2B
    obtain ⟨hA4, hN8, hP8⟩ :=
      even_short_model_divisibility hA2 (by
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
    have hlin : S = R + 2 * M * B + B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 2 * M * B + B ^ 3) := by
        calc
          8 * S = C + 2 * A * B + 4 * B ^ 3 := hS.symm
          _ = (C - 2 * A * B - 4 * B ^ 3) +
              8 * (2 * M * B + B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (2 * M * B + B ^ 3) := by rw [hR]
          _ = 8 * (R + 2 * M * B + B ^ 3) := by ring
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
    refine ⟨A, 2 * B, C - 2 * A * B - 4 * B ^ 3,
      C + 2 * A * B + 4 * B ^ 3, by positivity,
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

/-- No prime can divide both normalized descent factors. -/
private theorem flex_factors_isCoprime
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 2 * M * D + D ^ 3) :
    IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpMpow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR' S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpMpow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS' hpR'
  have hpSum : (p : ℤ) ∣ 2 * M * D + D ^ 3 := by
    rw [hlin] at hpDiff
    have hdiff :
        (R + 2 * M * D + D ^ 3) - R = 2 * M * D + D ^ 3 := by ring
    rwa [hdiff] at hpDiff
  have hpFirst : (p : ℤ) ∣ 2 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨2 * k * D, ?_⟩
    rw [hk]
    ring
  have hpDpow : (p : ℤ) ∣ D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    have hdiff :
        (2 * M * D + D ^ 3) - 2 * M * D = D ^ 3 := by ring
    rwa [hdiff] at this
  have hpD : (p : ℤ) ∣ D := hpInt.dvd_of_dvd_pow hpDpow
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)

/-- The normalized first descent factor is an integral cube. -/
theorem flex_factor_is_cube
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 2 * M * D + D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 := by
  have hcopRS : IsCoprime R S :=
    flex_factors_isCoprime hcop hprod hlin
  exact Int.eq_pow_of_mul_eq_pow_odd_left hcopRS
    (show Odd 3 by decide) hprod

/-- The first rational flex factor on the short model is always a rational
cube. -/
theorem short_alpha_is_cube {x y : ℚ} (h : OnShort x y) :
    ∃ r : ℚ, y - (2 * x + 4) = r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    short_flex_integral_model h
  obtain ⟨q, hq⟩ := flex_factor_is_cube hcop hprod hlin
  refine ⟨2 * (q : ℚ) / (D : ℚ), ?_⟩
  rw [halpha, hq]
  push_cast
  field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
  ring

/-- A nonzero cube value of the flex descent function constructs an explicit
preimage under the dual degree-three isogeny. -/
theorem exists_dualThreeIsogeny_preimage_of_alpha_cube
    {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular shortCurve x y)
    (hr : r ^ 3 = y - (2 * x + 4)) (hr0 : r ≠ 0) :
    ∃ Q : DualPoint,
      dualThreeIsogenyPoint Q =
        WeierstrassCurve.Affine.Point.some x y h := by
  have hcurve : OnShort x y := (shortCurve_equation_iff x y).mp h.1
  have hy : y = r ^ 3 + 2 * x + 4 := by
    linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 4 * x + 8) := by
    unfold OnShort at hcurve
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3 * x - 3 * r ^ 2 - 4 * r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r ^ 2 + 4 * r / 3 := by
      dsimp [d] at hd
      linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r ^ 3 = 0 := by
      linarith
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  let s : ℚ := 456 * r / d
  let t : ℚ := 9 * s * r + 6 * s + 684
  have hs : s ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hr0) hd
  have hdual : OnDual s t := by
    unfold OnDual
    dsimp only [t, s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 16842816 * hrel
  have hxmap : dualThreeIsogenyX s = x := by
    unfold dualThreeIsogenyX
    dsimp only [s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination -16842816 * hrel
  have hymap : dualThreeIsogenyY s t = y := by
    rw [hy]
    unfold dualThreeIsogenyY
    dsimp only [t, s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination
      69122916864 * (-2 * r ^ 2 + x - 2 * r) * hrel
  have hdualns :
      WeierstrassCurve.Affine.Nonsingular dualCurve s t :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((dualCurve_equation_iff s t).mpr hdual)
  let Q : DualPoint :=
    WeierstrassCurve.Affine.Point.some s t hdualns
  refine ⟨Q, ?_⟩
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns hs]
  change WeierstrassCurve.Affine.Point.some
      (dualThreeIsogenyX s) (dualThreeIsogenyY s t) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxmap, hymap⟩

/-- The dual degree-three isogeny is surjective on rational points of the
short model. -/
theorem dualThreeIsogenyPoint_surjective (P : ShortPoint) :
    ∃ Q : DualPoint, dualThreeIsogenyPoint Q = P := by
  cases P with
  | zero =>
      exact ⟨0, dualThreeIsogenyPoint_zero⟩
  | some x y h =>
      have hcurve : OnShort x y := (shortCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hySq : y ^ 2 = (4 : ℚ) ^ 2 := by
          rw [hx] at hcurve
          norm_num [OnShort] at hcurve ⊢
          exact hcurve
        rcases eq_or_eq_neg_of_sq_eq_sq y 4 hySq with hy | hy
        · have hdual : OnDual 228 2052 := by
            norm_num [OnDual]
          have hdualns :
              WeierstrassCurve.Affine.Nonsingular dualCurve 228 2052 :=
            WeierstrassCurve.Affine.equation_iff_nonsingular.mp
              ((dualCurve_equation_iff 228 2052).mpr hdual)
          let Q : DualPoint :=
            WeierstrassCurve.Affine.Point.some 228 2052 hdualns
          refine ⟨Q, ?_⟩
          rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns (by norm_num)]
          change WeierstrassCurve.Affine.Point.some
              (dualThreeIsogenyX 228) (dualThreeIsogenyY 228 2052) _ =
            WeierstrassCurve.Affine.Point.some x y h
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor
          · norm_num [dualThreeIsogenyX, hx]
          · norm_num [dualThreeIsogenyY, hy]
        · have hdual : OnDual 228 (-2052) := by
            norm_num [OnDual]
          have hdualns :
              WeierstrassCurve.Affine.Nonsingular dualCurve 228 (-2052) :=
            WeierstrassCurve.Affine.equation_iff_nonsingular.mp
              ((dualCurve_equation_iff 228 (-2052)).mpr hdual)
          let Q : DualPoint :=
            WeierstrassCurve.Affine.Point.some 228 (-2052) hdualns
          refine ⟨Q, ?_⟩
          rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns (by norm_num)]
          change WeierstrassCurve.Affine.Point.some
              (dualThreeIsogenyX 228) (dualThreeIsogenyY 228 (-2052)) _ =
            WeierstrassCurve.Affine.Point.some x y h
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor
          · norm_num [dualThreeIsogenyX, hx]
          · norm_num [dualThreeIsogenyY, hy]
      · obtain ⟨r, hr⟩ := short_alpha_is_cube hcurve
        have hr0 : r ≠ 0 := by
          intro hr0
          rw [hr0] at hr
          norm_num at hr
          apply hx
          have hx3 : x ^ 3 = 0 := by
            calc
              x ^ 3 = y ^ 2 - (2 * x + 4) ^ 2 := by
                unfold OnShort at hcurve
                linarith
              _ = (y - (2 * x + 4)) * (y + (2 * x + 4)) := by ring
              _ = 0 := by rw [hr]; ring
          exact eq_zero_of_pow_eq_zero hx3
        exact exists_dualThreeIsogeny_preimage_of_alpha_cube
          h hr.symm hr0

end

end MazurProof.XDelta19Descent
