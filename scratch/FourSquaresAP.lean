import scratch.SquareStep014

set_option maxHeartbeats 5000000

namespace FourSquaresAP

private lemma centered_product_identity (x n : ℤ) :
    (x ^ 2 - 5 * n ^ 2) ^ 2 - (4 * n ^ 2) ^ 2 =
      (x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2) := by
  ring

private lemma sq_product_centered_of_four_ap (a b c d Δ : ℤ)
    (h1 : b ^ 2 = a ^ 2 + Δ)
    (h2 : c ^ 2 = a ^ 2 + 2 * Δ)
    (h3 : d ^ 2 = a ^ 2 + 3 * Δ) :
    (4 * a * b * c * d) ^ 2 =
      ((2 * a ^ 2 + 3 * Δ) ^ 2 - Δ ^ 2) *
        ((2 * a ^ 2 + 3 * Δ) ^ 2 - 9 * Δ ^ 2) := by
  rw [show (4 * a * b * c * d) ^ 2 = 16 * a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 by ring]
  rw [h1, h2, h3]
  ring

private lemma centered_P_pos_of_pos_step (a Δ : ℤ) (hΔ : 0 < Δ) :
    0 < (2 * a ^ 2 + 3 * Δ) ^ 2 - 5 * Δ ^ 2 := by
  have : (2 * a ^ 2 + 3 * Δ) ^ 2 - 5 * Δ ^ 2 =
      4 * (a ^ 4 + 3 * a ^ 2 * Δ + Δ ^ 2) := by
    ring
  rw [this]
  positivity

private lemma isCoprime_sq_sub_mul_of_coprime
    {x n : ℤ} (hcop : IsCoprime x n) (k : ℤ) :
    IsCoprime (x ^ 2 - k * n ^ 2) n := by
  have hx2n : IsCoprime (x ^ 2) n := hcop.pow_left
  have h := hx2n.add_mul_right_left (-(k * n))
  simpa [sub_eq_add_neg, pow_two, mul_assoc, mul_left_comm, mul_comm] using h

private lemma coprime_y_n_of_centered
    {x n y : ℤ} (hcop : IsCoprime x n)
    (hprod : y ^ 2 = (x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2)) :
    IsCoprime y n := by
  have h1 : IsCoprime (x ^ 2 - 1 * n ^ 2) n :=
    isCoprime_sq_sub_mul_of_coprime hcop 1
  have h9 : IsCoprime (x ^ 2 - 9 * n ^ 2) n :=
    isCoprime_sq_sub_mul_of_coprime hcop 9
  have hp : IsCoprime ((x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2)) n := by
    simpa using h1.mul_left h9
  have hy2 : IsCoprime (y ^ 2) n := by
    simpa [hprod] using hp
  exact (IsCoprime.pow_left_iff (x := y) (y := n) (m := 2) (by norm_num)).mp hy2

private lemma int_mod_three_cases (z : ℤ) :
    (∃ q : ℤ, z = 3 * q) ∨
      (∃ q : ℤ, z = 3 * q + 1) ∨
        (∃ q : ℤ, z = 3 * q - 1) := by
  have hm : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases hm with h | h | h
  · left; exact ⟨z / 3, by omega⟩
  · right; left; exact ⟨z / 3, by omega⟩
  · right; right; exact ⟨z / 3 + 1, by omega⟩

private lemma not_three_dvd_sq_add_sq_of_coprime
    {A D : ℤ} (hcop : IsCoprime A D) :
    ¬ (3 : ℤ) ∣ A ^ 2 + D ^ 2 := by
  intro h3
  rcases int_mod_three_cases A with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases int_mod_three_cases D with ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩
  · have h3A : (3 : ℤ) ∣ A := ⟨a, ha⟩
    have h3D : (3 : ℤ) ∣ D := ⟨d, hd⟩
    have h3gcd : (3 : ℤ) ∣ (Int.gcd A D : ℤ) := Int.dvd_coe_gcd h3A h3D
    rw [Int.isCoprime_iff_gcd_eq_one.mp hcop] at h3gcd
    norm_num at h3gcd
  all_goals
    rw [ha, hd] at h3
    rcases h3 with ⟨k, hk⟩
    ring_nf at hk
    omega

private lemma coprime_sq_sum_left (A D : ℤ) (hcop : IsCoprime A D) :
    IsCoprime (A ^ 2 + D ^ 2) A := by
  simpa [add_comm] using Int.isCoprime_of_sq_sum (r := A) (s := D) hcop.symm

private lemma coprime_sq_sum_right (A D : ℤ) (hcop : IsCoprime A D) :
    IsCoprime (A ^ 2 + D ^ 2) D := by
  simpa [add_comm] using Int.isCoprime_of_sq_sum (r := D) (s := A) hcop

private lemma coprime_sq_sum_four_left (A D : ℤ) (hcop : IsCoprime A D) :
    IsCoprime (A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) := by
  let F : ℤ := A ^ 2 + D ^ 2
  have hFA : IsCoprime F A := by
    dsimp [F]
    exact coprime_sq_sum_left A D hcop
  have hFA2 : IsCoprime F (A ^ 2) := hFA.pow_right
  have hF3 : IsCoprime F (3 : ℤ) := by
    exact ((Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (3 : ℤ)).coprime_iff_not_dvd.mpr
      (by simpa [F] using not_three_dvd_sq_add_sq_of_coprime hcop)
      ).symm
  have hF3A : IsCoprime F (3 * A ^ 2) := hF3.mul_right hFA2
  have hFG : IsCoprime F (3 * A ^ 2 + F * 1) := hF3A.add_mul_left_right 1
  dsimp [F] at hFG
  convert hFG using 1 <;> ring

private lemma coprime_sq_sum_four_right (A D : ℤ) (hcop : IsCoprime A D) :
    IsCoprime (A ^ 2 + D ^ 2) (A ^ 2 + 4 * D ^ 2) := by
  let F : ℤ := A ^ 2 + D ^ 2
  have hFD : IsCoprime F D := by
    dsimp [F]
    exact coprime_sq_sum_right A D hcop
  have hFD2 : IsCoprime F (D ^ 2) := hFD.pow_right
  have hF3 : IsCoprime F (3 : ℤ) := by
    exact ((Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (3 : ℤ)).coprime_iff_not_dvd.mpr
      (by simpa [F] using not_three_dvd_sq_add_sq_of_coprime hcop)
      ).symm
  have hF3D : IsCoprime F (3 * D ^ 2) := hF3.mul_right hFD2
  have hFG : IsCoprime F (3 * D ^ 2 + F * 1) := hF3D.add_mul_left_right 1
  dsimp [F] at hFG
  convert hFG using 1 <;> ring

private theorem primitive_centered_product_no_sol
    (x n y : ℤ)
    (hn : n ≠ 0)
    (hPpos : 0 < x ^ 2 - 5 * n ^ 2)
    (hcop : Int.gcd x n = 1)
    (hprim : Int.gcd y (4 * n ^ 2) = 1)
    (hprod : y ^ 2 = (x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2)) :
    False := by
  let P : ℤ := x ^ 2 - 5 * n ^ 2
  have htrip : PythagoreanTriple y (4 * n ^ 2) P := by
    unfold PythagoreanTriple
    dsimp [P]
    nlinarith [hprod, centered_product_identity x n]
  have hy_odd : y % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
    · have h2y : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero hy
      have h2leg : (2 : ℤ) ∣ 4 * n ^ 2 := by
        exact dvd_mul_of_dvd_left (by norm_num : (2 : ℤ) ∣ 4) (n ^ 2)
      have h2gcd : (2 : ℤ) ∣ (Int.gcd y (4 * n ^ 2) : ℤ) :=
        Int.dvd_coe_gcd h2y h2leg
      rw [hprim] at h2gcd
      norm_num at h2gcd
    · exact hy
  obtain ⟨u, v, hyuv, hleguv, hPuv, huv_gcd, huv_par, hu_nonneg⟩ :=
    htrip.coprime_classification' hprim hy_odd (by simpa [P] using hPpos)
  have hleg : 4 * n ^ 2 = 2 * u * v := hleguv
  have hprod_uv : 2 * n ^ 2 = u * v := by nlinarith
  have huv_cop : IsCoprime u v := Int.isCoprime_iff_gcd_eq_one.mpr huv_gcd
  rcases huv_par with hpar | hpar
  · rcases Int.dvd_of_emod_eq_zero hpar.1 with ⟨U, hU⟩
    have hUprod : n ^ 2 = U * v := by
      rw [hU] at hprod_uv
      nlinarith
    have hcopUv : IsCoprime U v := by
      apply IsCoprime.of_mul_left_right
      simpa [hU, mul_assoc] using huv_cop
    obtain ⟨A, hA | hA⟩ := Int.sq_of_isCoprime hcopUv hUprod.symm
    · have hcopvU : IsCoprime v U := hcopUv.symm
      have hUprod' : v * U = n ^ 2 := by
        rw [mul_comm]
        exact hUprod.symm
      obtain ⟨D, hD | hD⟩ := Int.sq_of_isCoprime hcopvU hUprod'
      · have hxprod :
            x ^ 2 = (A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) := by
          rw [hU, hA, hD] at hPuv
          dsimp [P] at hPuv
          nlinarith [hPuv]
        have hcopAD : IsCoprime A D := by
          have hADpow : IsCoprime (A ^ 2) (D ^ 2) := by
            simpa [hA, hD] using hcopUv
          exact (IsCoprime.pow_iff (x := A) (y := D)
            (m := 2) (n := 2) (by norm_num) (by norm_num)).mp hADpow
        have hfac_cop : IsCoprime (A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) :=
          coprime_sq_sum_four_left A D hcopAD
        obtain ⟨B, hB | hB⟩ := Int.sq_of_isCoprime hfac_cop hxprod.symm
        · have hxprod' : (4 * A ^ 2 + D ^ 2) * (A ^ 2 + D ^ 2) = x ^ 2 := by
            rw [mul_comm]
            exact hxprod.symm
          obtain ⟨C, hC | hC⟩ := Int.sq_of_isCoprime hfac_cop.symm hxprod'
          · have hADzero := no_sq_at_0_1_4 D B C A (by nlinarith) (by nlinarith)
            have hA0orD0 : A = 0 ∨ D = 0 := by
              exact mul_eq_zero.mp (by simpa [mul_comm] using hADzero)
            rcases hA0orD0 with hA0 | hD0
            · apply hn
              have hn2 : n ^ 2 = 0 := by
                rw [hUprod, hA, hA0]
                ring
              nlinarith [sq_nonneg n]
            · apply hn
              have hn2 : n ^ 2 = 0 := by
                rw [hUprod, hD, hD0]
                ring
              nlinarith [sq_nonneg n]
          · nlinarith [sq_nonneg C]
        · nlinarith [sq_nonneg B]
      · have hupos : 0 < u := by
          rw [hU, hA]
          by_cases hAz : A = 0
          · subst A
            apply False.elim
            have hn2 : n ^ 2 = 0 := by
              rw [hUprod, hA]
              ring
            apply hn
            nlinarith [sq_nonneg n]
          · nlinarith [sq_pos_of_ne_zero hAz]
        have hvpos : 0 < v := by nlinarith [sq_pos_of_ne_zero hn]
        rw [hD] at hvpos
        nlinarith [sq_nonneg D]
    · rw [hU, hA] at hu_nonneg
      have hAz : A = 0 := by nlinarith [sq_nonneg A]
      have hn2 : n ^ 2 = 0 := by
        rw [hUprod, hA, hAz]
        ring
      apply hn
      nlinarith [sq_nonneg n]
  · rcases Int.dvd_of_emod_eq_zero hpar.2 with ⟨V, hV⟩
    have hVprod : n ^ 2 = u * V := by
      rw [hV] at hprod_uv
      nlinarith
    have hcopuV : IsCoprime u V := by
      apply IsCoprime.of_mul_right_right
      simpa [hV, mul_assoc] using huv_cop
    obtain ⟨A, hA | hA⟩ := Int.sq_of_isCoprime hcopuV hVprod.symm
    · have hVprod' : V * u = n ^ 2 := by
        rw [mul_comm]
        exact hVprod.symm
      obtain ⟨D, hD | hD⟩ := Int.sq_of_isCoprime hcopuV.symm hVprod'
      · have hxprod :
            x ^ 2 = (A ^ 2 + D ^ 2) * (A ^ 2 + 4 * D ^ 2) := by
          rw [hV, hA, hD] at hPuv
          dsimp [P] at hPuv
          nlinarith [hPuv]
        have hcopAD : IsCoprime A D := by
          have hADpow : IsCoprime (A ^ 2) (D ^ 2) := by
            simpa [hA, hD] using hcopuV
          exact (IsCoprime.pow_iff (x := A) (y := D)
            (m := 2) (n := 2) (by norm_num) (by norm_num)).mp hADpow
        have hfac_cop : IsCoprime (A ^ 2 + D ^ 2) (A ^ 2 + 4 * D ^ 2) :=
          coprime_sq_sum_four_right A D hcopAD
        obtain ⟨B, hB | hB⟩ := Int.sq_of_isCoprime hfac_cop hxprod.symm
        · have hxprod' : (A ^ 2 + 4 * D ^ 2) * (A ^ 2 + D ^ 2) = x ^ 2 := by
            rw [mul_comm]
            exact hxprod.symm
          obtain ⟨C, hC | hC⟩ := Int.sq_of_isCoprime hfac_cop.symm hxprod'
          · have hADzero := no_sq_at_0_1_4 A B C D (by nlinarith) (by nlinarith)
            have hA0orD0 : A = 0 ∨ D = 0 := mul_eq_zero.mp hADzero
            rcases hA0orD0 with hA0 | hD0
            · apply hn
              have hn2 : n ^ 2 = 0 := by
                rw [hVprod, hA, hA0]
                ring
              nlinarith [sq_nonneg n]
            · apply hn
              have hn2 : n ^ 2 = 0 := by
                rw [hVprod, hD, hD0]
                ring
              nlinarith [sq_nonneg n]
          · nlinarith [sq_nonneg C]
        · nlinarith [sq_nonneg B]
      · have hupos : 0 < u := by
          rw [hA]
          by_cases hAz : A = 0
          · subst A
            apply False.elim
            have hn2 : n ^ 2 = 0 := by
              rw [hVprod, hA]
              ring
            apply hn
            nlinarith [sq_nonneg n]
          · nlinarith [sq_pos_of_ne_zero hAz]
        have hvpos : 0 < v := by nlinarith [sq_pos_of_ne_zero hn]
        rw [hV, hD] at hvpos
        nlinarith [sq_nonneg D]
    · rw [hA] at hu_nonneg
      have hAz : A = 0 := by nlinarith [sq_nonneg A]
      have hn2 : n ^ 2 = 0 := by
        rw [hVprod, hA, hAz]
        ring
      apply hn
      nlinarith [sq_nonneg n]

end FourSquaresAP
