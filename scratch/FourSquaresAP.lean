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

private lemma sq_mod_four (z : ℤ) : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
  rcases Int.even_or_odd z with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk]
    ring_nf
    omega
  · right
    rw [hk]
    ring_nf
    omega

private lemma sq_mod_two (z : ℤ) : z ^ 2 % 2 = z % 2 := by
  rcases Int.even_or_odd z with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    ring_nf
    omega
  · rw [hk]
    ring_nf
    omega

private lemma four_sq_ap_step_dvd_four (a b c Δ : ℤ)
    (h1 : b ^ 2 = a ^ 2 + Δ)
    (h2 : c ^ 2 = a ^ 2 + 2 * Δ) : (4 : ℤ) ∣ Δ := by
  have ha := sq_mod_four a
  have hb := sq_mod_four b
  have hc := sq_mod_four c
  have hd : Δ % 4 = 0 ∨ Δ % 4 = 1 ∨ Δ % 4 = 2 ∨ Δ % 4 = 3 := by omega
  rcases hd with hd | hd | hd | hd
  · exact Int.dvd_of_emod_eq_zero hd
  all_goals
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
    all_goals
      have h1m := congrArg (fun z : ℤ => z % 4) h1
      have h2m := congrArg (fun z : ℤ => z % 4) h2
      omega

private lemma not_eight_dvd_four_mul_of_odd {m : ℤ} (hm : Odd m) :
    ¬ (8 : ℤ) ∣ 4 * m := by
  intro h8
  rcases h8 with ⟨k, hk⟩
  have h2m : (2 : ℤ) ∣ m := ⟨k, by omega⟩
  have hm2 : m % 2 = 1 := Int.odd_iff.mp hm
  have h2m_mod : m % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h2m
  omega

private lemma gcd_y_four_n_sq_eq_one_of_odd_of_coprime
    {y n : ℤ} (hyodd : Odd y) (hcop : IsCoprime y n) :
    Int.gcd y (4 * n ^ 2) = 1 := by
  have hy_not_two : ¬ (2 : ℤ) ∣ y := by
    intro h2
    have h2m : y % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h2
    have hym : y % 2 = 1 := Int.odd_iff.mp hyodd
    omega
  have hcop2y : IsCoprime (2 : ℤ) y :=
    (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (2 : ℤ)).coprime_iff_not_dvd.mpr
      hy_not_two
  have hcop_y4 : IsCoprime y (4 : ℤ) := by
    have hpow : IsCoprime y ((2 : ℤ) ^ 2) := hcop2y.symm.pow_right
    simpa using hpow
  have hcop_yn2 : IsCoprime y (n ^ 2) := hcop.pow_right
  exact Int.isCoprime_iff_gcd_eq_one.mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcop_y4.mul_right hcop_yn2)

private lemma even_of_mod_two_zero {z : ℤ} (hz : z % 2 = 0) : (2 : ℤ) ∣ z :=
  Int.dvd_of_emod_eq_zero hz

private lemma odd_of_mod_two_one {z : ℤ} (hz : z % 2 = 1) : Odd z :=
  Int.odd_iff.mpr hz

private theorem no_four_sq_AP_pos
    (a b c d Δ : ℤ) (hΔ : 0 < Δ)
    (h1 : b ^ 2 = a ^ 2 + Δ)
    (h2 : c ^ 2 = a ^ 2 + 2 * Δ)
    (h3 : d ^ 2 = a ^ 2 + 3 * Δ) : False := by
  let AP : ℕ → Prop := fun N =>
    ∀ a b c d Δ : ℤ, Δ.natAbs = N → 0 < Δ →
      b ^ 2 = a ^ 2 + Δ →
      c ^ 2 = a ^ 2 + 2 * Δ →
      d ^ 2 = a ^ 2 + 3 * Δ → False
  have hmain : ∀ N, AP N := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro a b c d Δ hN hΔ h1 h2 h3
      have hΔ4 : (4 : ℤ) ∣ Δ := four_sq_ap_step_dvd_four a b c Δ h1 h2
      by_cases hall_even :
          (2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b ∧ (2 : ℤ) ∣ c ∧ (2 : ℤ) ∣ d
      · rcases hall_even with ⟨⟨a0, ha0⟩, ⟨b0, hb0⟩, ⟨c0, hc0⟩, ⟨d0, hd0⟩⟩
        rcases hΔ4 with ⟨Δ0, hΔ0⟩
        have hΔ0pos : 0 < Δ0 := by nlinarith
        have hΔ0_lt : Δ0.natAbs < N := by
          rw [← hN, hΔ0]
          have h4Δ0_nonneg : 0 ≤ 4 * Δ0 := by nlinarith
          have hltZ : (Δ0.natAbs : ℤ) < ((4 * Δ0).natAbs : ℤ) := by
            rw [Int.natCast_natAbs, Int.natCast_natAbs]
            rw [abs_of_nonneg hΔ0pos.le, abs_of_nonneg h4Δ0_nonneg]
            nlinarith
          exact_mod_cast hltZ
        have h1' : b0 ^ 2 = a0 ^ 2 + Δ0 := by
          rw [ha0, hb0, hΔ0] at h1
          nlinarith
        have h2' : c0 ^ 2 = a0 ^ 2 + 2 * Δ0 := by
          rw [ha0, hc0, hΔ0] at h2
          nlinarith
        have h3' : d0 ^ 2 = a0 ^ 2 + 3 * Δ0 := by
          rw [ha0, hd0, hΔ0] at h3
          nlinarith
        exact ih Δ0.natAbs hΔ0_lt a0 b0 c0 d0 Δ0 rfl hΔ0pos h1' h2' h3'
      · have hΔ2 : Δ % 2 = 0 := by
          rcases hΔ4 with ⟨k, hk⟩
          rw [hk]
          omega
        have ha2_cases := Int.emod_two_eq_zero_or_one a
        have hb2_cases := Int.emod_two_eq_zero_or_one b
        have hc2_cases := Int.emod_two_eq_zero_or_one c
        have hd2_cases := Int.emod_two_eq_zero_or_one d
        have ha_sq2 := sq_mod_two a
        have hb_sq2 := sq_mod_two b
        have hc_sq2 := sq_mod_two c
        have hd_sq2 := sq_mod_two d
        have haodd : Odd a := by
          rcases ha2_cases with ha0 | ha1
          · have hb0 : b % 2 = 0 := by
              rcases hb2_cases with hb0 | hb1
              · exact hb0
              · have h1m := congrArg (fun z : ℤ => z % 2) h1
                omega
            have hc0 : c % 2 = 0 := by
              rcases hc2_cases with hc0 | hc1
              · exact hc0
              · have h2m := congrArg (fun z : ℤ => z % 2) h2
                omega
            have hd0 : d % 2 = 0 := by
              rcases hd2_cases with hd0 | hd1
              · exact hd0
              · have h3m := congrArg (fun z : ℤ => z % 2) h3
                omega
            exact False.elim (hall_even
              ⟨even_of_mod_two_zero ha0, even_of_mod_two_zero hb0,
                even_of_mod_two_zero hc0, even_of_mod_two_zero hd0⟩)
          · exact odd_of_mod_two_one ha1
        have ha2 : a % 2 = 1 := Int.odd_iff.mp haodd
        have hbodd : Odd b := by
          rcases hb2_cases with hb0 | hb1
          · have h1m := congrArg (fun z : ℤ => z % 2) h1
            omega
          · exact odd_of_mod_two_one hb1
        have hcodd : Odd c := by
          rcases hc2_cases with hc0 | hc1
          · have h2m := congrArg (fun z : ℤ => z % 2) h2
            omega
          · exact odd_of_mod_two_one hc1
        have hdodd : Odd d := by
          rcases hd2_cases with hd0 | hd1
          · have h3m := congrArg (fun z : ℤ => z % 2) h3
            omega
          · exact odd_of_mod_two_one hd1
        let X : ℤ := 2 * a ^ 2 + 3 * Δ
        let Y : ℤ := 4 * a * b * c * d
        let gN : ℕ := Int.gcd X Δ
        let g : ℤ := gN
        have hprod0 : Y ^ 2 = (X ^ 2 - Δ ^ 2) * (X ^ 2 - 9 * Δ ^ 2) := by
          dsimp [X, Y]
          exact sq_product_centered_of_four_ap a b c d Δ h1 h2 h3
        have hgposN : 0 < gN := by
          dsimp [gN]
          exact (Int.gcd_pos_iff (a := X) (b := Δ)).mpr (Or.inr (ne_of_gt hΔ))
        have hgpos : 0 < g := by
          dsimp [g]
          exact_mod_cast hgposN
        have hg_ne : g ≠ 0 := ne_of_gt hgpos
        have hgX : g ∣ X := by
          dsimp [g, gN]
          exact Int.gcd_dvd_left X Δ
        have hgΔ : g ∣ Δ := by
          dsimp [g, gN]
          exact Int.gcd_dvd_right X Δ
        have hX_even : (2 : ℤ) ∣ X := by
          dsimp [X]
          exact dvd_add (dvd_mul_of_dvd_left (by norm_num : (2 : ℤ) ∣ 2) (a ^ 2))
            (dvd_mul_of_dvd_right (even_of_mod_two_zero hΔ2) 3)
        have hg_even : (2 : ℤ) ∣ g := by
          dsimp [g, gN]
          exact Int.dvd_coe_gcd hX_even (even_of_mod_two_zero hΔ2)
        have hg2Y : g ^ 2 ∣ Y := by
          have hg2_f1 : g ^ 2 ∣ X ^ 2 - Δ ^ 2 := by
            rcases hgX with ⟨X0, hX0⟩
            rcases hgΔ with ⟨D0, hD0⟩
            refine ⟨X0 ^ 2 - D0 ^ 2, ?_⟩
            rw [hX0, hD0]
            ring
          have hg2_f9 : g ^ 2 ∣ X ^ 2 - 9 * Δ ^ 2 := by
            rcases hgX with ⟨X0, hX0⟩
            rcases hgΔ with ⟨D0, hD0⟩
            refine ⟨X0 ^ 2 - 9 * D0 ^ 2, ?_⟩
            rw [hX0, hD0]
            ring
          have hg4Y2 : (g ^ 2) ^ 2 ∣ Y ^ 2 := by
            rw [hprod0]
            simpa [pow_two] using mul_dvd_mul hg2_f1 hg2_f9
          exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hg4Y2
        let x : ℤ := X / g
        let n : ℤ := Δ / g
        let y : ℤ := Y / g ^ 2
        have hXeq : X = x * g := by
          dsimp [x]
          exact (Int.ediv_mul_cancel hgX).symm
        have hΔeq : Δ = n * g := by
          dsimp [n]
          exact (Int.ediv_mul_cancel hgΔ).symm
        have hYeq : Y = y * g ^ 2 := by
          dsimp [y]
          exact (Int.ediv_mul_cancel hg2Y).symm
        have hn_ne : n ≠ 0 := by
          intro hn0
          apply ne_of_gt hΔ
          rw [hΔeq, hn0]
          ring
        have hcop_g : Int.gcd x n = 1 := by
          dsimp [x, n, g, gN]
          exact Int.gcd_ediv_gcd_ediv_gcd hgposN
        have hprod : y ^ 2 = (x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2) := by
          have hmul :
              y ^ 2 * g ^ 4 =
                ((x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2)) * g ^ 4 := by
            calc
              y ^ 2 * g ^ 4 = (y * g ^ 2) ^ 2 := by ring
              _ = Y ^ 2 := by rw [← hYeq]
              _ = (X ^ 2 - Δ ^ 2) * (X ^ 2 - 9 * Δ ^ 2) := hprod0
              _ = ((x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2)) * g ^ 4 := by
                rw [hXeq, hΔeq]
                ring
          have hmul' :
              g ^ 4 * y ^ 2 =
                g ^ 4 * ((x ^ 2 - n ^ 2) * (x ^ 2 - 9 * n ^ 2)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact (mul_right_inj' (pow_ne_zero 4 hg_ne)).mp hmul'
        have hPpos : 0 < x ^ 2 - 5 * n ^ 2 := by
          have hP0 : 0 < X ^ 2 - 5 * Δ ^ 2 := by
            dsimp [X]
            exact centered_P_pos_of_pos_step a Δ hΔ
          have hPmul : X ^ 2 - 5 * Δ ^ 2 = (x ^ 2 - 5 * n ^ 2) * g ^ 2 := by
            rw [hXeq, hΔeq]
            ring
          have hg2pos : 0 < g ^ 2 := sq_pos_of_ne_zero hg_ne
          rw [hPmul] at hP0
          nlinarith
        have hyodd : Odd y := by
          by_contra hy_not
          have hyeven : (2 : ℤ) ∣ y := by
            rcases Int.not_odd_iff_even.mp hy_not with ⟨yy, hyy⟩
            exact ⟨yy, by rw [hyy]; ring⟩
          have h8Y : (8 : ℤ) ∣ Y := by
            rcases hyeven with ⟨yy, hyy⟩
            rcases hg_even with ⟨gg, hgg⟩
            refine ⟨yy * gg ^ 2, ?_⟩
            rw [hYeq, hyy, hgg]
            ring
          have habcd_odd : Odd (a * b * c * d) :=
            (((haodd.mul hbodd).mul hcodd).mul hdodd)
          exact not_eight_dvd_four_mul_of_odd habcd_odd (by simpa [Y, mul_assoc] using h8Y)
        have hcopyn : IsCoprime y n := by
          exact coprime_y_n_of_centered (Int.isCoprime_iff_gcd_eq_one.mpr hcop_g) hprod
        have hprim : Int.gcd y (4 * n ^ 2) = 1 :=
          gcd_y_four_n_sq_eq_one_of_odd_of_coprime hyodd hcopyn
        exact primitive_centered_product_no_sol x n y hn_ne hPpos hcop_g hprim hprod
  exact hmain Δ.natAbs a b c d Δ rfl hΔ h1 h2 h3

theorem no_four_sq_AP (a b c d Δ : ℤ)
    (h1 : b ^ 2 = a ^ 2 + Δ)
    (h2 : c ^ 2 = a ^ 2 + 2 * Δ)
    (h3 : d ^ 2 = a ^ 2 + 3 * Δ) : Δ = 0 := by
  rcases lt_trichotomy Δ 0 with hneg | hzero | hpos
  · exfalso
    have h1' : c ^ 2 = d ^ 2 + (-Δ) := by nlinarith
    have h2' : b ^ 2 = d ^ 2 + 2 * (-Δ) := by nlinarith
    have h3' : a ^ 2 = d ^ 2 + 3 * (-Δ) := by nlinarith
    exact no_four_sq_AP_pos d c b a (-Δ) (by linarith) h1' h2' h3'
  · exact hzero
  · exact False.elim (no_four_sq_AP_pos a b c d Δ hpos h1 h2 h3)

end FourSquaresAP
