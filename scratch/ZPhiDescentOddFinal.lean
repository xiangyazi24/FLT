import Mathlib

set_option maxHeartbeats 800000

private theorem right5_fourth_power_split_of_roots_product
    (x y m γ β : ℤ)
    (hx : x = γ ^ 2)
    (hy : y = β ^ 2)
    (hcop : IsCoprime γ β)
    (hprod : γ * β = m ^ 2) :
    ∃ c d : ℤ,
      x = c ^ 4 ∧
      y = d ^ 4 ∧
      (c * d) ^ 2 = m ^ 2 := by
  have hprod_swap : β * γ = m ^ 2 := by nlinarith
  obtain ⟨c, hc | hc⟩ := Int.sq_of_isCoprime hcop hprod
  · obtain ⟨d, hd | hd⟩ := Int.sq_of_isCoprime hcop.symm hprod_swap
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;> nlinarith
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;>
        nlinarith [sq_nonneg c, sq_nonneg d, sq_nonneg m, sq_nonneg (c * d)]
  · obtain ⟨d, hd | hd⟩ := Int.sq_of_isCoprime hcop.symm hprod_swap
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;>
        nlinarith [sq_nonneg c, sq_nonneg d, sq_nonneg m, sq_nonneg (c * d)]
    · refine ⟨c, d, ?_, ?_, ?_⟩ <;> nlinarith

private theorem right5_fourth_power_split_without_abs
    (x y m : ℤ)
    (hxpos : 0 < x)
    (hypos : 0 < y)
    (hcop : IsCoprime x y)
    (hmul_sq : x * y = (m ^ 2) ^ 2) :
    ∃ c d : ℤ,
      x = c ^ 4 ∧
      y = d ^ 4 ∧
      (c * d) ^ 2 = m ^ 2 := by
  obtain ⟨α, hα | hα⟩ := Int.sq_of_isCoprime hcop hmul_sq
  · obtain ⟨β, hβ | hβ⟩ := Int.sq_of_isCoprime hcop.symm (show y * x = (m ^ 2) ^ 2 by linarith)
    · have hcop_αβ : IsCoprime α β := by
        rwa [hα, hβ, IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)] at hcop
      have hprod_sq : (α * β) ^ 2 = (m ^ 2) ^ 2 := by nlinarith
      have hm_sq_pos : 0 < m ^ 2 := by nlinarith [mul_pos hxpos hypos]
      by_cases hsign : 0 ≤ α * β
      · have hzero : (α * β - m ^ 2) * (α * β + m ^ 2) = 0 := by nlinarith
        have hleft : α * β - m ^ 2 = 0 := by
          rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with h | h
          · exact h
          · nlinarith
        exact right5_fourth_power_split_of_roots_product x y m α β hα hβ hcop_αβ (by linarith)
      · have hlt : α * β < 0 := by omega
        have hsign' : 0 ≤ (-α) * β := by nlinarith
        have hzero : ((-α) * β - m ^ 2) * ((-α) * β + m ^ 2) = 0 := by nlinarith
        have hleft : (-α) * β - m ^ 2 = 0 := by
          rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with h | h
          · exact h
          · nlinarith
        have hcop_negαβ : IsCoprime (-α) β := by
          rcases hcop_αβ with ⟨u, v, huv⟩
          refine ⟨-u, v, ?_⟩
          nlinarith
        exact right5_fourth_power_split_of_roots_product x y m (-α) β (by nlinarith) hβ hcop_negαβ (by linarith)
    · nlinarith [sq_nonneg β]
  · nlinarith [sq_nonneg α]

private theorem right5_fourth_power_split
    (p r m : ℤ)
    (hleft_pos : 0 < p - r)
    (hright_pos : 0 < p + r)
    (hcop : IsCoprime (p - r) (p + r))
    (htriple : p ^ 2 = m ^ 4 + r ^ 2) :
    ∃ c d : ℤ,
      p - r = c ^ 4 ∧
      p + r = d ^ 4 ∧
      (c * d) ^ 2 = m ^ 2 := by
  exact right5_fourth_power_split_without_abs (p - r) (p + r) m hleft_pos hright_pos hcop (by nlinarith)

private theorem right5_descent_tail_from_fourth_split
    (p q _t m n r c d : ℤ)
    (hc : 2 ≤ c)
    (_hd : 1 ≤ d)
    (_hn : 1 ≤ n)
    (hc_lt_q : c < q)
    (_hq_nonneg : 0 ≤ q)
    (hcop_dc : Int.gcd d c = 1)
    (hpc : p - r = c ^ 4)
    (hpd : p + r = d ^ 4)
    (hm : m = c * d)
    (hr : 2 * r = n ^ 2 - m ^ 2) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  have hn_eq : n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 := by
    have hdiff : 2 * r = d ^ 4 - c ^ 4 := by nlinarith [hpc, hpd]
    have hm_sq : m ^ 2 = d ^ 2 * c ^ 2 := by
      rw [hm]
      ring
    nlinarith [hdiff, hm_sq, hr]
  refine ⟨d, c, n, hc, hcop_dc, ?_, ?_⟩
  · nlinarith
  · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) hc_lt_q

/-- Left Pellian factor. -/
private def zphiA (p q t : ℤ) : ℤ :=
  2 * p ^ 2 + q ^ 2 - 2 * t

/-- Right Pellian factor. -/
private def zphiB (p q t : ℤ) : ℤ :=
  2 * p ^ 2 + q ^ 2 + 2 * t

/-- Pellian product identity. -/
private lemma zphi_AB_eq_5q4 (p q t : ℤ)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    zphiA p q t * zphiB p q t = 5 * q ^ 4 := by
  dsimp [zphiA, zphiB]
  nlinarith

/-- Sum of the two Pellian factors. -/
private lemma zphi_A_add_B (p q t : ℤ) :
    zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2) := by
  dsimp [zphiA, zphiB]
  ring

/-- Difference of the two Pellian factors. -/
private lemma zphi_B_sub_A (p q t : ℤ) :
    zphiB p q t - zphiA p q t = 4 * t := by
  dsimp [zphiA, zphiB]
  ring

/-- Algebraic coefficient comparison in the branch `A = 5m^4`, `B = n^4`. -/
private lemma coeff_identity_left5
    (p q t m n : ℤ)
    (hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hqmn : q = m * n)
    (hA : zphiA p q t = 5 * m ^ 4)
    (hB : zphiB p q t = n ^ 4) :
    4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4 := by
  have hsum' : 5 * m ^ 4 + n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
    calc
      5 * m ^ 4 + n ^ 4 = zphiA p q t + zphiB p q t := by
        rw [hA, hB]
      _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
      _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
  nlinarith

/-- Algebraic coefficient comparison in the branch `A = m^4`, `B = 5n^4`. -/
private lemma coeff_identity_right5
    (p q t m n : ℤ)
    (hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hqmn : q = m * n)
    (hA : zphiA p q t = m ^ 4)
    (hB : zphiB p q t = 5 * n ^ 4) :
    4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4 := by
  have hsum' : m ^ 4 + 5 * n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
    calc
      m ^ 4 + 5 * n ^ 4 = zphiA p q t + zphiB p q t := by
        rw [hA, hB]
      _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
      _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
  nlinarith


/-- Symmetric descent package for the branch `A=m^4`, `B=5n^4`. -/
private theorem pythagorean_square_leg_self_descent_right5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  have hx_even : (2 : ℤ) ∣ m ^ 2 - n ^ 2 := by
    have hx_sq_dvd : (2 : ℤ) ∣ (m ^ 2 - n ^ 2) ^ 2 := by
      use 2 * (p ^ 2 - n ^ 4)
      nlinarith
    exact Int.Prime.dvd_pow' (p := 2) (k := 2) Nat.prime_two hx_sq_dvd
  have hm_even_iff_hn_even : (2 : ℤ) ∣ m ↔ (2 : ℤ) ∣ n := by
    constructor
    · intro hm2
      have hm2sq : (2 : ℤ) ∣ m ^ 2 := dvd_pow hm2 (by norm_num : (2 : ℕ) ≠ 0)
      have hn2sq : (2 : ℤ) ∣ n ^ 2 := by
        have htmp : (2 : ℤ) ∣ m ^ 2 - (m ^ 2 - n ^ 2) := dvd_sub hm2sq hx_even
        convert htmp using 1
        · nlinarith
      exact Int.Prime.dvd_pow' (p := 2) (k := 2) Nat.prime_two hn2sq
    · intro hn2
      have hn2sq : (2 : ℤ) ∣ n ^ 2 := dvd_pow hn2 (by norm_num : (2 : ℕ) ≠ 0)
      have hm2sq : (2 : ℤ) ∣ m ^ 2 := by
        have htmp : (2 : ℤ) ∣ (m ^ 2 - n ^ 2) + n ^ 2 := dvd_add hx_even hn2sq
        convert htmp using 1
        · nlinarith
      exact Int.Prime.dvd_pow' (p := 2) (k := 2) Nat.prime_two hm2sq
  have hn_odd : Odd n := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hn2
    have hm2 : (2 : ℤ) ∣ m := hm_even_iff_hn_even.mpr hn2
    have hp2 : (2 : ℤ) ∣ p := by
      rcases hm2 with ⟨a, ha⟩
      rcases hn2 with ⟨b, hb⟩
      subst m
      subst n
      have hp2sq : (2 : ℤ) ∣ p ^ 2 := by
        use 2 * ((a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4)
        nlinarith
      exact Int.Prime.dvd_pow' (p := 2) (k := 2) Nat.prime_two hp2sq
    have hq2 : (2 : ℤ) ∣ q := by
      rw [hqmn]
      exact dvd_mul_of_dvd_right hn2 m
    have h2gcd : (2 : ℤ) ∣ (Int.gcd p q : ℤ) := Int.dvd_coe_gcd hp2 hq2
    rw [hcop] at h2gcd
    norm_num at h2gcd
  have hm_odd : Odd m := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hm2
    have hn2 : (2 : ℤ) ∣ n := hm_even_iff_hn_even.mp hm2
    exact (show ¬ (2 : ℤ) ∣ n from by
      simpa [← even_iff_two_dvd, Int.not_even_iff_odd] using hn_odd) hn2
  obtain ⟨r, hr0⟩ := hx_even
  have hr : 2 * r = m ^ 2 - n ^ 2 := by linarith
  let P : ℤ := p.natAbs
  have hP_sq : P ^ 2 = p ^ 2 := by
    dsimp [P]
    rw [Int.natCast_natAbs]
    exact sq_abs p
  have htriple : P ^ 2 = n ^ 4 + r ^ 2 := by nlinarith
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact_mod_cast Nat.zero_le p.natAbs
  have hP_sq_gt_r_sq : r ^ 2 < P ^ 2 := by
    have hn4pos : 0 < n ^ 4 := by positivity
    nlinarith
  have hleft_pos : 0 < P - r := by
    by_contra hnot
    have hle : P ≤ r := by omega
    have hr_nonneg : 0 ≤ r := by omega
    have hsq : P ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hP_nonneg hr_nonneg).mpr hle
    nlinarith
  have hright_pos : 0 < P + r := by
    by_contra hnot
    have hle : P ≤ -r := by omega
    have hnr_nonneg : 0 ≤ -r := by omega
    have hsq : P ^ 2 ≤ (-r) ^ 2 := (sq_le_sq₀ hP_nonneg hnr_nonneg).mpr hle
    nlinarith
  have hpq_coprime : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hpn_coprime : IsCoprime p n := by
    have hp_mn : IsCoprime p (m * n) := by simpa [hqmn] using hpq_coprime
    exact IsCoprime.of_mul_right_right hp_mn
  have hPn_gcd : Int.gcd P n = 1 := by
    have hpn_gcd : Int.gcd p n = 1 := Int.isCoprime_iff_gcd_eq_one.mp hpn_coprime
    have hPnat : P.natAbs = p.natAbs := by dsimp [P]
    simpa [Int.gcd_def, hPnat] using hpn_gcd
  have hnr_gcd : Int.gcd n r = 1 := by
    by_contra H
    obtain ⟨ℓ, hℓprime, hℓn, hℓr⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
    rw [← Int.natCast_dvd] at hℓn hℓr
    have hℓP2 : (ℓ : ℤ) ∣ P ^ 2 := by
      rw [htriple]
      exact dvd_add (dvd_pow hℓn (by norm_num : (4 : ℕ) ≠ 0))
        (dvd_pow hℓr (by norm_num : (2 : ℕ) ≠ 0))
    have hℓP : (ℓ : ℤ) ∣ P := Int.Prime.dvd_pow' (p := ℓ) (k := 2) hℓprime hℓP2
    apply hℓprime.not_dvd_one
    rw [← hPn_gcd]
    rw [Int.gcd_def]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp hℓP) (Int.natCast_dvd.mp hℓn)
  have hPr_gcd : Int.gcd r P = 1 := by
    have hnr_coprime : IsCoprime n r := Int.isCoprime_iff_gcd_eq_one.mpr hnr_gcd
    have hn2r_gcd : Int.gcd (n ^ 2) r = 1 := by
      exact Int.isCoprime_iff_gcd_eq_one.mp (hnr_coprime.pow_left (m := 2))
    have hpy : PythagoreanTriple (n ^ 2) r P := by
      unfold PythagoreanTriple
      nlinarith
    exact hpy.coprime_of_coprime hn2r_gcd
  have hr_even : Even r := by
    rw [even_iff_two_dvd]
    have h8m : (8 : ℤ) ∣ m ^ 2 - 1 := Int.eight_dvd_sq_sub_one_of_odd hm_odd
    have h8n : (8 : ℤ) ∣ n ^ 2 - 1 := Int.eight_dvd_sq_sub_one_of_odd hn_odd
    have h8diff : (8 : ℤ) ∣ m ^ 2 - n ^ 2 := by
      have htmp := dvd_sub h8m h8n
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
    rcases h8diff with ⟨k, hk⟩
    use 2 * k
    nlinarith
  have hP_odd : Odd P := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hP2
    have hP2sq : (2 : ℤ) ∣ P ^ 2 := dvd_pow hP2 (by norm_num : (2 : ℕ) ≠ 0)
    have hr2 : (2 : ℤ) ∣ r := even_iff_two_dvd.mp hr_even
    have hr2sq : (2 : ℤ) ∣ r ^ 2 := dvd_pow hr2 (by norm_num : (2 : ℕ) ≠ 0)
    have hn4 : (2 : ℤ) ∣ n ^ 4 := by
      have htmp : (2 : ℤ) ∣ P ^ 2 - r ^ 2 := dvd_sub hP2sq hr2sq
      convert htmp using 1
      · nlinarith
    have hn2 : (2 : ℤ) ∣ n := Int.Prime.dvd_pow' (p := 2) (k := 4) Nat.prime_two hn4
    exact (show ¬ (2 : ℤ) ∣ n from by
      simpa [← even_iff_two_dvd, Int.not_even_iff_odd] using hn_odd) hn2
  have hA_odd : Odd (P - r) := hP_odd.sub_even hr_even
  have hcop_pm : IsCoprime (P - r) (P + r) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    by_contra H
    obtain ⟨ℓ, hℓprime, hℓA, hℓB⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
    rw [← Int.natCast_dvd] at hℓA hℓB
    have hℓ2P : (ℓ : ℤ) ∣ 2 * P := by
      have htmp := dvd_add hℓB hℓA
      simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
    have hℓ2r : (ℓ : ℤ) ∣ 2 * r := by
      have htmp := dvd_sub hℓB hℓA
      simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
    have hℓ_ne_two : ℓ ≠ 2 := by
      intro hℓ2eq
      have h2A : (2 : ℤ) ∣ P - r := by simpa [hℓ2eq] using hℓA
      exact (show ¬ (2 : ℤ) ∣ P - r from by
        simpa [← even_iff_two_dvd, Int.not_even_iff_odd] using hA_odd) h2A
    have hℓP : (ℓ : ℤ) ∣ P := by
      rcases Int.Prime.dvd_mul' (p := ℓ) hℓprime hℓ2P with hℓ_two | hℓP
      · have hℓ_two_nat : ℓ ∣ 2 := by exact Int.natCast_dvd.mp hℓ_two
        have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓ_two_nat
        exact False.elim (hℓ_ne_two (le_antisymm hle hℓprime.two_le))
      · exact hℓP
    have hℓr : (ℓ : ℤ) ∣ r := by
      rcases Int.Prime.dvd_mul' (p := ℓ) hℓprime hℓ2r with hℓ_two | hℓr
      · have hℓ_two_nat : ℓ ∣ 2 := by exact Int.natCast_dvd.mp hℓ_two
        have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓ_two_nat
        exact False.elim (hℓ_ne_two (le_antisymm hle hℓprime.two_le))
      · exact hℓr
    apply hℓprime.not_dvd_one
    rw [← hPr_gcd]
    rw [Int.gcd_def]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp hℓr) (Int.natCast_dvd.mp hℓP)
  obtain ⟨c0, d0, hpc0, hpd0, hcdsq0⟩ :=
    right5_fourth_power_split P r n hleft_pos hright_pos hcop_pm htriple
  let c : ℤ := c0.natAbs
  let d : ℤ := d0.natAbs
  have hc4 : c ^ 4 = c0 ^ 4 := by
    dsimp [c]
    rw [Int.natCast_natAbs]
    exact (by norm_num : Even 4).pow_abs c0
  have hd4 : d ^ 4 = d0 ^ 4 := by
    dsimp [d]
    rw [Int.natCast_natAbs]
    exact (by norm_num : Even 4).pow_abs d0
  have hpc : P - r = c ^ 4 := by rw [hc4]; exact hpc0
  have hpd : P + r = d ^ 4 := by rw [hd4]; exact hpd0
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.zero_le c0.natAbs
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.zero_le d0.natAbs
  have hc_pos : 0 < c := by
    by_contra hnot
    have hc0 : c = 0 := by omega
    rw [hc0] at hpc
    norm_num at hpc
    nlinarith
  have hd : 1 ≤ d := by
    have hd_pos : 0 < d := by
      by_contra hnot
      have hd0 : d = 0 := by omega
      rw [hd0] at hpd
      norm_num at hpd
      nlinarith
    omega
  have hcdsq : (c * d) ^ 2 = n ^ 2 := by
    have hsq : (c * d) ^ 2 = (c0 * d0) ^ 2 := by
      dsimp [c, d]
      rw [Int.natCast_natAbs, Int.natCast_natAbs, ← abs_mul, sq_abs]
    rw [hsq, hcdsq0]
  have hcd : n = c * d := by
    have hcd_nonneg : 0 ≤ c * d := mul_nonneg hc_nonneg hd_nonneg
    have habs : n.natAbs = (c * d).natAbs := Int.natAbs_eq_iff_sq_eq.mpr hcdsq.symm
    exact (Int.natAbs_inj_of_nonneg_of_nonneg (by omega : 0 ≤ n) hcd_nonneg).mp habs
  have hm_sq_from_split : m ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 := by
    nlinarith
  have hc : 2 ≤ c := by
    by_contra hnot
    have hc_eq_one : c = 1 := by omega
    by_cases hd_eq_one : d = 1
    · have hn_eq_one : n = 1 := by
        have htmp := hcd
        rw [hc_eq_one, hd_eq_one] at htmp
        norm_num at htmp
        exact htmp
      have hm_eq_one : m = 1 := by
        have htmp := hm_sq_from_split
        rw [hc_eq_one, hd_eq_one] at htmp
        norm_num at htmp
        rcases htmp with htmp | htmp
        · exact htmp
        · omega
      have hq_one : q = 1 := by nlinarith [hqmn, hm_eq_one, hn_eq_one]
      omega
    · have hd_ge_two : 2 ≤ d := by omega
      have hm_sq_expr : m ^ 2 = d ^ 4 + d ^ 2 - 1 := by
        have htmp := hm_sq_from_split
        rw [hc_eq_one] at htmp
        norm_num at htmp
        exact htmp
      have hd2_gt_one : 1 < d ^ 2 := by nlinarith [hd_ge_two, sq_nonneg (d - 2)]
      have hlow : d ^ 4 < m ^ 2 := by nlinarith [hm_sq_expr, hd2_gt_one]
      have hhigh : m ^ 2 < (d ^ 2 + 1) ^ 2 := by nlinarith [hm_sq_expr, sq_nonneg d]
      have h_abs_gt : d ^ 2 < |m| := by
        have hs : (d ^ 2) ^ 2 < |m| ^ 2 := by
          rw [sq_abs]
          nlinarith
        exact (sq_lt_sq₀ (sq_nonneg d) (abs_nonneg m)).mp hs
      have h_abs_lt : |m| < d ^ 2 + 1 := by
        have hnonneg : 0 ≤ d ^ 2 + 1 := by nlinarith [sq_nonneg d]
        have hs : |m| ^ 2 < (d ^ 2 + 1) ^ 2 := by
          rw [sq_abs]
          exact hhigh
        exact (sq_lt_sq₀ (abs_nonneg m) hnonneg).mp hs
      omega
  have hc_lt_q : c < q := by
    have hq_eq : q = c * (m * d) := by
      rw [hqmn, hcd]
      ring
    have hmd_ge_one : 1 ≤ m * d := by nlinarith [hmpos, hd]
    have hmd_ne_one : m * d ≠ 1 := by
      intro hmd_one
      have hm_eq_one : m = 1 := by
        have hm_unit : IsUnit m := isUnit_iff_dvd_one.mpr ⟨d, hmd_one.symm⟩
        have hm_abs : m.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hm_unit
        exact (Int.natAbs_inj_of_nonneg_of_nonneg (by omega : 0 ≤ m)
          (by norm_num : 0 ≤ (1 : ℤ))).mp hm_abs
      have hd_eq_one : d = 1 := by
        have hd_unit : IsUnit d := isUnit_iff_dvd_one.mpr ⟨m, by simpa [mul_comm] using hmd_one.symm⟩
        have hd_abs : d.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hd_unit
        exact (Int.natAbs_inj_of_nonneg_of_nonneg (by omega : 0 ≤ d)
          (by norm_num : 0 ≤ (1 : ℤ))).mp hd_abs
      have hc4_eq_hc2 : c ^ 4 = c ^ 2 := by
        have htmp := hm_sq_from_split
        rw [hm_eq_one, hd_eq_one] at htmp
        norm_num at htmp
        linear_combination htmp
      have hc2_le_one : c ^ 2 ≤ 1 := by
        nlinarith only [hc4_eq_hc2, sq_nonneg (c ^ 2 - 1)]
      have hc2_ge_four : 4 ≤ c ^ 2 := by
        nlinarith only [hc, sq_nonneg (c - 2)]
      nlinarith only [hc2_le_one, hc2_ge_four]
    have hmd_ge_two : 2 ≤ m * d := by omega
    have hc_mul_two : c < c * 2 := by nlinarith only [hc]
    have hc_mul_le : c * 2 ≤ c * (m * d) := by nlinarith only [hc, hmd_ge_two]
    nlinarith only [hq_eq, hc_mul_two, hc_mul_le]
  have hcop_cd : Int.gcd d c = 1 := by
    have hcop_pow : IsCoprime (c ^ 4) (d ^ 4) := by
      rw [← hpc, ← hpd]
      exact hcop_pm
    have hcop_cd' : IsCoprime c d := (IsCoprime.pow_iff (by norm_num : 0 < 4) (by norm_num : 0 < 4)).mp hcop_pow
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop_cd'.symm
  exact right5_descent_tail_from_fourth_split P q t n m r c d hc hd hmpos hc_lt_q (by omega) hcop_cd hpc hpd hcd hr

/-- `left5` is the `A = 5 m⁴, B = n⁴` branch.  It is the mirror image of
`right5` under the swap `m ↔ n` (the square `(n²-m²)² = (m²-n²)²` is symmetric),
so it reduces to `right5` with the two parameters exchanged. -/
private theorem pythagorean_square_leg_self_descent_left5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs :=
  pythagorean_square_leg_self_descent_right5 p q t n m hq hcop hnpos hmpos
    (by rw [hqmn]; ring) hcoeff

