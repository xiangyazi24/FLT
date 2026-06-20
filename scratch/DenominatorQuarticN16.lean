import Mathlib
import scratch.CoprimeFactorSplit

set_option maxHeartbeats 1200000

/-!
# Denominator quartic for the N=16 obstruction curve

The rational denominator reduction for
`w^2 = u^3 - u^2 - u` produces the quartic

`t^2 = p^4 - p^2*q^2 - q^4`.

This file proves that it has no primitive integer solution with `q >= 2`.
The proof is the same Pellian/fourth-power descent pattern as the discharged
20a4 denominator quartic, with the sign change carried through the coefficient
identity.
-/

namespace DenominatorQuarticN16

def NegQuartic (p q t : ℤ) : Prop :=
  t ^ 2 = p ^ 4 - p ^ 2 * q ^ 2 - q ^ 4

private def nphiA (p q t : ℤ) : ℤ :=
  2 * p ^ 2 - q ^ 2 - 2 * t

private def nphiB (p q t : ℤ) : ℤ :=
  2 * p ^ 2 - q ^ 2 + 2 * t

private lemma nphi_AB_eq_5q4 (p q t : ℤ)
    (h : NegQuartic p q t) :
    nphiA p q t * nphiB p q t = 5 * q ^ 4 := by
  unfold nphiA nphiB NegQuartic at *
  nlinarith

private lemma nphi_A_add_B (p q t : ℤ) :
    nphiA p q t + nphiB p q t = 2 * (2 * p ^ 2 - q ^ 2) := by
  unfold nphiA nphiB
  ring

private lemma nphi_B_sub_A (p q t : ℤ) :
    nphiB p q t - nphiA p q t = 4 * t := by
  unfold nphiA nphiB
  ring

private lemma two_p_sq_sub_q_sq_pos (p q t : ℤ) (hq : 2 ≤ q)
    (h : NegQuartic p q t) :
    0 < 2 * p ^ 2 - q ^ 2 := by
  have hq0 : q ≠ 0 := by omega
  have hq2pos : 0 < q ^ 2 := sq_pos_of_ne_zero hq0
  have hp2nonneg : 0 ≤ p ^ 2 := sq_nonneg p
  have hnonneg : 0 ≤ p ^ 4 - p ^ 2 * q ^ 2 - q ^ 4 := by
    rw [← h]
    exact sq_nonneg t
  by_contra hnot
  have hle : 2 * p ^ 2 ≤ q ^ 2 := by omega
  nlinarith [mul_nonneg hp2nonneg (sub_nonneg.mpr hle), sq_nonneg (q ^ 2)]

private lemma nphi_pellian_factors_pos (p q t : ℤ)
    (hq : 2 ≤ q)
    (h : NegQuartic p q t) :
    0 < nphiA p q t ∧ 0 < nphiB p q t := by
  have hprod := nphi_AB_eq_5q4 p q t h
  have hsum := nphi_A_add_B p q t
  have hinner : 0 < 2 * p ^ 2 - q ^ 2 := two_p_sq_sub_q_sq_pos p q t hq h
  have hsum_pos : 0 < nphiA p q t + nphiB p q t := by
    rw [hsum]
    nlinarith
  have hprod_pos : 0 < nphiA p q t * nphiB p q t := by
    rw [hprod]
    positivity
  by_cases hA : 0 < nphiA p q t
  · by_cases hB : 0 < nphiB p q t
    · exact ⟨hA, hB⟩
    · have hBle : nphiB p q t ≤ 0 := by omega
      have hnonpos : nphiA p q t * nphiB p q t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA) hBle
      nlinarith
  · have hAle : nphiA p q t ≤ 0 := by omega
    by_cases hB : 0 < nphiB p q t
    · have hnonpos : nphiA p q t * nphiB p q t ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hAle (le_of_lt hB)
      nlinarith
    · have hBle : nphiB p q t ≤ 0 := by omega
      have hsum_nonpos : nphiA p q t + nphiB p q t ≤ 0 := by omega
      nlinarith

private lemma int_mod_four_cases (z : ℤ) :
    (∃ q, z = 4 * q) ∨ (∃ q, z = 4 * q + 1) ∨
    (∃ q, z = 4 * q + 2) ∨ (∃ q, z = 4 * q - 1) := by
  have hnonneg : 0 ≤ z % 4 := Int.emod_nonneg z (by norm_num : (4 : ℤ) ≠ 0)
  have hlt : z % 4 < 4 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 4)
  have hdiv := Int.mul_ediv_add_emod z 4
  interval_cases z % 4
  · left
    exact ⟨z / 4, by omega⟩
  · right
    left
    exact ⟨z / 4, by omega⟩
  · right
    right
    left
    exact ⟨z / 4, by omega⟩
  · right
    right
    right
    exact ⟨z / 4 + 1, by omega⟩

private lemma int_odd_mod_four_cases (z : ℤ) (hz : Odd z) :
    (∃ q, z = 4 * q + 1) ∨ (∃ q, z = 4 * q - 1) := by
  have hz2 : z % 2 = 1 := Int.odd_iff.mp hz
  rcases int_mod_four_cases z with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
  · have : z % 2 = 0 := by
      rw [hq]
      omega
    omega
  · left
    exact ⟨q, hq⟩
  · have : z % 2 = 0 := by
      rw [hq]
      omega
    omega
  · right
    exact ⟨q, hq⟩

private lemma square_not_four_mul_add_three (t K : ℤ)
    (h : t ^ 2 = 4 * K + 3) : False := by
  rcases int_mod_four_cases t with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have : 16 * c ^ 2 = 4 * K + 3 := by nlinarith
    omega
  · have : 16 * c ^ 2 + 8 * c + 1 = 4 * K + 3 := by nlinarith
    omega
  · have : 16 * c ^ 2 + 16 * c + 4 = 4 * K + 3 := by nlinarith
    omega
  · have : 16 * c ^ 2 - 8 * c + 1 = 4 * K + 3 := by nlinarith
    omega

private lemma square_not_sixteen_mul_add_thirteen (t K : ℤ)
    (h : t ^ 2 = 16 * K + 13) : False := by
  rcases int_mod_four_cases t with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have : 16 * c ^ 2 = 16 * K + 13 := by nlinarith
    omega
  · have : 16 * c ^ 2 + 8 * c + 1 = 16 * K + 13 := by nlinarith
    omega
  · have : 16 * c ^ 2 + 16 * c + 4 = 16 * K + 13 := by nlinarith
    omega
  · have : 16 * c ^ 2 - 8 * c + 1 = 16 * K + 13 := by nlinarith
    omega

private lemma q_odd_contra (p q t : ℤ)
    (hq_odd : ¬ (2 : ℤ) ∣ q)
    (h : NegQuartic p q t) : False := by
  have hqodd : Odd q := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    exact hq_odd
  rcases Int.even_or_odd p with hp_even | hp_odd
  · rcases hp_even with ⟨a, hp⟩
    rcases int_odd_mod_four_cases q hqodd with ⟨b, hq⟩ | ⟨b, hq⟩
    · rw [hp, hq] at h
      have hmod : t ^ 2 = 4 *
          (-1 - 4 * b - 24 * b ^ 2 - a ^ 2 - 64 * b ^ 3
            - 8 * a ^ 2 * b - 64 * b ^ 4 - 16 * a ^ 2 * b ^ 2
            + 4 * a ^ 4) + 3 := by
        unfold NegQuartic at h
        ring_nf at h ⊢
        exact h
      exact square_not_four_mul_add_three t _ hmod
    · rw [hp, hq] at h
      have hmod : t ^ 2 = 4 *
          (-1 + 4 * b - 24 * b ^ 2 - a ^ 2 + 64 * b ^ 3
            + 8 * a ^ 2 * b - 64 * b ^ 4 - 16 * a ^ 2 * b ^ 2
            + 4 * a ^ 4) + 3 := by
        unfold NegQuartic at h
        ring_nf at h ⊢
        exact h
      exact square_not_four_mul_add_three t _ hmod
  · rcases int_odd_mod_four_cases p hp_odd with ⟨a, hp⟩ | ⟨a, hp⟩
    · rcases int_odd_mod_four_cases q hqodd with ⟨b, hq⟩ | ⟨b, hq⟩
      · rw [hp, hq] at h
        have hmod : t ^ 2 = 4 *
            (-1 - 6 * b + 2 * a - 28 * b ^ 2 - 16 * a * b
              + 20 * a ^ 2 - 64 * b ^ 3 - 32 * a * b ^ 2
              - 32 * a ^ 2 * b + 64 * a ^ 3 - 64 * b ^ 4
              - 64 * a ^ 2 * b ^ 2 + 64 * a ^ 4) + 3 := by
          unfold NegQuartic at h
          ring_nf at h ⊢
          exact h
        exact square_not_four_mul_add_three t _ hmod
      · rw [hp, hq] at h
        have hmod : t ^ 2 = 4 *
            (-1 + 6 * b + 2 * a - 28 * b ^ 2 + 16 * a * b
              + 20 * a ^ 2 + 64 * b ^ 3 - 32 * a * b ^ 2
              + 32 * a ^ 2 * b + 64 * a ^ 3 - 64 * b ^ 4
              - 64 * a ^ 2 * b ^ 2 + 64 * a ^ 4) + 3 := by
          unfold NegQuartic at h
          ring_nf at h ⊢
          exact h
        exact square_not_four_mul_add_three t _ hmod
    · rcases int_odd_mod_four_cases q hqodd with ⟨b, hq⟩ | ⟨b, hq⟩
      · rw [hp, hq] at h
        have hmod : t ^ 2 = 4 *
            (-1 - 6 * b - 2 * a - 28 * b ^ 2 + 16 * a * b
              + 20 * a ^ 2 - 64 * b ^ 3 + 32 * a * b ^ 2
              - 32 * a ^ 2 * b - 64 * a ^ 3 - 64 * b ^ 4
              - 64 * a ^ 2 * b ^ 2 + 64 * a ^ 4) + 3 := by
          unfold NegQuartic at h
          ring_nf at h ⊢
          exact h
        exact square_not_four_mul_add_three t _ hmod
      · rw [hp, hq] at h
        have hmod : t ^ 2 = 4 *
            (-1 + 6 * b - 2 * a - 28 * b ^ 2 - 16 * a * b
              + 20 * a ^ 2 + 64 * b ^ 3 + 32 * a * b ^ 2
              + 32 * a ^ 2 * b - 64 * a ^ 3 - 64 * b ^ 4
              - 64 * a ^ 2 * b ^ 2 + 64 * a ^ 4) + 3 := by
          unfold NegQuartic at h
          ring_nf at h ⊢
          exact h
        exact square_not_four_mul_add_three t _ hmod

private lemma q_two_times_odd_half_contra (p s t : ℤ)
    (hpodd : Odd p) (hsodd : Odd s)
    (h : NegQuartic p (2 * s) t) : False := by
  rcases int_odd_mod_four_cases p hpodd with ⟨a, hp⟩ | ⟨a, hp⟩
  · rcases int_odd_mod_four_cases s hsodd with ⟨b, hs⟩ | ⟨b, hs⟩
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-2 - 18 * b - a - 100 * b ^ 2 - 16 * a * b + 2 * a ^ 2
            - 256 * b ^ 3 - 32 * a * b ^ 2 - 32 * a ^ 2 * b + 16 * a ^ 3
            - 256 * b ^ 4 - 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 13 := by
        unfold NegQuartic at h
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_thirteen t _ hmod
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-2 + 18 * b - a - 100 * b ^ 2 + 16 * a * b + 2 * a ^ 2
            + 256 * b ^ 3 - 32 * a * b ^ 2 + 32 * a ^ 2 * b + 16 * a ^ 3
            - 256 * b ^ 4 - 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 13 := by
        unfold NegQuartic at h
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_thirteen t _ hmod
  · rcases int_odd_mod_four_cases s hsodd with ⟨b, hs⟩ | ⟨b, hs⟩
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-2 - 18 * b + a - 100 * b ^ 2 + 16 * a * b + 2 * a ^ 2
            - 256 * b ^ 3 + 32 * a * b ^ 2 - 32 * a ^ 2 * b - 16 * a ^ 3
            - 256 * b ^ 4 - 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 13 := by
        unfold NegQuartic at h
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_thirteen t _ hmod
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-2 + 18 * b + a - 100 * b ^ 2 - 16 * a * b + 2 * a ^ 2
            + 256 * b ^ 3 + 32 * a * b ^ 2 + 32 * a ^ 2 * b - 16 * a ^ 3
            - 256 * b ^ 4 - 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 13 := by
        unfold NegQuartic at h
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_thirteen t _ hmod

private theorem neg_square_leg_descent_core
    (p q _t m n : ℤ)
    (_hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = 2 * (m * n))
    (hcoeff : p ^ 2 = (n ^ 2 + m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      NegQuartic p' q' t' ∧
      q'.natAbs < q.natAbs := by
  have hp_odd : Odd p := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hp2
    have hq2 : (2 : ℤ) ∣ q := by
      rw [hqmn]
      exact ⟨m * n, by ring⟩
    have h2gcd : (2 : ℤ) ∣ (Int.gcd p q : ℤ) := Int.dvd_coe_gcd hp2 hq2
    rw [hcop] at h2gcd
    norm_num at h2gcd
  let r : ℤ := n ^ 2 + m ^ 2
  let P : ℤ := p.natAbs
  have hP_sq : P ^ 2 = p ^ 2 := by
    dsimp [P]
    rw [Int.natCast_natAbs]
    exact sq_abs p
  have htriple : P ^ 2 = r ^ 2 + 4 * m ^ 4 := by
    dsimp [r]
    nlinarith
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact_mod_cast Nat.zero_le p.natAbs
  have hP_odd : Odd P := by
    rcases hp_odd with ⟨a, hp⟩
    by_cases hnonneg : 0 ≤ 2 * a + 1
    · dsimp [P]
      rw [hp]
      rw [Int.natAbs_of_nonneg hnonneg]
      exact ⟨a, by ring⟩
    · have hnonpos : 2 * a + 1 ≤ 0 := by omega
      dsimp [P]
      rw [hp]
      rw [Int.ofNat_natAbs_of_nonpos hnonpos]
      exact ⟨-a - 1, by ring⟩
  have hr_odd : Odd r := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hr2
    have hr2sq : (2 : ℤ) ∣ r ^ 2 := dvd_pow hr2 (by norm_num : (2 : ℕ) ≠ 0)
    have h4m4 : (2 : ℤ) ∣ 4 * m ^ 4 := by
      exact ⟨2 * m ^ 4, by ring⟩
    have hP2sq : (2 : ℤ) ∣ P ^ 2 := by
      rw [htriple]
      exact dvd_add hr2sq h4m4
    have hP2 : (2 : ℤ) ∣ P :=
      Int.Prime.dvd_pow' (p := 2) (k := 2) Nat.prime_two hP2sq
    have hPmod : P % 2 = 1 := Int.odd_iff.mp hP_odd
    rcases hP2 with ⟨k, hk⟩
    rw [hk] at hPmod
    omega
  have hleft_even : Even (P - r) := hP_odd.sub_odd hr_odd
  have hright_even : Even (P + r) := hP_odd.add_odd hr_odd
  rcases hleft_even with ⟨X, hXdef0⟩
  rcases hright_even with ⟨Y, hYdef0⟩
  have hXdef : P - r = 2 * X := by
    rw [hXdef0]
    ring
  have hYdef : P + r = 2 * Y := by
    rw [hYdef0]
    ring
  have hP_eq_XY : P = X + Y := by nlinarith
  have hr_eq_YX : r = Y - X := by nlinarith
  have hm_pos : 0 < m := by omega
  have hm4_pos : 0 < 4 * m ^ 4 := by positivity
  have hP_sq_gt_r_sq : r ^ 2 < P ^ 2 := by nlinarith
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
  have hXpos : 0 < X := by nlinarith
  have hYpos : 0 < Y := by nlinarith
  have hXY : X * Y = m ^ 4 := by
    have hprod : (P - r) * (P + r) = 4 * m ^ 4 := by nlinarith
    nlinarith
  have hPq_gcd : Int.gcd P q = 1 := by
    have hPnat : P.natAbs = p.natAbs := by
      dsimp [P]
    simpa [Int.gcd_def, hPnat] using hcop
  have hcopXY_gcd : Int.gcd X Y = 1 := by
    by_contra H
    obtain ⟨ℓ, hℓprime, hℓX, hℓY⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
    rw [← Int.natCast_dvd] at hℓX hℓY
    have hℓP : (ℓ : ℤ) ∣ P := by
      rw [hP_eq_XY]
      exact dvd_add hℓX hℓY
    have hℓr : (ℓ : ℤ) ∣ r := by
      rw [hr_eq_YX]
      exact dvd_sub hℓY hℓX
    have hℓP2 : (ℓ : ℤ) ∣ P ^ 2 := dvd_pow hℓP (by norm_num : (2 : ℕ) ≠ 0)
    have hℓr2 : (ℓ : ℤ) ∣ r ^ 2 := dvd_pow hℓr (by norm_num : (2 : ℕ) ≠ 0)
    have hℓ4m4 : (ℓ : ℤ) ∣ 4 * m ^ 4 := by
      have htmp : (ℓ : ℤ) ∣ P ^ 2 - r ^ 2 := dvd_sub hℓP2 hℓr2
      convert htmp using 1
      · nlinarith
    have hℓ_ne_two : ℓ ≠ 2 := by
      intro hℓ2
      have h2P : (2 : ℤ) ∣ P := by simpa [hℓ2] using hℓP
      have hPmod : P % 2 = 1 := Int.odd_iff.mp hP_odd
      rcases h2P with ⟨k, hk⟩
      rw [hk] at hPmod
      omega
    have hℓm : (ℓ : ℤ) ∣ m := by
      rcases Int.Prime.dvd_mul' (p := ℓ) hℓprime hℓ4m4 with hℓ4 | hℓm4
      · have hℓ4nat : ℓ ∣ 4 := Int.natCast_dvd.mp hℓ4
        have hle : ℓ ≤ 4 := Nat.le_of_dvd (by norm_num) hℓ4nat
        have hℓeq2 : ℓ = 2 := by
          have hpos : 0 < ℓ := hℓprime.pos
          interval_cases ℓ
          · norm_num at hℓprime
          · rfl
          · norm_num at hℓ4nat
          · norm_num at hℓprime
        exact False.elim (hℓ_ne_two hℓeq2)
      · exact Int.Prime.dvd_pow' (p := ℓ) (k := 4) hℓprime hℓm4
    have hℓq : (ℓ : ℤ) ∣ q := by
      rw [hqmn]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hℓm n) 2
    apply hℓprime.not_dvd_one
    rw [← hPq_gcd, Int.gcd_def]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp hℓP) (Int.natCast_dvd.mp hℓq)
  have hcopXY : IsCoprime X Y := Int.isCoprime_iff_gcd_eq_one.mpr hcopXY_gcd
  obtain ⟨c, d, hXc, hYd, hcd, hcpos, hdpos⟩ :=
    Scratch.ChatGPTDropDM1.coprime_product_eq_fourth_power
      X Y m hXpos hYpos hm_pos hcopXY hXY
  have hpc : P - r = 2 * c ^ 4 := by rw [hXdef, hXc]
  have hpd : P + r = 2 * d ^ 4 := by rw [hYdef, hYd]
  have hn_sq_from_split : n ^ 2 = d ^ 4 - d ^ 2 * c ^ 2 - c ^ 4 := by
    have hr' : r = d ^ 4 - c ^ 4 := by nlinarith
    have hm_sq : m ^ 2 = d ^ 2 * c ^ 2 := by
      rw [← hcd]
      ring
    dsimp [r] at hr'
    nlinarith
  have hc : 2 ≤ c := by
    by_contra hnot
    have hc_eq_one : c = 1 := by omega
    by_cases hd_eq_one : d = 1
    · have hn_sq_neg : n ^ 2 = -1 := by
        simpa [hc_eq_one, hd_eq_one] using hn_sq_from_split
      nlinarith [sq_nonneg n]
    · have hd_ge_two : 2 ≤ d := by omega
      have hn_sq_expr : n ^ 2 = d ^ 4 - d ^ 2 - 1 := by
        rw [hc_eq_one] at hn_sq_from_split
        norm_num at hn_sq_from_split
        exact hn_sq_from_split
      have hd2_gt_one : 1 < d ^ 2 := by nlinarith [hd_ge_two, sq_nonneg (d - 2)]
      have hlow : (d ^ 2 - 1) ^ 2 < n ^ 2 := by nlinarith [hn_sq_expr, hd2_gt_one]
      have hhigh : n ^ 2 < (d ^ 2) ^ 2 := by nlinarith [hn_sq_expr, sq_nonneg d]
      have h_abs_gt : d ^ 2 - 1 < |n| := by
        have hbase : 0 ≤ d ^ 2 - 1 := by nlinarith [hd_ge_two, sq_nonneg (d - 2)]
        have hs : (d ^ 2 - 1) ^ 2 < |n| ^ 2 := by
          rw [sq_abs]
          exact hlow
        exact (sq_lt_sq₀ hbase (abs_nonneg n)).mp hs
      have h_abs_lt : |n| < d ^ 2 := by
        have hnonneg : 0 ≤ d ^ 2 := sq_nonneg d
        have hs : |n| ^ 2 < (d ^ 2) ^ 2 := by
          rw [sq_abs]
          exact hhigh
        exact (sq_lt_sq₀ (abs_nonneg n) hnonneg).mp hs
      omega
  have hcop_dc : Int.gcd d c = 1 := by
    have hcop_pow : IsCoprime (c ^ 4) (d ^ 4) := by
      rw [← hXc, ← hYd]
      exact hcopXY
    have hcop_cd' : IsCoprime c d :=
      (IsCoprime.pow_iff (by norm_num : 0 < 4) (by norm_num : 0 < 4)).mp hcop_pow
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop_cd'.symm
  have hc_lt_q : c < q := by
    have hq_eq : q = c * (2 * d * n) := by
      rw [hqmn, ← hcd]
      ring
    have hfactor_ge_two : 2 ≤ 2 * d * n := by nlinarith [hdpos, hnpos]
    have hc_mul_two : c < c * 2 := by nlinarith [hc]
    have hc_mul_le : c * 2 ≤ c * (2 * d * n) := by nlinarith [hc, hfactor_ge_two]
    nlinarith
  refine ⟨d, c, n, hc, hcop_dc, ?_, ?_⟩
  · unfold NegQuartic
    exact hn_sq_from_split
  · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) hc_lt_q

private theorem nphi_descent_step_even_core
    (p q t : ℤ)
    (hq : 2 ≤ q)
    (hqeven : (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : NegQuartic p q t) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      NegQuartic p' q' t' ∧
      q'.natAbs < q.natAbs := by
  have hp_odd : Odd p := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hp2
    have h2gcd : (2 : ℤ) ∣ (Int.gcd p q : ℤ) := Int.dvd_coe_gcd hp2 hqeven
    rw [hcop] at h2gcd
    norm_num at h2gcd
  have ht_odd : Odd t := by
    have hp4_odd : Odd (p ^ 4) := hp_odd.pow
    have hp2q2_even : Even (p ^ 2 * q ^ 2) := by
      rw [even_iff_two_dvd]
      exact dvd_mul_of_dvd_right (dvd_pow hqeven (by norm_num : (2 : ℕ) ≠ 0)) (p ^ 2)
    have hq4_even : Even (q ^ 4) := by
      rw [even_iff_two_dvd]
      exact dvd_pow hqeven (by norm_num : (4 : ℕ) ≠ 0)
    have hrhs_odd : Odd (p ^ 4 - p ^ 2 * q ^ 2 - q ^ 4) :=
      (hp4_odd.sub_even hp2q2_even).sub_even hq4_even
    have ht2_odd : Odd (t ^ 2) := by
      rw [h]
      exact hrhs_odd
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro ht2
    have ht2sq_even : Even (t ^ 2) := by
      rw [even_iff_two_dvd]
      exact dvd_pow ht2 (by norm_num : (2 : ℕ) ≠ 0)
    have h0 : (t ^ 2) % 2 = 0 := Int.even_iff.mp ht2sq_even
    have h1 : (t ^ 2) % 2 = 1 := Int.odd_iff.mp ht2_odd
    omega
  rcases hqeven with ⟨s, hqeq⟩
  have hqeq' : q = 2 * s := hqeq
  by_cases hs_even : (2 : ℤ) ∣ s
  · have hAB : nphiA p q t * nphiB p q t = 5 * q ^ 4 :=
      nphi_AB_eq_5q4 p q t h
    have hsum : nphiA p q t + nphiB p q t = 2 * (2 * p ^ 2 - q ^ 2) :=
      nphi_A_add_B p q t
    have hdiff : nphiB p q t - nphiA p q t = 4 * t :=
      nphi_B_sub_A p q t
    have hpos : 0 < nphiA p q t ∧ 0 < nphiB p q t :=
      nphi_pellian_factors_pos p q t hq h
    have hspos : 0 < s := by omega
    have hp2_odd : Odd (p ^ 2) := hp_odd.pow
    have h2s2_even : Even (2 * s ^ 2) := ⟨s ^ 2, by ring⟩
    have hinnerA_even : Even (p ^ 2 - 2 * s ^ 2 - t) := by
      have hpt : Even (p ^ 2 - t) := hp2_odd.sub_odd ht_odd
      rcases hpt with ⟨u, hu⟩
      rcases h2s2_even with ⟨v, hv⟩
      refine ⟨u - v, ?_⟩
      nlinarith
    have hinnerB_even : Even (p ^ 2 - 2 * s ^ 2 + t) := by
      have hpt : Even (p ^ 2 + t) := hp2_odd.add_odd ht_odd
      rcases hpt with ⟨u, hu⟩
      rcases h2s2_even with ⟨v, hv⟩
      refine ⟨u - v, ?_⟩
      nlinarith
    rcases hinnerA_even with ⟨A1, hAinner⟩
    rcases hinnerB_even with ⟨B1, hBinner⟩
    have hAeq : nphiA p q t = 4 * A1 := by
      dsimp [nphiA]
      rw [hqeq']
      nlinarith
    have hBeq : nphiB p q t = 4 * B1 := by
      dsimp [nphiB]
      rw [hqeq']
      nlinarith
    have hA1pos : 0 < A1 := by
      have hApos := hpos.1
      rw [hAeq] at hApos
      nlinarith
    have hB1pos : 0 < B1 := by
      have hBpos := hpos.2
      rw [hBeq] at hBpos
      nlinarith
    have hA1B1 : A1 * B1 = 5 * s ^ 4 := by
      have hAB' := hAB
      rw [hAeq, hBeq, hqeq'] at hAB'
      nlinarith
    have hA1sum : A1 + B1 = p ^ 2 - 2 * s ^ 2 := by
      have hsum' := hsum
      rw [hAeq, hBeq, hqeq'] at hsum'
      nlinarith
    have hB1sub : B1 - A1 = t := by
      have hdiff' := hdiff
      rw [hAeq, hBeq] at hdiff'
      nlinarith
    have hcopA1B1_gcd : Int.gcd A1 B1 = 1 := by
      by_contra H
      obtain ⟨ℓ, hℓprime, hℓA, hℓB⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
      rw [← Int.natCast_dvd] at hℓA hℓB
      have hℓsum : (ℓ : ℤ) ∣ A1 + B1 := dvd_add hℓA hℓB
      have hℓprod : (ℓ : ℤ) ∣ 5 * s ^ 4 := by
        rw [← hA1B1]
        exact dvd_mul_of_dvd_left hℓA B1
      have hℓs : (ℓ : ℤ) ∣ s := by
        rcases Int.Prime.dvd_mul' (p := ℓ) hℓprime hℓprod with hℓ5 | hℓs4
        · have hℓ5nat : ℓ ∣ 5 := Int.natCast_dvd.mp hℓ5
          have hle : ℓ ≤ 5 := Nat.le_of_dvd (by norm_num) hℓ5nat
          have hℓeq5 : ℓ = 5 := by
            have hposℓ : 0 < ℓ := hℓprime.pos
            interval_cases ℓ
            · norm_num at hℓprime
            · norm_num at hℓ5nat
            · norm_num at hℓ5nat
            · norm_num at hℓprime
            · rfl
          have h5A : (5 : ℤ) ∣ A1 := by simpa [hℓeq5] using hℓA
          have h5B : (5 : ℤ) ∣ B1 := by simpa [hℓeq5] using hℓB
          have h5s4 : (5 : ℤ) ∣ s ^ 4 := by
            rcases h5A with ⟨a, ha⟩
            rcases h5B with ⟨b, hb⟩
            use a * b
            rw [ha, hb] at hA1B1
            nlinarith
          simpa [hℓeq5] using
            (Int.Prime.dvd_pow' (p := 5) (k := 4) Nat.prime_five h5s4)
        · exact Int.Prime.dvd_pow' (p := ℓ) (k := 4) hℓprime hℓs4
      have hℓsum' : (ℓ : ℤ) ∣ p ^ 2 - 2 * s ^ 2 := by
        rwa [hA1sum] at hℓsum
      have hℓs2 : (ℓ : ℤ) ∣ s ^ 2 := dvd_pow hℓs (by norm_num : (2 : ℕ) ≠ 0)
      have hℓ2s2 : (ℓ : ℤ) ∣ 2 * s ^ 2 := dvd_mul_of_dvd_right hℓs2 2
      have hℓp2 : (ℓ : ℤ) ∣ p ^ 2 := by
        have htmp : (ℓ : ℤ) ∣ (p ^ 2 - 2 * s ^ 2) + 2 * s ^ 2 :=
          dvd_add hℓsum' hℓ2s2
        convert htmp using 1
        ring
      have hℓp : (ℓ : ℤ) ∣ p :=
        Int.Prime.dvd_pow' (p := ℓ) (k := 2) hℓprime hℓp2
      have hℓq : (ℓ : ℤ) ∣ q := by
        rw [hqeq']
        exact dvd_mul_of_dvd_right hℓs 2
      apply hℓprime.not_dvd_one
      rw [← hcop, Int.gcd_def]
      exact Nat.dvd_gcd (Int.natCast_dvd.mp hℓp) (Int.natCast_dvd.mp hℓq)
    have hcopA1B1 : IsCoprime A1 B1 :=
      Int.isCoprime_iff_gcd_eq_one.mpr hcopA1B1_gcd
    have h5prod : (5 : ℤ) ∣ A1 * B1 := by
      rw [hA1B1]
      exact dvd_mul_of_dvd_left (dvd_refl (5 : ℤ)) (s ^ 4)
    rcases Int.Prime.dvd_mul' (p := 5) Nat.prime_five h5prod with h5A | h5B
    · obtain ⟨m, n, hA5, hB4, hmn, hmpos, hnpos⟩ :=
        Scratch.ChatGPTDropDM1.coprime_fourth_power_factor A1 B1 s hA1B1
          hcopA1B1 hA1pos hB1pos hspos h5A
      have hcoeff : p ^ 2 = (n ^ 2 + m ^ 2) ^ 2 + 4 * m ^ 4 := by
        have hsum' : 5 * m ^ 4 + n ^ 4 = p ^ 2 - 2 * (m * n) ^ 2 := by
          calc
            5 * m ^ 4 + n ^ 4 = A1 + B1 := by rw [hA5, hB4]
            _ = p ^ 2 - 2 * s ^ 2 := hA1sum
            _ = p ^ 2 - 2 * (m * n) ^ 2 := by rw [← hmn]
        nlinarith
      have hqmn : q = 2 * (m * n) := by
        rw [hqeq', ← hmn]
      exact neg_square_leg_descent_core p q t m n hq hcop
        (by omega) (by omega) hqmn hcoeff
    · obtain ⟨m, n, hB5, hA4, hmn, hmpos, hnpos⟩ :=
        Scratch.ChatGPTDropDM1.coprime_fourth_power_factor B1 A1 s
          (by simpa [mul_comm] using hA1B1) hcopA1B1.symm
          hB1pos hA1pos hspos h5B
      have hcoeff : p ^ 2 = (n ^ 2 + m ^ 2) ^ 2 + 4 * m ^ 4 := by
        have hsum' : n ^ 4 + 5 * m ^ 4 = p ^ 2 - 2 * (m * n) ^ 2 := by
          calc
            n ^ 4 + 5 * m ^ 4 = A1 + B1 := by rw [hA4, hB5]
            _ = p ^ 2 - 2 * s ^ 2 := hA1sum
            _ = p ^ 2 - 2 * (m * n) ^ 2 := by rw [← hmn]
        nlinarith
      have hqmn : q = 2 * (m * n) := by
        rw [hqeq', ← hmn]
      exact neg_square_leg_descent_core p q t m n hq hcop
        (by omega) (by omega) hqmn hcoeff
  · have hs_odd : Odd s := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      exact hs_even
    have h2s : NegQuartic p (2 * s) t := by
      simpa [hqeq'] using h
    exact False.elim (q_two_times_odd_half_contra p s t hp_odd hs_odd h2s)

private theorem nphi_descent_step (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : NegQuartic p q t) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      NegQuartic p' q' t' ∧
      q'.natAbs < q.natAbs := by
  by_cases hqeven : (2 : ℤ) ∣ q
  · exact nphi_descent_step_even_core p q t hq hqeven hcop h
  · exact False.elim (q_odd_contra p q t hqeven h)

private theorem no_denominator_quartic_N16_aux :
    ∀ n : ℕ, ∀ p q t : ℤ,
      q.natAbs ≤ n →
      2 ≤ q →
      Int.gcd p q = 1 →
      NegQuartic p q t →
      False := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p q t hqn hq hcop hquartic
      obtain ⟨p', q', t', hq', hcop', hquartic', hdrop⟩ :=
        nphi_descent_step p q t hq hcop hquartic
      exact ih q'.natAbs (by omega) p' q' t' le_rfl hq' hcop' hquartic'

theorem no_denominator_quartic_N16 (p q t : ℤ) (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1) :
    t ^ 2 = p ^ 4 - p ^ 2 * q ^ 2 - q ^ 4 → False := by
  intro h
  exact no_denominator_quartic_N16_aux q.natAbs p q t le_rfl hq hcop h

end DenominatorQuarticN16
