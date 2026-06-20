import Mathlib
import scratch.CoprimeFactorSplit

set_option maxHeartbeats 1200000

/-!
# Ljunggren's quartic `x^4 + 14*x^2*y^2 + y^4`

This file proves the integer obstruction needed by the `N=12` reduction.
-/

namespace Ljunggren14

private def LQ (x y : ℤ) : ℤ :=
  x ^ 4 + 14 * x ^ 2 * y ^ 2 + y ^ 4

private lemma LQ_symm (x y : ℤ) : LQ x y = LQ y x := by
  unfold LQ
  ring

private lemma LQ_abs (x y : ℤ) : LQ |x| |y| = LQ x y := by
  unfold LQ
  rw [sq_abs, sq_abs]
  have hx4 : |x| ^ 4 = x ^ 4 := by
    exact (by norm_num : Even 4).pow_abs x
  have hy4 : |y| ^ 4 = y ^ 4 := by
    exact (by norm_num : Even 4).pow_abs y
  rw [hx4, hy4]

private lemma lj_factor (x y z : ℤ) (h : z ^ 2 = LQ x y) :
    (x ^ 2 + 7 * y ^ 2 - z) * (x ^ 2 + 7 * y ^ 2 + z) = 48 * y ^ 4 := by
  unfold LQ at h
  nlinarith

private lemma lj_factor_sum (x y z : ℤ) :
    (x ^ 2 + 7 * y ^ 2 - z) + (x ^ 2 + 7 * y ^ 2 + z)
      = 2 * (x ^ 2 + 7 * y ^ 2) := by
  ring

private lemma lj_factor_diff (x y z : ℤ) :
    (x ^ 2 + 7 * y ^ 2 + z) - (x ^ 2 + 7 * y ^ 2 - z) = 2 * z := by
  ring

private lemma sq_eq_one_of_sq_le_one {a : ℤ} (ha0 : a ≠ 0) (h : a ^ 2 ≤ 1) :
    a ^ 2 = 1 := by
  have hnonneg : 0 ≤ a ^ 2 := sq_nonneg a
  have hcases : a ^ 2 = 0 ∨ a ^ 2 = 1 := by omega
  rcases hcases with h0 | h1
  · have : a = 0 := by nlinarith
    exact False.elim (ha0 this)
  · exact h1

private lemma odd_sq_mod8 {a : ℤ} (ha : Odd a) : a ^ 2 % 8 = 1 := by
  rcases Int.eight_dvd_sq_sub_one_of_odd ha with ⟨k, hk⟩
  have : a ^ 2 = 8 * k + 1 := by omega
  rw [this]
  omega

private lemma odd_pow4_mod8 {a : ℤ} (ha : Odd a) : a ^ 4 % 8 = 1 := by
  have hsq : Odd (a ^ 2) := ha.pow
  have h := odd_sq_mod8 hsq
  convert h using 1
  ring_nf

private lemma square_not_three_mod_four (a k : ℤ) (h : a ^ 2 = 4 * k + 3) :
    False := by
  rcases Int.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · have : 4 * b ^ 2 = 4 * k + 3 := by nlinarith
    omega
  · have : 4 * b ^ 2 + 4 * b + 1 = 4 * k + 3 := by nlinarith
    omega

private lemma square_not_seven_mod_eight (a k : ℤ) (h : a ^ 2 = 8 * k + 7) :
    False := by
  rcases Int.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rcases Int.even_or_odd b with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have : 16 * c ^ 2 = 8 * k + 7 := by nlinarith
      omega
    · have : 16 * c ^ 2 + 16 * c + 4 = 8 * k + 7 := by nlinarith
      omega
  · have : 4 * b ^ 2 + 4 * b + 1 = 8 * k + 7 := by nlinarith
    omega

private lemma eq_zero_of_pow4_eq_zero {a : ℤ} (h : a ^ 4 = 0) : a = 0 := by
  have hsq : (a ^ 2) ^ 2 = 0 := by
    nlinarith
  have : a ^ 2 = 0 := by nlinarith [sq_nonneg (a ^ 2)]
  nlinarith

private def MQ (x y : ℤ) : ℤ :=
  x ^ 4 - x ^ 2 * y ^ 2 + y ^ 4

private lemma LQ_to_MQ (x y : ℤ) :
    LQ x y = MQ (x + y) (x - y) := by
  unfold LQ MQ
  ring

private lemma MQ_to_LQ (x y : ℤ) :
    LQ (x + y) (x - y) = 16 * MQ x y := by
  unfold LQ MQ
  ring

private lemma MQ_symm (x y : ℤ) : MQ x y = MQ y x := by
  unfold MQ
  ring

private lemma MQ_abs (x y : ℤ) : MQ |x| |y| = MQ x y := by
  unfold MQ
  rw [sq_abs, sq_abs]
  have hx4 : |x| ^ 4 = x ^ 4 := by
    exact (by norm_num : Even 4).pow_abs x
  have hy4 : |y| ^ 4 = y ^ 4 := by
    exact (by norm_num : Even 4).pow_abs y
  rw [hx4, hy4]

private lemma nat_matrix_factor
    {P Q U V : ℕ} (hPQ : P.Coprime Q) (hUV : U.Coprime V)
    (h : P * Q = U * V) :
    let α := P.gcd U
    let β := P.gcd V
    let γ := Q.gcd U
    let δ := Q.gcd V
    P = α * β ∧ Q = γ * δ ∧ U = α * γ ∧ V = β * δ := by
  dsimp
  have hPdvd : P ∣ U * V := ⟨Q, by rw [← h]⟩
  have hQdvd : Q ∣ U * V := ⟨P, by rw [← h, mul_comm P Q]⟩
  have hUdvd : U ∣ P * Q := ⟨V, h⟩
  have hVdvd : V ∣ P * Q := ⟨U, by rw [h, mul_comm U V]⟩
  have hP : P.gcd U * P.gcd V = P :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hUV).mpr hPdvd
  have hQ : Q.gcd U * Q.gcd V = Q :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hUV).mpr hQdvd
  have hU : U.gcd P * U.gcd Q = U :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hPQ).mpr hUdvd
  have hV : V.gcd P * V.gcd Q = V :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hPQ).mpr hVdvd
  exact ⟨hP.symm, hQ.symm, by simpa [Nat.gcd_comm, mul_comm] using hU.symm,
    by simpa [Nat.gcd_comm, mul_comm] using hV.symm⟩

private lemma mq_pythagorean (p q r : ℤ) (h : r ^ 2 = MQ p q) :
    PythagoreanTriple (p ^ 2 - q ^ 2) (p * q) r := by
  unfold PythagoreanTriple MQ at *
  nlinarith

private lemma coprime_mq_legs (p q : ℤ) (hcop : IsCoprime p q) :
    IsCoprime (p ^ 2 - q ^ 2) (p * q) := by
  have hcop_q_p : IsCoprime q p := hcop.symm
  have hcop_q2_p : IsCoprime (q ^ 2) p := hcop_q_p.pow_left (m := 2)
  have hcop_negq2_p : IsCoprime (-(q ^ 2)) p := by
    rcases hcop_q2_p with ⟨a, b, h⟩
    refine ⟨-a, b, ?_⟩
    nlinarith
  have hcop_diff_p : IsCoprime (p ^ 2 - q ^ 2) p := by
    simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using
      hcop_negq2_p.add_mul_right_left p
  have hcop_p2_q : IsCoprime (p ^ 2) q := hcop.pow_left (m := 2)
  have hcop_diff_q : IsCoprime (p ^ 2 - q ^ 2) q := by
    simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using
      hcop_p2_q.add_mul_right_left (-q)
  exact hcop_diff_p.mul_right hcop_diff_q

private theorem pocklington_tail_from_square_system
    (α β γ δ : ℤ)
    (hαpos : 0 < α) (hβpos : 0 < β) (hδpos : 0 < δ)
    (hcop : Int.gcd α δ = 1)
    (hαodd : Odd α)
    (hbeta : β ^ 2 = α ^ 2 + (2 * δ) ^ 2)
    (hgamma : γ ^ 2 = α ^ 2 + δ ^ 2) :
    ∃ x y z : ℤ,
      x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 ≠ y ^ 2 ∧ Int.gcd x y = 1 ∧
        ((2 : ℤ) ∣ x ∨ (2 : ℤ) ∣ y) ∧ z ^ 2 = MQ x y ∧
        (x * y).natAbs = δ.natAbs := by
  have htrip : PythagoreanTriple α (2 * δ) β := by
    unfold PythagoreanTriple
    nlinarith
  have hcop2δ : Int.gcd α (2 * δ) = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    have hcopαδ : IsCoprime α δ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hcopα2 : IsCoprime α (2 : ℤ) := by
      simpa [isCoprime_comm] using (show IsCoprime (2 : ℤ) α from by simpa using hαodd)
    exact hcopα2.mul_right hcopαδ
  obtain ⟨m, n, hmα, hmn2, _hβ, hmngcd, hmnpar, _hmnonneg⟩ :=
    htrip.coprime_classification' hcop2δ (Int.odd_iff.mp hαodd) hβpos
  have hδmn : δ = m * n := by nlinarith
  have hm_ne : m ≠ 0 := by
    intro hm0
    rw [hm0] at hδmn
    nlinarith
  have hn_ne : n ≠ 0 := by
    intro hn0
    rw [hn0] at hδmn
    nlinarith
  have hsq_ne : m ^ 2 ≠ n ^ 2 := by
    intro hsq
    nlinarith
  have hnew : γ ^ 2 = MQ m n := by
    unfold MQ
    nlinarith
  have heven : (2 : ℤ) ∣ m ∨ (2 : ℤ) ∣ n := by
    rcases hmnpar with hpar | hpar
    · left
      exact Int.dvd_of_emod_eq_zero hpar.1
    · right
      exact Int.dvd_of_emod_eq_zero hpar.2
  refine ⟨m, n, γ, hm_ne, hn_ne, hsq_ne, hmngcd, heven, hnew, ?_⟩
  rw [← hδmn]

private lemma nat_sq_add_coprime_three
    {α δ : ℕ} (hcop : α.Coprime δ) : ¬ (3 ∣ α ^ 2 + δ ^ 2) := by
  intro h3A
  have hAmod : (α ^ 2 + δ ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3A
  have hα : α % 3 = 0 ∨ α % 3 = 1 ∨ α % 3 = 2 := by omega
  have hδ : δ % 3 = 0 ∨ δ % 3 = 1 ∨ δ % 3 = 2 := by omega
  rcases hα with hα | hα | hα <;> rcases hδ with hδ | hδ | hδ
  · have h3α : 3 ∣ α := Nat.dvd_of_mod_eq_zero hα
    have h3δ : 3 ∣ δ := Nat.dvd_of_mod_eq_zero hδ
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3α h3δ) hcop
  all_goals
    have hαsq : α ^ 2 % 3 = (α % 3) ^ 2 % 3 := Nat.pow_mod α 2 3
    have hδsq : δ ^ 2 % 3 = (δ % 3) ^ 2 % 3 := Nat.pow_mod δ 2 3
    rw [Nat.add_mod, hαsq, hδsq, hα, hδ] at hAmod
    norm_num at hAmod

private lemma nat_pocklington_AB_coprime
    {α δ : ℕ} (hcop : α.Coprime δ) :
    (α ^ 2 + δ ^ 2).Coprime (α ^ 2 + (2 * δ) ^ 2) := by
  by_contra hnot
  obtain ⟨p, hp, hpA, hpB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  let A := α ^ 2 + δ ^ 2
  let B := α ^ 2 + (2 * δ) ^ 2
  have htwo : (2 * δ) ^ 2 = 4 * δ ^ 2 := by ring
  have hp3δ : p ∣ 3 * δ ^ 2 := by
    have hsub : p ∣ B - A := Nat.dvd_sub hpB hpA
    convert hsub using 1
    · dsimp [A, B]
      rw [htwo]
      omega
  have hp3α : p ∣ 3 * α ^ 2 := by
    have h4A : p ∣ 4 * A := dvd_mul_of_dvd_right hpA 4
    have hsub : p ∣ 4 * A - B := Nat.dvd_sub h4A hpB
    convert hsub using 1
    · dsimp [A, B]
      rw [htwo]
      omega
  by_cases hp3 : p = 3
  · subst p
    exact nat_sq_add_coprime_three hcop hpA
  · have hpδ : p ∣ δ := by
      have hpδ2 : p ∣ δ ^ 2 := by
        rcases (Nat.Prime.dvd_mul hp).mp hp3δ with hp_dvd3 | hpδ2
        · have hp_eq3 : p = 3 := by
            rcases (Nat.dvd_prime Nat.prime_three).mp hp_dvd3 with hp1 | hp3'
            · exact False.elim (hp.ne_one hp1)
            · exact hp3'
          exact False.elim (hp3 hp_eq3)
        · exact hpδ2
      exact hp.dvd_of_dvd_pow hpδ2
    have hpα : p ∣ α := by
      have hpα2 : p ∣ α ^ 2 := by
        rcases (Nat.Prime.dvd_mul hp).mp hp3α with hp_dvd3 | hpα2
        · have hp_eq3 : p = 3 := by
            rcases (Nat.dvd_prime Nat.prime_three).mp hp_dvd3 with hp1 | hp3'
            · exact False.elim (hp.ne_one hp1)
            · exact hp3'
          exact False.elim (hp3 hp_eq3)
        · exact hpα2
      exact hp.dvd_of_dvd_pow hpα2
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpα hpδ) hcop

private lemma nat_square_system
    (α β γ δ : ℕ)
    (hAB : (α ^ 2 + δ ^ 2).Coprime (α ^ 2 + (2 * δ) ^ 2))
    (hβγ : β.Coprime γ)
    (h : β ^ 2 * (α ^ 2 + δ ^ 2) =
      γ ^ 2 * (α ^ 2 + (2 * δ) ^ 2)) :
    γ ^ 2 = α ^ 2 + δ ^ 2 ∧ β ^ 2 = α ^ 2 + (2 * δ) ^ 2 := by
  let A := α ^ 2 + δ ^ 2
  let B := α ^ 2 + (2 * δ) ^ 2
  have hAB' : A.Coprime B := hAB
  have hβγ2 : (β ^ 2).Coprime (γ ^ 2) := hβγ.pow_left 2 |>.pow_right 2
  have h_order : A * β ^ 2 = γ ^ 2 * B := by
    dsimp [A, B]
    rw [mul_comm]
    exact h
  have hA_dvd_g2 : A ∣ γ ^ 2 := by
    apply hAB'.dvd_of_dvd_mul_right
    refine ⟨β ^ 2, ?_⟩
    rw [h_order, mul_comm]
  have hg2_dvd_A : γ ^ 2 ∣ A := by
    have hdiv : γ ^ 2 ∣ A * β ^ 2 := ⟨B, h_order⟩
    exact hβγ2.symm.dvd_of_dvd_mul_right hdiv
  have hAeq : γ ^ 2 = A := Nat.dvd_antisymm hg2_dvd_A hA_dvd_g2
  have hB_dvd_b2 : B ∣ β ^ 2 := by
    have hdiv : B ∣ β ^ 2 * A := by
      refine ⟨γ ^ 2, ?_⟩
      rw [mul_comm (β ^ 2) A, h_order, mul_comm]
    exact hAB'.symm.dvd_of_dvd_mul_right hdiv
  have hb2_dvd_B : β ^ 2 ∣ B := by
    have hdiv : β ^ 2 ∣ B * γ ^ 2 := by
      refine ⟨A, ?_⟩
      rw [mul_comm B (γ ^ 2), ← h_order, mul_comm]
    exact hβγ2.dvd_of_dvd_mul_right hdiv
  have hBeq : β ^ 2 = B := Nat.dvd_antisymm hb2_dvd_B hB_dvd_b2
  exact ⟨by simpa [A] using hAeq, by simpa [B] using hBeq⟩

private theorem pocklington_even_from_params
    (P Q2 U V : ℕ)
    (_hPpos : 0 < P) (hQ2pos : 0 < Q2) (_hUpos : 0 < U) (_hVpos : 0 < V)
    (hPQ : P.Coprime Q2) (hUV : U.Coprime V)
    (hPodd : P % 2 = 1)
    (hprod : P * Q2 = U * V)
    (hmain : (P : ℤ) ^ 2 - (2 * (Q2 : ℤ)) ^ 2 = (U : ℤ) ^ 2 - (V : ℤ) ^ 2) :
    ∃ x y z : ℤ,
      x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 ≠ y ^ 2 ∧ Int.gcd x y = 1 ∧
        ((2 : ℤ) ∣ x ∨ (2 : ℤ) ∣ y) ∧ z ^ 2 = MQ x y ∧
        (x * y).natAbs < P * (2 * Q2) := by
  let α := P.gcd U
  let β := P.gcd V
  let γ := Q2.gcd U
  let δ := Q2.gcd V
  obtain ⟨hPfac, hQfac, hUfac, hVfac⟩ := nat_matrix_factor hPQ hUV hprod
  have hαpos : 0 < α := by
    by_contra hnot
    have hα0 : α = 0 := by omega
    have hP0 : P = 0 := by
      rw [hPfac]
      dsimp [α] at hα0
      rw [hα0]
      simp
    omega
  have hβpos : 0 < β := by
    by_contra hnot
    have hβ0 : β = 0 := by omega
    have hP0 : P = 0 := by
      rw [hPfac]
      dsimp [β] at hβ0
      rw [hβ0]
      simp
    omega
  have hγpos : 0 < γ := by
    by_contra hnot
    have hγ0 : γ = 0 := by omega
    have hQ0 : Q2 = 0 := by
      rw [hQfac]
      dsimp [γ] at hγ0
      rw [hγ0]
      simp
    omega
  have hδpos : 0 < δ := by
    by_contra hnot
    have hδ0 : δ = 0 := by omega
    have hQ0 : Q2 = 0 := by
      rw [hQfac]
      dsimp [δ] at hδ0
      rw [hδ0]
      simp
    omega
  have hαδ : α.Coprime δ := by
    have hαU : α ∣ U := by
      dsimp [α]
      exact Nat.gcd_dvd_right P U
    have hδV : δ ∣ V := by
      dsimp [δ]
      exact Nat.gcd_dvd_right Q2 V
    exact Nat.Coprime.coprime_dvd_right hδV
      (Nat.Coprime.coprime_dvd_left hαU hUV)
  have hβγ : β.Coprime γ := by
    have hβV : β ∣ V := by
      dsimp [β]
      exact Nat.gcd_dvd_right P V
    have hγU : γ ∣ U := by
      dsimp [γ]
      exact Nat.gcd_dvd_right Q2 U
    exact Nat.Coprime.coprime_dvd_right hγU
      (Nat.Coprime.coprime_dvd_left hβV hUV.symm)
  have hαodd : α % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one α with hαeven | hαodd
    · have hPmod0 : P % 2 = 0 := by
        have hαeven' : (P.gcd U) % 2 = 0 := by
          simpa [α] using hαeven
        rw [hPfac]
        rw [Nat.mul_mod, hαeven']
        norm_num
      omega
    · exact hαodd
  have hcoeffZ : (β : ℤ) ^ 2 * ((α : ℤ) ^ 2 + (δ : ℤ) ^ 2) =
      (γ : ℤ) ^ 2 * ((α : ℤ) ^ 2 + (2 * (δ : ℤ)) ^ 2) := by
    have hmain' : ((α : ℤ) * (β : ℤ)) ^ 2 - (2 * ((γ : ℤ) * (δ : ℤ))) ^ 2 =
        ((α : ℤ) * (γ : ℤ)) ^ 2 - ((β : ℤ) * (δ : ℤ)) ^ 2 := by
      have hPz : (P : ℤ) = (α : ℤ) * (β : ℤ) := by
        exact_mod_cast hPfac
      have hQz : (Q2 : ℤ) = (γ : ℤ) * (δ : ℤ) := by
        exact_mod_cast hQfac
      have hUz : (U : ℤ) = (α : ℤ) * (γ : ℤ) := by
        exact_mod_cast hUfac
      have hVz : (V : ℤ) = (β : ℤ) * (δ : ℤ) := by
        exact_mod_cast hVfac
      simpa [hPz, hQz, hUz, hVz, mul_assoc] using hmain
    nlinarith
  have hcoeffN : β ^ 2 * (α ^ 2 + δ ^ 2) =
      γ ^ 2 * (α ^ 2 + (2 * δ) ^ 2) := by
    exact_mod_cast hcoeffZ
  obtain ⟨hγsq, hβsq⟩ :=
    nat_square_system α β γ δ (nat_pocklington_AB_coprime hαδ) hβγ hcoeffN
  have hcopZ : Int.gcd (α : ℤ) (δ : ℤ) = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hαδ
  have hαoddZ : Odd (α : ℤ) := by
    rw [Int.odd_iff]
    exact_mod_cast hαodd
  have hβsqZ : (β : ℤ) ^ 2 = (α : ℤ) ^ 2 + (2 * (δ : ℤ)) ^ 2 := by
    exact_mod_cast hβsq
  have hγsqZ : (γ : ℤ) ^ 2 = (α : ℤ) ^ 2 + (δ : ℤ) ^ 2 := by
    exact_mod_cast hγsq
  obtain ⟨x, y, z, hx, hy, hxy, hgcd, heven, hz, hxyδ⟩ :=
    pocklington_tail_from_square_system (α : ℤ) (β : ℤ) (γ : ℤ) (δ : ℤ)
      (by exact_mod_cast hαpos) (by exact_mod_cast hβpos) (by exact_mod_cast hδpos)
      hcopZ hαoddZ hβsqZ hγsqZ
  refine ⟨x, y, z, hx, hy, hxy, hgcd, heven, hz, ?_⟩
  rw [hxyδ]
  have hδnat : (δ : ℤ).natAbs = δ := by simp
  rw [hδnat]
  have hfacDrop : P * (2 * Q2) = δ * (2 * (α * β * γ)) := by
    rw [hPfac, hQfac]
    dsimp [α, β, γ, δ]
    ring
  rw [hfacDrop]
  nlinarith [hδpos, hαpos, hβpos, hγpos]

private theorem pocklington_even_descent_step
    (p q r : ℤ)
    (hp : 0 < p) (hq : 0 < q)
    (_hpq_ne : p ^ 2 ≠ q ^ 2)
    (hcop : Int.gcd p q = 1)
    (hqeven : (2 : ℤ) ∣ q)
    (h : r ^ 2 = MQ p q) :
    ∃ x y z : ℤ,
      x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 ≠ y ^ 2 ∧ Int.gcd x y = 1 ∧
        ((2 : ℤ) ∣ x ∨ (2 : ℤ) ∣ y) ∧ z ^ 2 = MQ x y ∧
        (x * y).natAbs < (p * q).natAbs := by
  have hcopI : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hp_odd : Odd p := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hp2
    have h2gcd : (2 : ℤ) ∣ (Int.gcd p q : ℤ) := Int.dvd_coe_gcd hp2 hqeven
    rw [hcop] at h2gcd
    norm_num at h2gcd
  let R : ℤ := r.natAbs
  have hR_sq : R ^ 2 = r ^ 2 := by
    dsimp [R]
    rw [Int.natCast_natAbs]
    exact sq_abs r
  have hmq_pos : 0 < MQ p q := by
    have hpqpos : 0 < p * q := mul_pos hp hq
    have hmq_alt : MQ p q = (p ^ 2 - q ^ 2) ^ 2 + (p * q) ^ 2 := by
      unfold MQ
      ring
    rw [hmq_alt]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hpqpos)
  have hr_ne : r ≠ 0 := by
    intro hr0
    rw [hr0] at h
    nlinarith
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast Int.natAbs_pos.mpr hr_ne
  have hR : R ^ 2 = MQ p q := by
    rw [hR_sq]
    exact h
  have htrip : PythagoreanTriple (p ^ 2 - q ^ 2) (p * q) R :=
    mq_pythagorean p q R hR
  have hlegcop : Int.gcd (p ^ 2 - q ^ 2) (p * q) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (coprime_mq_legs p q hcopI)
  have hparity : (p ^ 2 - q ^ 2) % 2 = 1 := by
    have hp2_odd : Odd (p ^ 2) := hp_odd.pow
    have hq2_even : Even (q ^ 2) := by
      rw [even_iff_two_dvd]
      exact dvd_pow hqeven (by norm_num : (2 : ℕ) ≠ 0)
    exact Int.odd_iff.mp (hp2_odd.sub_even hq2_even)
  obtain ⟨u, v, huv_diff, hpq_uv, _hRuv, hugcd, _huvpar, hunonneg⟩ :=
    htrip.coprime_classification' hlegcop hparity hRpos
  have hpqpos : 0 < p * q := mul_pos hp hq
  have huvprod_pos : 0 < u * v := by nlinarith
  have hupos : 0 < u := by
    by_cases hu0 : u = 0
    · rw [hu0] at huvprod_pos
      nlinarith
    · omega
  have hvpos : 0 < v := by
    by_contra hnot
    have hvle : v ≤ 0 := by omega
    have hprod_nonpos : u * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hupos.le hvle
    nlinarith
  rcases hqeven with ⟨q2, hqeq⟩
  have hqeq' : q = 2 * q2 := hqeq
  have hq2pos : 0 < q2 := by nlinarith
  let P : ℕ := p.natAbs
  let Q2 : ℕ := q2.natAbs
  let U : ℕ := u.natAbs
  let V : ℕ := v.natAbs
  have hPz : (P : ℤ) = p := by
    dsimp [P]
    exact Int.ofNat_natAbs_of_nonneg hp.le
  have hQ2z : (Q2 : ℤ) = q2 := by
    dsimp [Q2]
    exact Int.ofNat_natAbs_of_nonneg hq2pos.le
  have hUz : (U : ℤ) = u := by
    dsimp [U]
    exact Int.ofNat_natAbs_of_nonneg hupos.le
  have hVz : (V : ℤ) = v := by
    dsimp [V]
    exact Int.ofNat_natAbs_of_nonneg hvpos.le
  have hPpos : 0 < P := by
    dsimp [P]
    exact Int.natAbs_pos.mpr (ne_of_gt hp)
  have hQ2pos : 0 < Q2 := by
    dsimp [Q2]
    exact Int.natAbs_pos.mpr (ne_of_gt hq2pos)
  have hUpos : 0 < U := by
    dsimp [U]
    exact Int.natAbs_pos.mpr (ne_of_gt hupos)
  have hVpos : 0 < V := by
    dsimp [V]
    exact Int.natAbs_pos.mpr (ne_of_gt hvpos)
  have hqnat : q.natAbs = 2 * Q2 := by
    dsimp [Q2]
    rw [hqeq', Int.natAbs_mul]
    norm_num
  have hPQfull : P.Coprime q.natAbs := by
    simpa [P] using (Int.isCoprime_iff_nat_coprime.mp hcopI)
  have hQ2dvd : Q2 ∣ q.natAbs := by
    refine ⟨2, ?_⟩
    rw [hqnat, mul_comm]
  have hPQ : P.Coprime Q2 :=
    Nat.Coprime.coprime_dvd_right hQ2dvd hPQfull
  have hUV : U.Coprime V := by
    have huvI : IsCoprime u v := Int.isCoprime_iff_gcd_eq_one.mpr hugcd
    simpa [U, V] using (Int.isCoprime_iff_nat_coprime.mp huvI)
  have hPodd : P % 2 = 1 := by
    have hP_odd : Odd (P : ℤ) := by
      rwa [hPz]
    have hPmod : (P : ℤ) % 2 = 1 := Int.odd_iff.mp hP_odd
    exact_mod_cast hPmod
  have hprodZ : p * q2 = u * v := by
    rw [hqeq'] at hpq_uv
    nlinarith
  have hprod : P * Q2 = U * V := by
    have hprodZ' : (P : ℤ) * (Q2 : ℤ) = (U : ℤ) * (V : ℤ) := by
      rw [hPz, hQ2z, hUz, hVz]
      exact hprodZ
    exact_mod_cast hprodZ'
  have hmain : (P : ℤ) ^ 2 - (2 * (Q2 : ℤ)) ^ 2 =
      (U : ℤ) ^ 2 - (V : ℤ) ^ 2 := by
    rw [hPz, hQ2z, hUz, hVz, ← hqeq']
    exact huv_diff
  obtain ⟨x, y, z, hx, hy, hxy, hgcd, heven, hz, hdrop⟩ :=
    pocklington_even_from_params P Q2 U V hPpos hQ2pos hUpos hVpos hPQ hUV hPodd
      hprod hmain
  refine ⟨x, y, z, hx, hy, hxy, hgcd, heven, hz, ?_⟩
  have hpqnat : (p * q).natAbs = P * (2 * Q2) := by
    rw [Int.natAbs_mul, hqnat]
  rw [hpqnat]
  exact hdrop

private theorem mq_even_no_sol_aux :
    ∀ n : ℕ, ∀ p q r : ℤ,
      (p * q).natAbs ≤ n →
      p ≠ 0 → q ≠ 0 → p ^ 2 ≠ q ^ 2 → Int.gcd p q = 1 →
      ((2 : ℤ) ∣ p ∨ (2 : ℤ) ∣ q) →
      r ^ 2 = MQ p q → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p q r hpqn hp0 hq0 hpq_ne hcop heven h
      rcases heven with hp_even | hq_even
      · let P : ℤ := |q|
        let Q : ℤ := |p|
        have hPpos : 0 < P := by
          dsimp [P]
          exact abs_pos.mpr hq0
        have hQpos : 0 < Q := by
          dsimp [Q]
          exact abs_pos.mpr hp0
        have hneq : P ^ 2 ≠ Q ^ 2 := by
          intro hsq
          apply hpq_ne
          dsimp [P, Q] at hsq
          rw [sq_abs, sq_abs] at hsq
          exact hsq.symm
        have hgcd : Int.gcd P Q = 1 := by
          dsimp [P, Q]
          rw [Int.gcd_comm]
          simpa [Int.gcd_def, Int.natAbs_abs] using hcop
        have hQeven : (2 : ℤ) ∣ Q := by
          dsimp [Q]
          rwa [dvd_abs]
        have hnorm : r ^ 2 = MQ P Q := by
          dsimp [P, Q]
          rw [MQ_abs, MQ_symm]
          exact h
        obtain ⟨x, y, z, hx, hy, hxy, hgcd', heven', hz, hdrop⟩ :=
          pocklington_even_descent_step P Q r hPpos hQpos hneq hgcd hQeven hnorm
        have hprod_norm : (P * Q).natAbs = (p * q).natAbs := by
          dsimp [P, Q]
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_abs, Int.natAbs_abs, mul_comm]
        exact ih (x * y).natAbs (by omega) x y z le_rfl hx hy hxy hgcd' heven' hz
      · let P : ℤ := |p|
        let Q : ℤ := |q|
        have hPpos : 0 < P := by
          dsimp [P]
          exact abs_pos.mpr hp0
        have hQpos : 0 < Q := by
          dsimp [Q]
          exact abs_pos.mpr hq0
        have hneq : P ^ 2 ≠ Q ^ 2 := by
          intro hsq
          apply hpq_ne
          dsimp [P, Q] at hsq
          rwa [sq_abs, sq_abs] at hsq
        have hgcd : Int.gcd P Q = 1 := by
          dsimp [P, Q]
          simpa [Int.gcd_def, Int.natAbs_abs] using hcop
        have hQeven : (2 : ℤ) ∣ Q := by
          dsimp [Q]
          rwa [dvd_abs]
        have hnorm : r ^ 2 = MQ P Q := by
          dsimp [P, Q]
          rw [MQ_abs]
          exact h
        obtain ⟨x, y, z, hx, hy, hxy, hgcd', heven', hz, hdrop⟩ :=
          pocklington_even_descent_step P Q r hPpos hQpos hneq hgcd hQeven hnorm
        have hprod_norm : (P * Q).natAbs = (p * q).natAbs := by
          dsimp [P, Q]
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_abs, Int.natAbs_abs]
        exact ih (x * y).natAbs (by omega) x y z le_rfl hx hy hxy hgcd' heven' hz

private theorem mq_even_no_sol
    (p q r : ℤ)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpq_ne : p ^ 2 ≠ q ^ 2)
    (hcop : Int.gcd p q = 1)
    (heven : (2 : ℤ) ∣ p ∨ (2 : ℤ) ∣ q)
    (h : r ^ 2 = MQ p q) : False :=
  mq_even_no_sol_aux (p * q).natAbs p q r le_rfl hp0 hq0 hpq_ne hcop heven h

private theorem coprime_product_eq_square
    (X Y q : ℤ)
    (hXpos : 0 < X)
    (hYpos : 0 < Y)
    (hqpos : 0 < q)
    (hcop : IsCoprime X Y)
    (hXY : X * Y = q ^ 2) :
    ∃ m n : ℤ,
      X = m ^ 2 ∧
      Y = n ^ 2 ∧
      m * n = q ∧
      0 < m ∧
      0 < n := by
  obtain ⟨m0, hm0assoc⟩ :=
    exists_associated_pow_of_mul_eq_pow' (R := ℤ) (a := X) (b := Y) (c := q)
      hcop (k := 2) hXY
  obtain ⟨n0, hn0assoc⟩ :=
    exists_associated_pow_of_mul_eq_pow' (R := ℤ) (a := Y) (b := X) (c := q)
      hcop.symm (k := 2) (by simpa [mul_comm] using hXY)
  let m : ℤ := m0.natAbs
  let n : ℤ := n0.natAbs
  have hmAbs : (m0 ^ 2).natAbs = X.natAbs :=
    Int.natAbs_eq_iff_associated.mpr hm0assoc
  have hnAbs : (n0 ^ 2).natAbs = Y.natAbs :=
    Int.natAbs_eq_iff_associated.mpr hn0assoc
  have hmX : X = m ^ 2 := by
    calc
      X = (X.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_nonneg hXpos.le]
      _ = ((m0 ^ 2).natAbs : ℤ) := by rw [hmAbs]
      _ = m ^ 2 := by
        dsimp [m]
        rw [Int.natAbs_pow]
        norm_num
  have hnY : Y = n ^ 2 := by
    calc
      Y = (Y.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_nonneg hYpos.le]
      _ = ((n0 ^ 2).natAbs : ℤ) := by rw [hnAbs]
      _ = n ^ 2 := by
        dsimp [n]
        rw [Int.natAbs_pow]
        norm_num
  have hmpos : 0 < m := by
    dsimp [m]
    have hmne : m0 ≠ 0 := by
      intro hmzero
      have hX0 : X = 0 := by
        subst m0
        dsimp [m] at hmX
        nlinarith [hmX]
      omega
    exact_mod_cast Int.natAbs_pos.mpr hmne
  have hnpos : 0 < n := by
    dsimp [n]
    have hnne : n0 ≠ 0 := by
      intro hnzero
      have hY0 : Y = 0 := by
        subst n0
        dsimp [n] at hnY
        nlinarith [hnY]
      omega
    exact_mod_cast Int.natAbs_pos.mpr hnne
  have hmn_pow : (m * n) ^ 2 = q ^ 2 := by
    calc
      (m * n) ^ 2 = m ^ 2 * n ^ 2 := by ring
      _ = X * Y := by rw [← hmX, ← hnY]
      _ = q ^ 2 := hXY
  have hmn_nonneg : 0 ≤ m * n := by nlinarith
  have hmn_abs : (m * n).natAbs = q.natAbs :=
    Int.natAbs_eq_iff_sq_eq.mpr hmn_pow
  have hmn : m * n = q :=
    (Int.natAbs_inj_of_nonneg_of_nonneg hmn_nonneg hqpos.le).mp hmn_abs
  exact ⟨m, n, hmX, hnY, hmn, hmpos, hnpos⟩

private lemma isCoprime_four_of_odd {O : ℤ} (hOodd : Odd O) :
    IsCoprime (4 : ℤ) O := by
  have h2O : ¬ (2 : ℤ) ∣ O := by
    simpa [← even_iff_two_dvd, Int.not_even_iff_odd] using hOodd
  have hcop2O : IsCoprime (2 : ℤ) O :=
    (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (2 : ℤ)).coprime_iff_not_dvd.mpr h2O
  simpa using hcop2O.pow_left (m := 2)

private lemma isCoprime_three_of_not_dvd {O : ℤ} (h3O : ¬ (3 : ℤ) ∣ O) :
    IsCoprime (3 : ℤ) O :=
  (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (3 : ℤ)).coprime_iff_not_dvd.mpr h3O

private lemma twelve_dvd_of_three_and_four_dvd {E : ℤ}
    (h3 : (3 : ℤ) ∣ E) (h4 : (4 : ℤ) ∣ E) : (12 : ℤ) ∣ E := by
  rcases h3 with ⟨a, ha⟩
  have h4a : (4 : ℤ) ∣ a := by
    have h4_3a : (4 : ℤ) ∣ 3 * a := by simpa [ha] using h4
    have hcop43 : IsCoprime (4 : ℤ) (3 : ℤ) := by norm_num
    exact hcop43.dvd_of_dvd_mul_right (by simpa [mul_comm] using h4_3a)
  rcases h4a with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [ha, hk]
  ring

private theorem coprime_factor_split_12_fourth
    (E O y : ℤ)
    (hEpos : 0 < E)
    (hOpos : 0 < O)
    (hypos : 0 < y)
    (hOodd : Odd O)
    (hcop : IsCoprime E O)
    (hEO : E * O = 12 * y ^ 4) :
    (∃ m n : ℤ,
      E = 4 * m ^ 4 ∧ O = 3 * n ^ 4 ∧ m * n = y ∧ 0 < m ∧ 0 < n) ∨
    (∃ m n : ℤ,
      E = 12 * m ^ 4 ∧ O = n ^ 4 ∧ m * n = y ∧ 0 < m ∧ 0 < n) := by
  have hcop4O : IsCoprime (4 : ℤ) O := isCoprime_four_of_odd hOodd
  have h4prod : (4 : ℤ) ∣ E * O := by
    rw [hEO]
    exact dvd_mul_of_dvd_left (by norm_num : (4 : ℤ) ∣ 12) (y ^ 4)
  have h4E : (4 : ℤ) ∣ E := hcop4O.dvd_of_dvd_mul_right h4prod
  by_cases h3O : (3 : ℤ) ∣ O
  · left
    rcases h4E with ⟨E1, hE⟩
    rcases h3O with ⟨O1, hO⟩
    have hE1pos : 0 < E1 := by
      rw [hE] at hEpos
      nlinarith
    have hO1pos : 0 < O1 := by
      rw [hO] at hOpos
      nlinarith
    have hE1O1 : E1 * O1 = y ^ 4 := by
      rw [hE, hO] at hEO
      nlinarith
    have hcopE1O1 : IsCoprime E1 O1 := by
      rcases hcop with ⟨r, s, hrs⟩
      refine ⟨4 * r, 3 * s, ?_⟩
      rw [hE, hO] at hrs
      nlinarith
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      Scratch.ChatGPTDropDM1.coprime_product_eq_fourth_power
        E1 O1 y hE1pos hO1pos hypos hcopE1O1 hE1O1
    refine ⟨m, n, ?_, ?_, hmn, hmpos, hnpos⟩
    · rw [hE, hm]
    · rw [hO, hn]
  · right
    have h3prod : (3 : ℤ) ∣ E * O := by
      rw [hEO]
      exact dvd_mul_of_dvd_left (by norm_num : (3 : ℤ) ∣ 12) (y ^ 4)
    have hcop3O : IsCoprime (3 : ℤ) O := isCoprime_three_of_not_dvd h3O
    have h3E : (3 : ℤ) ∣ E := hcop3O.dvd_of_dvd_mul_right h3prod
    have h12E : (12 : ℤ) ∣ E := twelve_dvd_of_three_and_four_dvd h3E h4E
    rcases h12E with ⟨E1, hE⟩
    have hE1pos : 0 < E1 := by
      rw [hE] at hEpos
      nlinarith
    have hE1O : E1 * O = y ^ 4 := by
      rw [hE] at hEO
      nlinarith
    have hcopE1O : IsCoprime E1 O := by
      rcases hcop with ⟨r, s, hrs⟩
      refine ⟨12 * r, s, ?_⟩
      rw [hE] at hrs
      nlinarith
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      Scratch.ChatGPTDropDM1.coprime_product_eq_fourth_power
        E1 O y hE1pos hOpos hypos hcopE1O hE1O
    refine ⟨m, n, ?_, hn, hmn, hmpos, hnpos⟩
    rw [hE, hm]

private theorem coprime_factor_split_3_fourth
    (A B y : ℤ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hypos : 0 < y)
    (hcop : IsCoprime A B)
    (hAB : A * B = 3 * y ^ 4) :
    (∃ m n : ℤ,
      A = 3 * m ^ 4 ∧ B = n ^ 4 ∧ m * n = y ∧ 0 < m ∧ 0 < n) ∨
    (∃ m n : ℤ,
      A = m ^ 4 ∧ B = 3 * n ^ 4 ∧ m * n = y ∧ 0 < m ∧ 0 < n) := by
  have h3prod : (3 : ℤ) ∣ A * B := by
    rw [hAB]
    exact dvd_mul_of_dvd_left (dvd_refl (3 : ℤ)) (y ^ 4)
  rcases Int.Prime.dvd_mul' (p := 3) Nat.prime_three h3prod with h3A | h3B
  · left
    rcases h3A with ⟨A1, hA⟩
    have hA1pos : 0 < A1 := by
      rw [hA] at hApos
      nlinarith
    have hA1B : A1 * B = y ^ 4 := by
      rw [hA] at hAB
      ring_nf at hAB ⊢
      nlinarith
    have hcopA1B : IsCoprime A1 B := by
      rcases hcop with ⟨r, s, hrs⟩
      refine ⟨3 * r, s, ?_⟩
      rw [hA] at hrs
      ring_nf at hrs ⊢
      exact hrs
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      Scratch.ChatGPTDropDM1.coprime_product_eq_fourth_power
        A1 B y hA1pos hBpos hypos hcopA1B hA1B
    refine ⟨m, n, ?_, hn, hmn, hmpos, hnpos⟩
    rw [hA, hm]
    ring
  · right
    rcases h3B with ⟨B1, hB⟩
    have hB1pos : 0 < B1 := by
      rw [hB] at hBpos
      nlinarith
    have hAB1 : A * B1 = y ^ 4 := by
      rw [hB] at hAB
      ring_nf at hAB ⊢
      nlinarith
    have hcopAB1 : IsCoprime A B1 := by
      rcases hcop with ⟨r, s, hrs⟩
      refine ⟨r, 3 * s, ?_⟩
      rw [hB] at hrs
      ring_nf at hrs ⊢
      exact hrs
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      Scratch.ChatGPTDropDM1.coprime_product_eq_fourth_power
        A B1 y hApos hB1pos hypos hcopAB1 hAB1
    refine ⟨m, n, hm, ?_, hmn, hmpos, hnpos⟩
    rw [hB, hn]
    ring

private theorem primitive_lq_no_sol_ordered
    (x y z : ℤ)
    (hx : 0 < x) (hy : 0 < y) (hyx : y ^ 2 < x ^ 2)
    (hcop : Int.gcd x y = 1)
    (h : z ^ 2 = LQ x y) : False := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy_ne : x ^ 2 ≠ y ^ 2 := by omega
  have hcopI : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hLpos : 0 < LQ x y := by
    unfold LQ
    positivity
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at h
    nlinarith
  let Z : ℤ := z.natAbs
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact_mod_cast Int.natAbs_pos.mpr hz0
  have hZsq : Z ^ 2 = z ^ 2 := by
    dsimp [Z]
    rw [Int.natCast_natAbs]
    exact sq_abs z
  have hcop_diff_xy : IsCoprime (x ^ 2 - y ^ 2) (x * y) :=
    coprime_mq_legs x y hcopI
  rcases Int.even_or_odd x with hx_even | hx_odd
  · rcases Int.even_or_odd y with hy_even | hy_odd
    · have h2x : (2 : ℤ) ∣ x := by simpa [even_iff_two_dvd] using hx_even
      have h2y : (2 : ℤ) ∣ y := by simpa [even_iff_two_dvd] using hy_even
      have h2gcd : (2 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd h2x h2y
      rw [hcop] at h2gcd
      norm_num at h2gcd
    · let A : ℤ := x ^ 2 - y ^ 2
      let D : ℤ := 2 * x * y
      have hApos : 0 < A := by dsimp [A]; omega
      have hDpos : 0 < D := by dsimp [D]; nlinarith
      have hAodd : Odd A := by
        dsimp [A]
        have hx2_even : Even (x ^ 2) := by
          rcases hx_even with ⟨a, hxa⟩
          refine ⟨2 * a ^ 2, ?_⟩
          rw [hxa]
          ring
        exact hx2_even.sub_odd (hy_odd.pow)
      have hcopA2 : IsCoprime A (2 : ℤ) := by
        simpa [isCoprime_comm] using (show IsCoprime (2 : ℤ) A from by simpa using hAodd)
      have hcopAD : Int.gcd A D = 1 := by
        apply Int.isCoprime_iff_gcd_eq_one.mp
        dsimp [D]
        simpa [mul_assoc] using hcopA2.mul_right hcop_diff_xy
      have hbeta : Z ^ 2 = A ^ 2 + (2 * D) ^ 2 := by
        dsimp [A, D]
        rw [hZsq, h]
        unfold LQ
        ring
      have hgamma : (x ^ 2 + y ^ 2) ^ 2 = A ^ 2 + D ^ 2 := by
        dsimp [A, D]
        ring
      obtain ⟨p, q, r, hp, hq, hpq, hgcd, heven, hmq, _hdrop⟩ :=
        pocklington_tail_from_square_system A Z (x ^ 2 + y ^ 2) D
          hApos hZpos hDpos hcopAD hAodd hbeta hgamma
      exact mq_even_no_sol p q r hp hq hpq hgcd heven hmq
  · rcases Int.even_or_odd y with hy_even | hy_odd
    · let A : ℤ := x ^ 2 - y ^ 2
      let D : ℤ := 2 * x * y
      have hApos : 0 < A := by dsimp [A]; omega
      have hDpos : 0 < D := by dsimp [D]; nlinarith
      have hAodd : Odd A := by
        dsimp [A]
        have hy2_even : Even (y ^ 2) := by
          rcases hy_even with ⟨a, hya⟩
          refine ⟨2 * a ^ 2, ?_⟩
          rw [hya]
          ring
        exact (hx_odd.pow).sub_even hy2_even
      have hcopA2 : IsCoprime A (2 : ℤ) := by
        simpa [isCoprime_comm] using (show IsCoprime (2 : ℤ) A from by simpa using hAodd)
      have hcopAD : Int.gcd A D = 1 := by
        apply Int.isCoprime_iff_gcd_eq_one.mp
        dsimp [D]
        simpa [mul_assoc] using hcopA2.mul_right hcop_diff_xy
      have hbeta : Z ^ 2 = A ^ 2 + (2 * D) ^ 2 := by
        dsimp [A, D]
        rw [hZsq, h]
        unfold LQ
        ring
      have hgamma : (x ^ 2 + y ^ 2) ^ 2 = A ^ 2 + D ^ 2 := by
        dsimp [A, D]
        ring
      obtain ⟨p, q, r, hp, hq, hpq, hgcd, heven, hmq, _hdrop⟩ :=
        pocklington_tail_from_square_system A Z (x ^ 2 + y ^ 2) D
          hApos hZpos hDpos hcopAD hAodd hbeta hgamma
      exact mq_even_no_sol p q r hp hq hpq hgcd heven hmq
    · have h4dvd : (4 : ℤ) ∣ x ^ 2 - y ^ 2 := by
        rcases hx_odd with ⟨a, hxa⟩
        rcases hy_odd with ⟨b, hyb⟩
        refine ⟨a ^ 2 + a - (b ^ 2 + b), ?_⟩
        rw [hxa, hyb]
        ring
      rcases h4dvd with ⟨d, hd⟩
      have hdpos : 0 < d := by nlinarith
      have h2sum : (2 : ℤ) ∣ x ^ 2 + y ^ 2 := by
        rcases hx_odd with ⟨a, hxa⟩
        rcases hy_odd with ⟨b, hyb⟩
        refine ⟨2 * a ^ 2 + 2 * a + 2 * b ^ 2 + 2 * b + 1, ?_⟩
        rw [hxa, hyb]
        ring
      rcases h2sum with ⟨B, hB⟩
      have hBpos : 0 < B := by nlinarith [sq_pos_of_ne_zero hx0, sq_pos_of_ne_zero hy0]
      have hLexpr : LQ x y = 16 * ((x * y) ^ 2 + d ^ 2) := by
        calc
          LQ x y = (x ^ 2 - y ^ 2) ^ 2 + 16 * (x * y) ^ 2 := by
            unfold LQ
            ring
          _ = 16 * ((x * y) ^ 2 + d ^ 2) := by
            rw [hd]
            ring
      have h16z : (16 : ℤ) ∣ z ^ 2 := by
        rw [h, hLexpr]
        exact dvd_mul_right 16 ((x * y) ^ 2 + d ^ 2)
      have h4z : (4 : ℤ) ∣ z := by
        have hpow : (4 : ℤ) ^ 2 ∣ z ^ 2 := by
          convert h16z using 1
          norm_num
        exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
      rcases h4z with ⟨C, hC⟩
      have halpha_pos : 0 < x * y := mul_pos hx hy
      have halpha_odd : Odd (x * y) := hx_odd.mul hy_odd
      have hcop_d_xy : IsCoprime d (x * y) := by
        rcases hcop_diff_xy with ⟨r, s, hrs⟩
        refine ⟨4 * r, s, ?_⟩
        rw [hd] at hrs
        nlinarith
      have hcop_xy_d : Int.gcd (x * y) d = 1 :=
        Int.isCoprime_iff_gcd_eq_one.mp hcop_d_xy.symm
      have hbeta : B ^ 2 = (x * y) ^ 2 + (2 * d) ^ 2 := by
        nlinarith
      have hgamma : C ^ 2 = (x * y) ^ 2 + d ^ 2 := by
        rw [hC] at h
        rw [hLexpr] at h
        nlinarith
      obtain ⟨p, q, r, hp, hq, hpq, hgcd, heven, hmq, _hdrop⟩ :=
        pocklington_tail_from_square_system (x * y) B C d
          halpha_pos hBpos hdpos hcop_xy_d halpha_odd hbeta hgamma
      exact mq_even_no_sol p q r hp hq hpq hgcd heven hmq

private theorem primitive_lq_no_sol
    (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ^ 2 ≠ y ^ 2)
    (hcop : Int.gcd x y = 1)
    (h : z ^ 2 = LQ x y) : False := by
  let X : ℤ := |x|
  let Y : ℤ := |y|
  have hXpos : 0 < X := by
    dsimp [X]
    exact abs_pos.mpr hx
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact abs_pos.mpr hy
  have hsq_ne : X ^ 2 ≠ Y ^ 2 := by
    intro hsq
    apply hxy
    dsimp [X, Y] at hsq
    rwa [sq_abs, sq_abs] at hsq
  have hcopXY : Int.gcd X Y = 1 := by
    dsimp [X, Y]
    simpa [Int.gcd_def, Int.natAbs_abs] using hcop
  have hXY : z ^ 2 = LQ X Y := by
    dsimp [X, Y]
    rw [LQ_abs]
    exact h
  rcases lt_or_gt_of_ne hsq_ne with hlt | hgt
  · have hYX : z ^ 2 = LQ Y X := by
      rw [LQ_symm]
      exact hXY
    have hcopYX : Int.gcd Y X = 1 := by
      rw [Int.gcd_comm]
      exact hcopXY
    exact primitive_lq_no_sol_ordered Y X z hYpos hXpos hlt hcopYX hYX
  · exact primitive_lq_no_sol_ordered X Y z hXpos hYpos hgt hcopXY hXY

private theorem lq_no_sol
    (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ^ 2 ≠ y ^ 2)
    (h : z ^ 2 = LQ x y) : False := by
  obtain ⟨g, x0, y0, hgpos, hcop, hxg, hyg⟩ :=
    Int.exists_gcd_one' ((Int.gcd_pos_iff (a := x) (b := y)).mpr (Or.inl hx))
  have hgZpos : 0 < (g : ℤ) := by exact_mod_cast hgpos
  have hx0 : x0 ≠ 0 := by
    intro hx00
    apply hx
    rw [hxg, hx00]
    simp
  have hy0 : y0 ≠ 0 := by
    intro hy00
    apply hy
    rw [hyg, hy00]
    simp
  have hxy0 : x0 ^ 2 ≠ y0 ^ 2 := by
    intro hsq
    apply hxy
    have : (x0 * (g : ℤ)) ^ 2 = (y0 * (g : ℤ)) ^ 2 := by
      calc
        (x0 * (g : ℤ)) ^ 2 = x0 ^ 2 * (g : ℤ) ^ 2 := by ring
        _ = y0 ^ 2 * (g : ℤ) ^ 2 := by rw [hsq]
        _ = (y0 * (g : ℤ)) ^ 2 := by ring
    simpa [hxg, hyg] using this
  have hLscale : LQ x y = (g : ℤ) ^ 4 * LQ x0 y0 := by
    rw [hxg, hyg]
    unfold LQ
    ring
  have hg2dvdz : ((g : ℤ) ^ 2) ∣ z := by
    have hpow : ((g : ℤ) ^ 2) ^ 2 ∣ z ^ 2 := by
      rw [h, hLscale]
      refine ⟨LQ x0 y0, ?_⟩
      ring
    exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
  rcases hg2dvdz with ⟨z0, hz0⟩
  have hprim : z0 ^ 2 = LQ x0 y0 := by
    rw [hz0] at h
    rw [hLscale] at h
    have hg4pos : 0 < (g : ℤ) ^ 4 := by positivity
    nlinarith
  exact primitive_lq_no_sol x0 y0 z0 hx0 hy0 hxy0 hcop hprim

end Ljunggren14

open Ljunggren14

theorem not_ljunggren_14 {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ^ 2 ≠ y ^ 2) :
    x ^ 4 + 14 * x ^ 2 * y ^ 2 + y ^ 4 ≠ z ^ 2 := by
  intro h
  have hL : z ^ 2 = Ljunggren14.LQ x y := by
    unfold Ljunggren14.LQ
    nlinarith
  exact Ljunggren14.lq_no_sol x y z hx hy hxy hL
