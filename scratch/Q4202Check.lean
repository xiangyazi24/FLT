import Mathlib
import scratch.FermatFourthDifferenceN16

set_option autoImplicit false

namespace MazurProof.CyclicExclusion16

/-- Four integers are pairwise coprime. -/
structure PairwiseCoprime4 (a b c d : ℤ) : Prop where
  ab : IsCoprime a b
  ac : IsCoprime a c
  ad : IsCoprime a d
  bc : IsCoprime b c
  bd : IsCoprime b d
  cd : IsCoprime c d

namespace PairwiseCoprime4

variable {a b c d : ℤ}

lemma fst_rest (h : PairwiseCoprime4 a b c d) :
    IsCoprime a (b * c * d) := by
  exact (h.ab.mul_right h.ac).mul_right h.ad

lemma snd_rest (h : PairwiseCoprime4 a b c d) :
    IsCoprime b (a * c * d) := by
  exact (h.ab.symm.mul_right h.bc).mul_right h.bd

lemma trd_rest (h : PairwiseCoprime4 a b c d) :
    IsCoprime c (a * b * d) := by
  exact (h.ac.symm.mul_right h.bc.symm).mul_right h.cd

end PairwiseCoprime4

lemma isCoprime_neg_left {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime (-a) b := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨-u, v, ?_⟩
  calc
    (-u) * (-a) + v * b = u * a + v * b := by ring
    _ = 1 := huv

lemma isCoprime_neg_right {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime a (-b) := by
  exact (isCoprime_neg_left h.symm).symm

lemma isCoprime_of_neg_left {a b : ℤ} (h : IsCoprime (-a) b) :
    IsCoprime a b := by
  simpa only [neg_neg] using isCoprime_neg_left h

lemma isCoprime_of_neg_right {a b : ℤ} (h : IsCoprime a (-b)) :
    IsCoprime a b := by
  simpa only [neg_neg] using isCoprime_neg_right h

lemma signedSquare_factor_fst {a b c d z : ℤ}
    (hp : PairwiseCoprime4 a b c d)
    (hz : z ^ 2 = a * b * c * d) :
    ∃ t : ℤ, a = t ^ 2 ∨ a = -(t ^ 2) := by
  apply Int.sq_of_isCoprime hp.fst_rest
  calc
    a * (b * c * d) = a * b * c * d := by ring
    _ = z ^ 2 := hz.symm

lemma signedSquare_factor_snd {a b c d z : ℤ}
    (hp : PairwiseCoprime4 a b c d)
    (hz : z ^ 2 = a * b * c * d) :
    ∃ t : ℤ, b = t ^ 2 ∨ b = -(t ^ 2) := by
  apply Int.sq_of_isCoprime hp.snd_rest
  calc
    b * (a * c * d) = a * b * c * d := by ring
    _ = z ^ 2 := hz.symm

lemma signedSquare_factor_trd {a b c d z : ℤ}
    (hp : PairwiseCoprime4 a b c d)
    (hz : z ^ 2 = a * b * c * d) :
    ∃ t : ℤ, c = t ^ 2 ∨ c = -(t ^ 2) := by
  apply Int.sq_of_isCoprime hp.trd_rest
  calc
    c * (a * b * d) = a * b * c * d := by ring
    _ = z ^ 2 := hz.symm

lemma eq_sq_of_pos_of_eq_sq_or_neg_sq {n t : ℤ} (hn : 0 < n)
    (h : n = t ^ 2 ∨ n = -(t ^ 2)) : n = t ^ 2 := by
  rcases h with h | h
  · exact h
  · exfalso
    nlinarith [sq_nonneg t]

/-- The imported twice-square endpoint is exactly the final infinite-descent
    contradiction for the non-diagonal branch. -/
theorem quarticMean_trivial {a b c : ℤ}
    (hab : IsCoprime a b) (ha : Odd a) (hb : Odd b)
    (h : a ^ 4 + b ^ 4 = 2 * c ^ 2) : a ^ 2 = b ^ 2 := by
  by_contra hne
  exact no_twice_square_fourth_difference ⟨a, b, c, hab, ha, hb, h, hne⟩

def Q16 (M N : ℤ) : ℤ := M ^ 2 + N ^ 2

def R16 (M N : ℤ) : ℤ := M ^ 2 + 2 * M * N - N ^ 2

lemma coprime_M_Q16 {M N : ℤ} (hMN : IsCoprime M N) :
    IsCoprime M (Q16 M N) := by
  simpa [Q16] using (Int.isCoprime_of_sq_sum hMN.symm).symm

lemma coprime_N_Q16 {M N : ℤ} (hMN : IsCoprime M N) :
    IsCoprime N (Q16 M N) := by
  simpa [Q16, add_comm] using (Int.isCoprime_of_sq_sum hMN).symm

lemma coprime_M_R16 {M N : ℤ} (hMN : IsCoprime M N) :
    IsCoprime M (R16 M N) := by
  have h0 : IsCoprime M (-(N ^ 2)) := isCoprime_neg_right hMN.pow_right
  have h1 := h0.add_mul_left_right (M + 2 * N)
  convert h1 using 1 <;> simp [R16] <;> ring

lemma coprime_N_R16 {M N : ℤ} (hMN : IsCoprime M N) :
    IsCoprime N (R16 M N) := by
  have h0 : IsCoprime N (M ^ 2) := hMN.symm.pow_right
  have h1 := h0.add_mul_left_right (2 * M - N)
  convert h1 using 1 <;> simp [R16] <;> ring

lemma coprime_sub_right {M N : ℤ} (hMN : IsCoprime M N) :
    IsCoprime (M - N) N := by
  convert hMN.add_mul_left_left (-1) using 1 <;> ring

lemma not_both_even_of_isCoprime {M N : ℤ} (hMN : IsCoprime M N) :
    ¬(Even M ∧ Even N) := by
  rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  rcases hMN with ⟨u, v, huv⟩
  apply Int.not_even_one
  refine ⟨u * m + v * n, ?_⟩
  rw [← huv, hm, hn]
  ring

lemma pairwiseCoprime4_of_oppositeParity {M N : ℤ}
    (hMN : IsCoprime M N)
    (hop : (Even M ∧ Odd N) ∨ (Odd M ∧ Even N)) :
    PairwiseCoprime4 M N (Q16 M N) (R16 M N) := by
  have hQodd : Odd (Q16 M N) := by
    rcases hop with ⟨hMe, hNo⟩ | ⟨hMo, hNe⟩
    · simpa [Q16] using hMe.add_odd (hNo.pow)
    · simpa [Q16, add_comm] using hNe.add_odd (hMo.pow)
  have hDodd : Odd (M - N) := by
    rcases hop with ⟨hMe, hNo⟩ | ⟨hMo, hNe⟩
    · exact hMe.sub_odd hNo
    · exact hMo.sub_even hNe
  have hDN : IsCoprime (M - N) N := coprime_sub_right hMN
  have hD2 : IsCoprime (M - N) 2 := Int.isCoprime_two_right.mpr hDodd
  have hDN2 : IsCoprime (M - N) (N ^ 2) := hDN.pow_right
  have hD2N2 : IsCoprime (M - N) (2 * N ^ 2) := hD2.mul_right hDN2
  have hDQ : IsCoprime (M - N) (Q16 M N) := by
    have ht := hD2N2.add_mul_left_right (M + N)
    convert ht using 1 <;> simp [Q16] <;> ring
  have hQ2 : IsCoprime (Q16 M N) 2 := Int.isCoprime_two_right.mpr hQodd
  have hQN : IsCoprime (Q16 M N) N := (coprime_N_Q16 hMN).symm
  have hQD : IsCoprime (Q16 M N) (M - N) := hDQ.symm
  have hQrest : IsCoprime (Q16 M N) (2 * N * (M - N)) := by
    have ht := (hQ2.mul_right hQN).mul_right hQD
    convert ht using 1 <;> ring
  have hQR : IsCoprime (Q16 M N) (R16 M N) := by
    have ht := hQrest.add_mul_left_right 1
    convert ht using 1 <;> simp [Q16, R16] <;> ring
  exact ⟨hMN, coprime_M_Q16 hMN, coprime_M_R16 hMN,
    coprime_N_Q16 hMN, coprime_N_R16 hMN, hQR⟩

lemma oppositeParity_impossible16 {M N W : ℤ}
    (hN : 0 < N) (hMN : IsCoprime M N) (hM0 : M ≠ 0)
    (hop : (Even M ∧ Odd N) ∨ (Odd M ∧ Even N))
    (hW : W ^ 2 = M * N * Q16 M N * R16 M N) : False := by
  let hp : PairwiseCoprime4 M N (Q16 M N) (R16 M N) :=
    pairwiseCoprime4_of_oppositeParity hMN hop
  obtain ⟨a, ha⟩ := signedSquare_factor_fst hp hW
  obtain ⟨b, hb⟩ := signedSquare_factor_snd hp hW
  obtain ⟨c, hc⟩ := signedSquare_factor_trd hp hW
  have hb' : N = b ^ 2 := eq_sq_of_pos_of_eq_sq_or_neg_sq hN hb
  have hQpos : 0 < Q16 M N := by
    unfold Q16
    nlinarith [sq_nonneg M, sq_pos_of_pos hN]
  have hc' : Q16 M N = c ^ 2 := eq_sq_of_pos_of_eq_sq_or_neg_sq hQpos hc
  have ha0 : a ≠ 0 := by
    intro haZero
    rcases ha with ha | ha <;> simp [haZero] at ha <;> exact hM0 ha.symm
  have hb0 : b ≠ 0 := by
    intro hbZero
    rw [hbZero] at hb'
    norm_num at hb'
    linarith
  apply (not_fermat_42 ha0 hb0)
  rcases ha with ha | ha
  · calc
      a ^ 4 + b ^ 4 = M ^ 2 + N ^ 2 := by rw [ha, hb']; ring
      _ = Q16 M N := by rfl
      _ = c ^ 2 := hc'
  · calc
      a ^ 4 + b ^ 4 = M ^ 2 + N ^ 2 := by rw [ha, hb']; ring
      _ = Q16 M N := by rfl
      _ = c ^ 2 := hc'

lemma odd_half_data {M N : ℤ} (hMo : Odd M) (hNo : Odd N) :
    ∃ m n Q0 R0 : ℤ,
      M = 2 * m + 1 ∧ N = 2 * n + 1 ∧
      Q16 M N = 2 * Q0 ∧ R16 M N = 2 * R0 ∧
      Odd Q0 ∧ Odd R0 := by
  rcases hMo with ⟨m, hm⟩
  rcases hNo with ⟨n, hn⟩
  refine ⟨m, n,
    2 * m ^ 2 + 2 * m + 2 * n ^ 2 + 2 * n + 1,
    2 * m ^ 2 + 4 * m * n + 4 * m - 2 * n ^ 2 + 1,
    hm, hn, ?_, ?_, ?_, ?_⟩
  · simp [Q16, hm, hn]
    ring
  · simp [R16, hm, hn]
    ring
  · refine ⟨m ^ 2 + m + n ^ 2 + n, ?_⟩
    ring
  · refine ⟨m ^ 2 + 2 * m * n + 2 * m - n ^ 2, ?_⟩
    ring

lemma pairwiseCoprime4_odd_halves {M N m n Q0 R0 : ℤ}
    (hMN : IsCoprime M N)
    (hM : M = 2 * m + 1) (hN : N = 2 * n + 1)
    (hQ : Q16 M N = 2 * Q0) (hR : R16 M N = 2 * R0)
    (hQodd : Odd Q0) (hRodd : Odd R0) :
    PairwiseCoprime4 M N Q0 R0 := by
  have hMQ : IsCoprime M (Q16 M N) := coprime_M_Q16 hMN
  have hNQ : IsCoprime N (Q16 M N) := coprime_N_Q16 hMN
  have hMR : IsCoprime M (R16 M N) := coprime_M_R16 hMN
  have hNR : IsCoprime N (R16 M N) := coprime_N_R16 hMN
  have hQdvd : Q0 ∣ Q16 M N := ⟨2, by rw [hQ]; ring⟩
  have hRdvd : R0 ∣ R16 M N := ⟨2, by rw [hR]; ring⟩
  have hMQ0 : IsCoprime M Q0 := hMQ.of_isCoprime_of_dvd_right hQdvd
  have hNQ0 : IsCoprime N Q0 := hNQ.of_isCoprime_of_dvd_right hQdvd
  have hMR0 : IsCoprime M R0 := hMR.of_isCoprime_of_dvd_right hRdvd
  have hNR0 : IsCoprime N R0 := hNR.of_isCoprime_of_dvd_right hRdvd
  have hDN : IsCoprime (M - N) N := coprime_sub_right hMN
  have hDN2 : IsCoprime (M - N) (N ^ 2) := hDN.pow_right
  have hDQ0 : IsCoprime (M - N) Q0 := by
    have ht := hDN2.add_mul_left_right (m + n + 1)
    convert ht using 1 <;> simp [hM, hN, hQ, Q16] <;> ring
  have hQ0N : IsCoprime Q0 N := hNQ0.symm
  have hQ0D : IsCoprime Q0 (M - N) := hDQ0.symm
  have hQ0ND : IsCoprime Q0 (N * (M - N)) := hQ0N.mul_right hQ0D
  have hQ0R0 : IsCoprime Q0 R0 := by
    have ht := hQ0ND.add_mul_left_right 1
    convert ht using 1 <;> simp [hQ, hR, Q16, R16] <;> ring
  exact ⟨hMN, hMQ0, hMR0, hNQ0, hNR0, hQ0R0⟩

lemma odd_product_square16 {M N W m n Q0 R0 : ℤ}
    (hM : M = 2 * m + 1) (hN : N = 2 * n + 1)
    (hQ : Q16 M N = 2 * Q0) (hR : R16 M N = 2 * R0)
    (hW : W ^ 2 = M * N * Q16 M N * R16 M N) :
    ∃ W0 : ℤ, W0 ^ 2 = M * N * Q0 * R0 := by
  have h2Wsq : (2 : ℤ) ∣ W ^ 2 := by
    refine ⟨2 * M * N * Q0 * R0, ?_⟩
    rw [hW, hQ, hR]
    ring
  have h2W : (2 : ℤ) ∣ W := Int.Prime.dvd_pow' Nat.prime_two h2Wsq
  rcases h2W with ⟨W0, hW0⟩
  refine ⟨W0, ?_⟩
  rw [hW0, hQ, hR] at hW
  nlinarith

lemma odd_branch16 {M N W : ℤ}
    (hN : 0 < N) (hMN : IsCoprime M N)
    (hMo : Odd M) (hNo : Odd N)
    (hW : W ^ 2 = M * N * Q16 M N * R16 M N) :
    M = N ∨ M = -N := by
  obtain ⟨m, n, Q0, R0, hM, hNrep, hQ, hR, hQodd, hRodd⟩ :=
    odd_half_data hMo hNo
  let hp : PairwiseCoprime4 M N Q0 R0 :=
    pairwiseCoprime4_odd_halves hMN hM hNrep hQ hR hQodd hRodd
  obtain ⟨W0, hW0⟩ := odd_product_square16 hM hNrep hQ hR hW
  obtain ⟨a, ha⟩ := signedSquare_factor_fst hp hW0
  obtain ⟨b, hb⟩ := signedSquare_factor_snd hp hW0
  obtain ⟨c, hc⟩ := signedSquare_factor_trd hp hW0
  have hb' : N = b ^ 2 := eq_sq_of_pos_of_eq_sq_or_neg_sq hN hb
  have hQ0pos : 0 < Q0 := by
    have hQpos : 0 < Q16 M N := by
      unfold Q16
      nlinarith [sq_nonneg M, sq_pos_of_pos hN]
    nlinarith
  have hc' : Q0 = c ^ 2 := eq_sq_of_pos_of_eq_sq_or_neg_sq hQ0pos hc
  rcases ha with ha | ha
  · have habsq : IsCoprime (a ^ 2) (b ^ 2) := by simpa [ha, hb'] using hMN
    have hab : IsCoprime a b :=
      (IsCoprime.pow_iff (m := 2) (n := 2) (by decide) (by decide)).mp habsq
    have haodd : Odd a := by
      apply (Int.odd_pow' (m := a) (n := 2) (by decide)).mp
      simpa [ha] using hMo
    have hbodd : Odd b := by
      apply (Int.odd_pow' (m := b) (n := 2) (by decide)).mp
      simpa [hb'] using hNo
    have hmean : a ^ 4 + b ^ 4 = 2 * c ^ 2 := by
      calc
        a ^ 4 + b ^ 4 = Q16 M N := by rw [ha, hb']; unfold Q16; ring
        _ = 2 * Q0 := hQ
        _ = 2 * c ^ 2 := by rw [hc']
    left
    rw [ha, hb', quarticMean_trivial hab haodd hbodd hmean]
  · have habsq0 : IsCoprime (-(a ^ 2)) (b ^ 2) := by simpa [ha, hb'] using hMN
    have habsq : IsCoprime (a ^ 2) (b ^ 2) := isCoprime_of_neg_left habsq0
    have hab : IsCoprime a b :=
      (IsCoprime.pow_iff (m := 2) (n := 2) (by decide) (by decide)).mp habsq
    have haodd : Odd a := by
      apply (Int.odd_pow' (m := a) (n := 2) (by decide)).mp
      have : Odd (-(a ^ 2)) := by simpa [ha] using hMo
      exact (odd_neg.mp this)
    have hbodd : Odd b := by
      apply (Int.odd_pow' (m := b) (n := 2) (by decide)).mp
      simpa [hb'] using hNo
    have hmean : a ^ 4 + b ^ 4 = 2 * c ^ 2 := by
      calc
        a ^ 4 + b ^ 4 = Q16 M N := by rw [ha, hb']; unfold Q16; ring
        _ = 2 * Q0 := hQ
        _ = 2 * c ^ 2 := by rw [hc']
    right
    rw [ha, hb', quarticMean_trivial hab haodd hbodd hmean]

/-- Primitive integer points on the denominator-cleared `C16` model. -/
theorem primitive_product16 {M N W : ℤ}
    (hN : 0 < N) (hMN : IsCoprime M N)
    (hW : W ^ 2 = M * N * (M ^ 2 + N ^ 2) *
      (M ^ 2 + 2 * M * N - N ^ 2)) :
    M = 0 ∨ M = N ∨ M = -N := by
  have hW' : W ^ 2 = M * N * Q16 M N * R16 M N := by
    simpa [Q16, R16] using hW
  by_cases hM0 : M = 0
  · exact Or.inl hM0
  rcases Int.even_or_odd M with hMe | hMo
  · rcases Int.even_or_odd N with hNe | hNo
    · exfalso
      exact not_both_even_of_isCoprime hMN ⟨hMe, hNe⟩
    · exfalso
      exact oppositeParity_impossible16 hN hMN hM0 (Or.inl ⟨hMe, hNo⟩) hW'
  · rcases Int.even_or_odd N with hNe | hNo
    · exfalso
      exact oppositeParity_impossible16 hN hMN hM0 (Or.inr ⟨hMo, hNe⟩) hW'
    · rcases odd_branch16 hN hMN hMo hNo hW' with hEq | hEq
      · exact Or.inr (Or.inl hEq)
      · exact Or.inr (Or.inr hEq)

/-- A rational whose square is an integer is an integer. -/
theorem rat_isInt_of_sq_isInt (r : ℚ) (k : ℤ)
    (h : r ^ 2 = (k : ℚ)) : ∃ z : ℤ, r = z := by
  have hden : r.den * r.den = 1 := by
    have hd := congrArg Rat.den h
    simpa [pow_two, Rat.mul_self_den] using hd
  have hdone : r.den = 1 := (Nat.mul_eq_one.mp hden).1
  refine ⟨r.num, ?_⟩
  rw [← Rat.num_divInt_den r, hdone]
  simp

/-- The only rational `u`-coordinates on the odd-degree model are `-1,0,1`. -/
theorem C16_rational_u {u v : ℚ}
    (h : v ^ 2 = u * (u ^ 2 + 1) * (u ^ 2 + 2 * u - 1)) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  let M : ℤ := u.num
  let N : ℤ := u.den
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast u.den_pos
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hMN : IsCoprime M N := by
    dsimp [M, N]
    exact Rat.isCoprime_num_den u
  have hu : u = (M : ℚ) / (N : ℚ) := by
    dsimp [M, N]
    exact (Rat.num_div_den u).symm
  let wq : ℚ := (N : ℚ) ^ 3 * v
  have hwq : wq ^ 2 = ((M * N * Q16 M N * R16 M N : ℤ) : ℚ) := by
    dsimp [wq]
    rw [h, hu]
    field_simp [show (N : ℚ) ≠ 0 by exact_mod_cast hN0]
    simp [Q16, R16]
    ring
  obtain ⟨W, hWrat⟩ := rat_isInt_of_sq_isInt wq (M * N * Q16 M N * R16 M N) hwq
  have hWint : W ^ 2 = M * N * Q16 M N * R16 M N := by
    rw [hWrat] at hwq
    exact_mod_cast hwq
  rcases primitive_product16 hN hMN (by simpa [Q16, R16] using hWint) with hM0 | hMN' | hMneg
  · right
    left
    rw [hu, hM0]
    simp
  · right
    right
    rw [hu, hMN']
    field_simp [show (N : ℚ) ≠ 0 by exact_mod_cast hN0]
  · left
    rw [hu, hMneg]
    field_simp [show (N : ℚ) ≠ 0 by exact_mod_cast hN0]


def A16 (x : ℚ) : ℚ := x ^ 3 + x ^ 2 - x + 1

def sextic16 (x : ℚ) : ℚ :=
  (x ^ 2 - 1) * (x ^ 2 + 1) * (x ^ 2 + 2 * x - 1)

lemma complete_square16_identity (x y : ℚ) :
    (2 * y + A16 x) ^ 2 - sextic16 x =
      4 * (y ^ 2 + A16 x * y + x ^ 2) := by
  unfold A16 sextic16
  ring

lemma mobius16_identity (x z : ℚ) (hx : 1 + x ≠ 0) :
    (2 * z / (1 + x) ^ 3) ^ 2 -
      ((1 - x) / (1 + x)) * (((1 - x) / (1 + x)) ^ 2 + 1) *
        (((1 - x) / (1 + x)) ^ 2 + 2 * ((1 - x) / (1 + x)) - 1) =
      4 * (z ^ 2 - sextic16 x) / (1 + x) ^ 6 := by
  unfold sextic16
  field_simp [hx]
  ring

/-- The affine rational points on Sutherland's optimized `X_1(16)` model. -/
theorem X16_affine_rational_points {x y : ℚ}
    (h : y ^ 2 + (x ^ 3 + x ^ 2 - x + 1) * y + x ^ 2 = 0) :
    (x = -1 ∧ y = -1) ∨
      (x = 0 ∧ (y = 0 ∨ y = -1)) ∨
      (x = 1 ∧ y = -1) := by
  by_cases hxneg : x = -1
  · left
    refine ⟨hxneg, ?_⟩
    rw [hxneg] at h
    norm_num at h
    nlinarith [sq_nonneg (y + 1)]
  have hxden : 1 + x ≠ 0 := by
    intro hx
    apply hxneg
    linarith
  let z : ℚ := 2 * y + A16 x
  have hz : z ^ 2 = sextic16 x := by
    have hi := complete_square16_identity x y
    dsimp [z]
    have hcurve : y ^ 2 + A16 x * y + x ^ 2 = 0 := by
      simpa [A16] using h
    rw [hcurve] at hi
    nlinarith
  let u : ℚ := (1 - x) / (1 + x)
  let v : ℚ := 2 * z / (1 + x) ^ 3
  have huv : v ^ 2 = u * (u ^ 2 + 1) * (u ^ 2 + 2 * u - 1) := by
    have hi := mobius16_identity x z hxden
    dsimp [u, v]
    rw [hz] at hi
    simp at hi
    exact sub_eq_zero.mp hi
  rcases C16_rational_u huv with huNeg | huZero | huOne
  · exfalso
    dsimp [u] at huNeg
    field_simp [hxden] at huNeg
    linarith
  · right
    right
    have hxone : x = 1 := by
      dsimp [u] at huZero
      field_simp [hxden] at huZero
      linarith
    refine ⟨hxone, ?_⟩
    rw [hxone] at h
    norm_num at h
    nlinarith [sq_nonneg (y + 1)]
  · right
    left
    have hxzero : x = 0 := by
      dsimp [u] at huOne
      field_simp [hxden] at huOne
      linarith
    refine ⟨hxzero, ?_⟩
    rw [hxzero] at h
    norm_num at h
    have hyprod : y * (y + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hyprod with hy0 | hy1
    · exact Or.inl hy0
    · exact Or.inr (by linarith)

end MazurProof.CyclicExclusion16
