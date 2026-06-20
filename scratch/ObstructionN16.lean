import Mathlib
import scratch.DescentN16
import scratch.DenominatorQuarticN16
import scratch.CoprimeSqDvd
import scratch.IsSquareCube
import scratch.ObstructionComplete

noncomputable section

private lemma eq_sq_of_nonneg_associated_sq {x z : ℤ}
    (hx : 0 ≤ x) (h : Associated x (z ^ 2)) :
    x = z ^ 2 := by
  rcases (Int.associated_iff.mp h) with hpos | hneg
  · exact hpos
  · have hz_nonneg : 0 ≤ z ^ 2 := by nlinarith [sq_nonneg z]
    have hx_nonpos : x ≤ 0 := by
      rw [hneg]
      exact neg_nonpos.mpr hz_nonneg
    have hx0 : x = 0 := le_antisymm hx_nonpos hx
    have hz20 : z ^ 2 = 0 := by
      have hzneg0 : -(z ^ 2) = 0 := by
        simpa [hx0] using hneg.symm
      nlinarith
    rw [hx0, hz20]

private lemma eq_neg_sq_of_nonpos_associated_sq {x z : ℤ}
    (hx : x ≤ 0) (h : Associated x (z ^ 2)) :
    x = -(z ^ 2) := by
  rcases (Int.associated_iff.mp h) with hpos | hneg
  · have hz_nonneg : 0 ≤ z ^ 2 := by nlinarith [sq_nonneg z]
    have hz20 : z ^ 2 = 0 := by nlinarith
    rw [hpos, hz20]
    simp
  · exact hneg

private lemma associated_square_left_of_coprime_square_mul
    {a b r : ℤ} (hab : IsCoprime a b) (h : a * b = r ^ 2) :
    ∃ z : ℤ, Associated a (z ^ 2) := by
  exact (exists_associated_pow_of_mul_eq_pow' hab h).imp (fun d hd => hd.symm)

private lemma nat_coprime_of_int_gcd_eq_one {a b : ℤ}
    (h : Int.gcd a b = 1) :
    Nat.Coprime a.natAbs b.natAbs := by
  simpa [Int.gcd_def, Nat.Coprime] using h

private lemma int_gcd_eq_one_of_nat_coprime {a b : ℤ}
    (h : Nat.Coprime a.natAbs b.natAbs) :
    Int.gcd a b = 1 := by
  simpa [Int.gcd_def, Nat.Coprime] using h

private lemma nat_coprime_curve_M_den_N16
    (p q : ℤ) (hpq : Nat.Coprime p.natAbs q.natAbs) :
    Nat.Coprime (p ^ 2 - p * q - q ^ 2).natAbs q.natAbs := by
  have hpqI : IsCoprime p q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact int_gcd_eq_one_of_nat_coprime hpq
  have hp2qI : IsCoprime (p ^ 2) q := by
    simpa using (hpqI.pow_left : IsCoprime (p ^ 2) q)
  have hM :
      p ^ 2 - p * q - q ^ 2 = p ^ 2 + q * (-p - q) := by ring
  have hI : IsCoprime (p ^ 2 - p * q - q ^ 2) q := by
    rw [hM]
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      hp2qI.add_mul_left_right (-p - q)
  rw [Int.isCoprime_iff_gcd_eq_one] at hI
  exact nat_coprime_of_int_gcd_eq_one hI

private lemma nat_coprime_curve_p_M_N16
    (p q : ℤ) (hpq : Nat.Coprime p.natAbs q.natAbs) :
    IsCoprime p (p ^ 2 - p * q - q ^ 2) := by
  have hpqI : IsCoprime p q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact int_gcd_eq_one_of_nat_coprime hpq
  have hpq2I : IsCoprime p (q ^ 2) := by
    simpa using (hpqI.pow_right : IsCoprime p (q ^ 2))
  have hM :
      p ^ 2 - p * q - q ^ 2 = -(q ^ 2) + p * (p - q) := by ring
  rw [hM]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using
    hpq2I.neg_right.add_mul_right_right (p - q)

private lemma rat_curve_rhs_num_den_N16 (u : ℚ) :
    let p : ℤ := u.num
    let q : ℤ := u.den
    let M : ℤ := p ^ 2 - p * q - q ^ 2
    (u ^ 3 - u ^ 2 - u).num = p * M ∧
      (u ^ 3 - u ^ 2 - u).den = u.den ^ 3 := by
  classical
  let p : ℤ := u.num
  let qN : ℕ := u.den
  let q : ℤ := qN
  let M : ℤ := p ^ 2 - p * q - q ^ 2
  have hqposN : 0 < qN := u.pos
  have hqpos : 0 < q := by
    dsimp [q]
    exact Int.natCast_pos.mpr hqposN
  have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hu : u = (p : ℚ) / (q : ℚ) := by
    dsimp [p, q, qN]
    exact (Rat.num_div_den u).symm
  have hrhs :
      u ^ 3 - u ^ 2 - u =
        ((p * M : ℤ) : ℚ) / ((q ^ 3 : ℤ) : ℚ) := by
    rw [hu]
    field_simp [hq_ne]
    dsimp [M]
    push_cast
    ring
  have hpq : Nat.Coprime p.natAbs q.natAbs := by
    dsimp [p, q, qN]
    simpa [Int.natAbs_natCast] using u.reduced
  have hMq : Nat.Coprime M.natAbs q.natAbs := by
    dsimp [M]
    exact nat_coprime_curve_M_den_N16 p q hpq
  have hpqM : Nat.Coprime (p * M).natAbs q.natAbs := by
    rw [Int.natAbs_mul]
    exact hpq.mul_left hMq
  have hcop_den : Nat.Coprime (p * M).natAbs (q ^ 3).natAbs := by
    have hpow : Nat.Coprime (p * M).natAbs (q.natAbs ^ 3) :=
      hpqM.pow_right 3
    simpa [Int.natAbs_pow] using hpow
  have hq3pos : 0 < q ^ 3 := by positivity
  constructor
  · rw [hrhs]
    exact Rat.num_div_eq_of_coprime hq3pos hcop_den
  · rw [hrhs]
    have hden :=
      Rat.den_div_eq_of_coprime
        (a := p * M) (b := q ^ 3) hq3pos hcop_den
    apply Int.ofNat_inj.1
    simpa [q, qN, Int.natAbs_pow, Int.natAbs_natCast] using hden

private lemma gcd_abs_square_root_of_coprime_square_square
    {a b p q : ℤ}
    (hpq : Nat.Coprime p.natAbs q.natAbs)
    (hp : p = a ^ 2 ∨ p = -(a ^ 2))
    (hq : q = b ^ 2) :
    Int.gcd (|a|) b = 1 := by
  have hpq' : Nat.Coprime (a.natAbs ^ 2) (b.natAbs ^ 2) := by
    rcases hp with hp | hp
    · simpa [hp, hq, Int.natAbs_pow] using hpq
    · simpa [hp, hq, Int.natAbs_pow] using hpq
  have hab1 : Nat.Coprime a.natAbs (b.natAbs ^ 2) := by
    exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) a.natAbs (b.natAbs ^ 2)).mp hpq'
  have hab : Nat.Coprime a.natAbs b.natAbs := by
    exact (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) a.natAbs b.natAbs).mp hab1
  have h_abs_nat : (|a| : ℤ).natAbs = a.natAbs := Int.natAbs_abs a
  simpa [Int.gcd_def, h_abs_nat, Nat.Coprime] using hab

private lemma abs_root_ge_two_of_large_square
    {p a : ℤ} (hlarge : 1 < |p|) (hp : p = a ^ 2 ∨ p = -(a ^ 2)) :
    2 ≤ |a| := by
  have ha_nonneg : 0 ≤ |a| := abs_nonneg a
  have ha_ne_zero : |a| ≠ 0 := by
    intro ha0
    have ha_sq0 : a ^ 2 = 0 := by
      have : a = 0 := by exact abs_eq_zero.mp ha0
      simp [this]
    rcases hp with hp | hp
    · have : |p| = 0 := by simp [hp, ha_sq0]
      omega
    · have : |p| = 0 := by simp [hp, ha_sq0]
      omega
  have ha_ne_one : |a| ≠ 1 := by
    intro ha1
    have ha_sq1 : a ^ 2 = 1 := by
      have hsq_abs : |a| ^ 2 = a ^ 2 := by
        rw [sq_abs]
      nlinarith
    rcases hp with hp | hp
    · have : |p| = 1 := by simp [hp, ha_sq1]
      omega
    · have : |p| = 1 := by simp [hp, ha_sq1]
      omega
  omega

private lemma den_root_ge_two
    {q b : ℤ} {qN : ℕ} (hqN : q = qN) (hden : qN ≠ 1)
    (hb_nonneg : 0 ≤ b) (hqpos : 0 < q) (hq : q = b ^ 2) :
    2 ≤ b := by
  have hb_ne_zero : b ≠ 0 := by
    intro hb0
    have hq0 : q = 0 := by simp [hq, hb0]
    nlinarith
  have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb_ne_zero)
  have hb_ne_one : b ≠ 1 := by
    intro hb1
    have hq1 : q = 1 := by simp [hq, hb1]
    have hqN1 : qN = 1 := by
      apply Int.ofNat_inj.1
      calc
        (qN : ℤ) = q := hqN.symm
        _ = 1 := hq1
    exact hden hqN1
  omega

private lemma curve_point_gives_quartic_N16
    (u w : ℚ) (h : w ^ 2 = u ^ 3 - u ^ 2 - u)
    (hden : u.den ≠ 1) (hlarge : 1 < |u.num|) :
    ∃ P Q T : ℤ, 2 ≤ Q ∧ Int.gcd P Q = 1 ∧
      T ^ 2 = P ^ 4 - P ^ 2 * Q ^ 2 - Q ^ 4 := by
  classical
  let p : ℤ := u.num
  let qN : ℕ := u.den
  let q : ℤ := qN
  let M : ℤ := p ^ 2 - p * q - q ^ 2
  have hqposN : 0 < qN := u.pos
  have hqpos : 0 < q := by
    dsimp [q]
    exact Int.natCast_pos.mpr hqposN
  have hp_large : 1 < |p| := by simpa [p] using hlarge
  have hp_abs_pos : 0 < |p| := lt_trans (by norm_num : (0 : ℤ) < 1) hp_large
  have hp_abs_ne_zero : |p| ≠ 0 := ne_of_gt hp_abs_pos
  have hpq : Nat.Coprime p.natAbs q.natAbs := by
    dsimp [p, q, qN]
    simpa [Int.natAbs_natCast] using u.reduced
  have hnumden := rat_curve_rhs_num_den_N16 u
  have hnumR : (u ^ 3 - u ^ 2 - u).num = p * M := by
    simpa [p, q, qN, M] using hnumden.1
  have hdenR : (u ^ 3 - u ^ 2 - u).den = qN ^ 3 := by
    simpa [p, q, qN, M] using hnumden.2
  have hsR : IsSquare (u ^ 3 - u ^ 2 - u) := by
    exact ⟨w, by simpa [pow_two] using h.symm⟩
  have hs_numden := Rat.isSquare_iff.mp hsR
  have hs_pM : IsSquare (p * M) := by
    simpa [hnumR] using hs_numden.1
  have hs_q3 : IsSquare (qN ^ 3) := by
    simpa [hdenR] using hs_numden.2
  obtain ⟨bN, hbN⟩ := isSquare_of_isSquare_cube qN hs_q3
  let b : ℤ := bN
  have hbq : q = b ^ 2 := by
    have hbNpow : qN = bN ^ 2 := by simpa [pow_two] using hbN
    change (qN : ℤ) = (bN : ℤ) ^ 2
    exact_mod_cast hbNpow
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact Int.natCast_nonneg bN
  have hbge2 : 2 ≤ b := by
    exact den_root_ge_two (q := q) (b := b) (qN := qN) rfl hden hb_nonneg hqpos hbq
  have hpM_coprime : IsCoprime p M := by
    dsimp [M]
    exact nat_coprime_curve_p_M_N16 p q hpq
  rcases hs_pM with ⟨r, hr⟩
  have hprod : p * M = r ^ 2 := by simpa [pow_two] using hr
  obtain ⟨a0, hp_assoc⟩ :=
    associated_square_left_of_coprime_square_mul hpM_coprime hprod
  obtain ⟨T0, hM_assoc⟩ :=
    associated_square_left_of_coprime_square_mul
      (a := M) (b := p) (r := r) hpM_coprime.symm (by simpa [mul_comm] using hprod)
  rcases (Int.associated_iff.mp hp_assoc) with hp_pos_assoc | hp_neg_assoc
  · let a : ℤ := |a0|
    have ha2 : a ^ 2 = a0 ^ 2 := by
      dsimp [a]
      rw [sq_abs]
    have hp_eq : p = a ^ 2 := by
      rw [hp_pos_assoc, ← ha2]
    have hp_pos : 0 < p := by
      have hp_nonneg : 0 ≤ p := by rw [hp_eq]; nlinarith [sq_nonneg a]
      have hp_ne : p ≠ 0 := by
        intro hp0
        exact hp_abs_ne_zero (by simp [hp0])
      exact lt_of_le_of_ne hp_nonneg (Ne.symm hp_ne)
    have hM_nonneg : 0 ≤ M := by
      have hr_nonneg : 0 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
      nlinarith
    have hM_eq : M = T0 ^ 2 :=
      eq_sq_of_nonneg_associated_sq hM_nonneg hM_assoc
    have hquart : T0 ^ 2 = a ^ 4 - a ^ 2 * b ^ 2 - b ^ 4 := by
      rw [← hM_eq]
      dsimp [M]
      rw [hp_eq, hbq]
      ring
    have hcop_ab : Int.gcd a b = 1 := by
      have hp_or : p = a ^ 2 ∨ p = -(a ^ 2) := Or.inl hp_eq
      simpa [a] using gcd_abs_square_root_of_coprime_square_square hpq hp_or hbq
    exact ⟨a, b, T0, hbge2, hcop_ab, hquart⟩
  · let a : ℤ := |a0|
    have ha2 : a ^ 2 = a0 ^ 2 := by
      dsimp [a]
      rw [sq_abs]
    have hp_eq : p = -(a ^ 2) := by
      rw [hp_neg_assoc, ← ha2]
    have hp_neg : p < 0 := by
      have hp_nonpos : p ≤ 0 := by rw [hp_eq]; nlinarith [sq_nonneg a]
      have hp_ne : p ≠ 0 := by
        intro hp0
        exact hp_abs_ne_zero (by simp [hp0])
      exact lt_of_le_of_ne hp_nonpos hp_ne
    have hM_nonpos : M ≤ 0 := by
      have hr_nonneg : 0 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
      nlinarith
    have hM_eq : M = -(T0 ^ 2) :=
      eq_neg_sq_of_nonpos_associated_sq hM_nonpos hM_assoc
    have ha_ge2 : 2 ≤ a := by
      have hp_or : p = a ^ 2 ∨ p = -(a ^ 2) := Or.inr hp_eq
      have ha_abs_ge2 : 2 ≤ |a| :=
        abs_root_ge_two_of_large_square (p := p) (a := a) hp_large hp_or
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        exact abs_nonneg a0
      simpa [abs_of_nonneg ha_nonneg] using ha_abs_ge2
    have hquart : T0 ^ 2 = b ^ 4 - b ^ 2 * a ^ 2 - a ^ 4 := by
      have hnegM : -(M) = T0 ^ 2 := by linarith
      rw [← hnegM]
      dsimp [M]
      rw [hp_eq, hbq]
      ring
    have hcop_ab : Int.gcd a b = 1 := by
      have hp_or : p = a ^ 2 ∨ p = -(a ^ 2) := Or.inr hp_eq
      simpa [a] using gcd_abs_square_root_of_coprime_square_square hpq hp_or hbq
    have hcop_ba : Int.gcd b a = 1 := by
      simpa [Int.gcd_comm] using hcop_ab
    exact ⟨b, a, T0, ha_ge2, hcop_ba, by nlinarith [hquart]⟩

private theorem num_abs_le_one_N16 (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - u) (hden : u.den ≠ 1) :
    |u.num| ≤ 1 := by
  by_contra hle
  have hlarge : 1 < |u.num| := not_le.mp hle
  obtain ⟨P, Q, T, hQ, hcop, hquart⟩ :=
    curve_point_gives_quartic_N16 u w h hden hlarge
  exact DenominatorQuarticN16.no_denominator_quartic_N16 P Q T hQ hcop hquart

private lemma coprime_pow_three_qsq_sub_q_sub_one (q : ℕ) (hq : 2 ≤ q) :
    Nat.Coprime (q ^ 3) (q ^ 2 - q - 1) := by
  have hcop : Nat.Coprime q (q ^ 2 - q - 1) := by
    change Nat.gcd q (q ^ 2 - q - 1) = 1
    let g := Nat.gcd q (q ^ 2 - q - 1)
    change g = 1
    have hgq : g ∣ q := by
      dsimp [g]
      exact Nat.gcd_dvd_left q (q ^ 2 - q - 1)
    have hgN : g ∣ q ^ 2 - q - 1 := by
      dsimp [g]
      exact Nat.gcd_dvd_right q (q ^ 2 - q - 1)
    have hgq2 : g ∣ q ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hgq q
    have hgsum : g ∣ q ^ 2 - q := Nat.dvd_sub hgq2 hgq
    have hone : q ^ 2 - q - (q ^ 2 - q - 1) = 1 := by
      have hgeq : q ≤ q ^ 2 := by
        have hq1 : 1 ≤ q := by omega
        simpa [pow_two] using Nat.le_mul_of_pos_right q hq1
      have hge1 : 1 ≤ q ^ 2 - q := by
        have hqminus : 1 ≤ q - 1 := by omega
        have hmul : 1 * 1 ≤ q * (q - 1) := Nat.mul_le_mul (by omega) hqminus
        have hpow_sub : q ^ 2 - q = q * (q - 1) := by
          rw [pow_two]
          symm
          rw [Nat.mul_sub_left_distrib]
          simp
        simpa [hpow_sub] using hmul
      omega
    have hgdvd1 : g ∣ 1 := by
      have hsub : g ∣ q ^ 2 - q - (q ^ 2 - q - 1) :=
        Nat.dvd_sub hgsum hgN
      simpa [hone] using hsub
    exact Nat.dvd_one.mp hgdvd1
  simpa using hcop.pow_left 3

private lemma neg_one_case_false_N16 (q : ℕ) (w : ℚ) (hq : 2 ≤ q)
    (h : w ^ 2 =
      ((-1 : ℚ) / (q : ℚ)) ^ 3 -
      ((-1 : ℚ) / (q : ℚ)) ^ 2 -
      ((-1 : ℚ) / (q : ℚ))) :
    False := by
  have hqpos_nat : 0 < q := by omega
  have hqposQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqpos_nat
  have hq0 : (q : ℚ) ≠ 0 := ne_of_gt hqposQ
  have hq2ne : (q : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hq3ne : (q : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hq0

  let Nn : ℕ := q ^ 2 - q - 1

  have hN_castQ : (Nn : ℚ) = (q : ℚ) ^ 2 - (q : ℚ) - 1 := by
    dsimp [Nn]
    have hgeq : q ≤ q ^ 2 := by
      have hq1 : 1 ≤ q := by omega
      simpa [pow_two] using Nat.le_mul_of_pos_right q hq1
    have hge1 : 1 ≤ q ^ 2 - q := by
      have hqminus : 1 ≤ q - 1 := by omega
      have hmul : 1 * 1 ≤ q * (q - 1) := Nat.mul_le_mul (by omega) hqminus
      have hpow_sub : q ^ 2 - q = q * (q - 1) := by
        rw [pow_two]
        symm
        rw [Nat.mul_sub_left_distrib]
        simp
      simpa [hpow_sub] using hmul
    calc
      ((q ^ 2 - q - 1 : ℕ) : ℚ)
          = ((q ^ 2 - q : ℕ) : ℚ) - (1 : ℚ) := by
            exact
              (Nat.cast_sub hge1 :
                ((q ^ 2 - q - 1 : ℕ) : ℚ) =
                  ((q ^ 2 - q : ℕ) : ℚ) - (1 : ℚ))
      _ = ((q ^ 2 : ℕ) : ℚ) - (q : ℚ) - 1 := by
            rw [Nat.cast_sub hgeq]
      _ = (q : ℚ) ^ 2 - (q : ℚ) - 1 := by
            rw [Nat.cast_pow]

  have hwq0 : w ^ 2 * (q : ℚ) ^ 3 =
      (q : ℚ) ^ 2 - (q : ℚ) - 1 := by
    rw [h]
    field_simp [hq0, hq2ne, hq3ne]
    ring

  have hwq : w ^ 2 * (q : ℚ) ^ 3 = (Nn : ℚ) := by
    rw [hN_castQ]
    exact hwq0

  let a : ℤ := w.num
  let b : ℕ := w.den

  have hw_numden : w = (a : ℚ) / (b : ℚ) := by
    dsimp [a, b]
    exact (Rat.num_div_den w).symm

  have hbpos : 0 < b := by
    dsimp [b]
    exact w.pos
  have hbposQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hbpos
  have hb0 : (b : ℚ) ≠ 0 := ne_of_gt hbposQ
  have hb2ne : (b : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hb0

  have heqQ : (a : ℚ) ^ 2 * (q : ℚ) ^ 3 =
      (b : ℚ) ^ 2 * (Nn : ℚ) := by
    have hwq' := hwq
    rw [hw_numden] at hwq'
    field_simp [hb0, hb2ne] at hwq'
    ring_nf at hwq' ⊢
    nlinarith

  have heqInt :
      a ^ 2 * (((q ^ 3 : ℕ) : ℤ)) = (b : ℤ) ^ 2 * (Nn : ℤ) := by
    have heqInt' : a ^ 2 * (q : ℤ) ^ 3 = (b : ℤ) ^ 2 * (Nn : ℤ) := by
      exact_mod_cast heqQ
    simpa using heqInt'

  have habIso : IsCoprime a (b : ℤ) := by
    dsimp [a, b]
    exact Int.isCoprime_iff_gcd_eq_one.mpr w.reduced

  have hab : Int.gcd a b = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp habIso

  have hcop : Nat.Coprime (q ^ 3) Nn := by
    dsimp [Nn]
    exact coprime_pow_three_qsq_sub_q_sub_one q hq

  have hsq_q3 : IsSquare (q ^ 3) := by
    refine coprime_sq_dvd_implies_sq (q ^ 3) b a (Nn : ℤ) hab ?_ ?_
    · have hnat : ((Nn : ℤ).natAbs) = Nn := by
        simp
      simpa [hnat] using hcop
    · exact heqInt

  have hsq_q : IsSquare q := isSquare_of_isSquare_cube q hsq_q3
  rcases hsq_q with ⟨d, hdq⟩

  have hq_d2 : q = d ^ 2 := by
    simpa [pow_two] using hdq

  have hd_ne0 : d ≠ 0 := by
    intro hd
    rw [hd, pow_two] at hq_d2
    norm_num at hq_d2
    omega
  have hd_ne1 : d ≠ 1 := by
    intro hd
    rw [hd, pow_two] at hq_d2
    norm_num at hq_d2
    omega
  have hd_ge_two : 2 ≤ d := by omega

  let r : ℚ := w * (d : ℚ) ^ 3

  have hqQ : (q : ℚ) = (d : ℚ) ^ 2 := by
    exact_mod_cast hq_d2

  have hr_sq :
      r ^ 2 = (((d : ℤ) ^ 4 - (d : ℤ) ^ 2 - 1 : ℤ) : ℚ) := by
    have hwq_d : w ^ 2 * (d : ℚ) ^ 6 = (d : ℚ) ^ 4 - (d : ℚ) ^ 2 - 1 := by
      have := hwq0
      rw [hqQ] at this
      ring_nf at this ⊢
      linarith [this]
    dsimp [r]
    push_cast
    ring_nf
    ring_nf at hwq_d
    linarith [hwq_d]

  have hrden : r.den = 1 :=
    rat_sq_int_den_one r ((d : ℤ) ^ 4 - (d : ℤ) ^ 2 - 1) hr_sq

  have hrZ := rat_eq_num r hrden

  have hr_int : r.num ^ 2 = (d : ℤ) ^ 4 - (d : ℤ) ^ 2 - 1 := by
    have h1 := hr_sq
    rw [show r = (r.num : ℚ) from hrZ] at h1
    exact_mod_cast h1

  have hdZ : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd_ge_two

  have hlow : ((d : ℤ) ^ 2 - 1) ^ 2 < r.num ^ 2 := by
    rw [hr_int]
    nlinarith [sq_nonneg ((d : ℤ) - 2)]

  have hhigh : r.num ^ 2 < ((d : ℤ) ^ 2) ^ 2 := by
    rw [hr_int]
    nlinarith [sq_nonneg (d : ℤ)]

  have hhigh' : r.num ^ 2 < (((d : ℤ) ^ 2 - 1) + 1) ^ 2 := by
    convert hhigh using 1
    ring

  exact no_int_sq_between_consecutive ((d : ℤ) ^ 2 - 1) r.num
    (by nlinarith [hdZ]) hlow hhigh'

theorem obstruction_N16 (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  by_cases hu : u = 0
  · right
    left
    exact hu

  have hden : u.den = 1 := by
    by_contra hne
    have hq : 2 ≤ u.den := by
      have hpos : 0 < u.den := u.pos
      omega

    set p := u.num
    set q := u.den

    have hq_ge : 2 ≤ q := by
      simpa [q] using hq

    have hqpos_nat : 0 < q := by omega
    have hqposQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqpos_nat
    have hqne' : (q : ℚ) ≠ 0 := ne_of_gt hqposQ
    have hq2ne' : (q : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hqne'
    have hq3ne' : (q : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hqne'

    have hu_eq : u = (p : ℚ) / (q : ℚ) := by
      simpa [p, q] using (Rat.num_div_den u).symm

    have hmul :
        w ^ 2 * (q : ℚ) ^ 3 =
          (p : ℚ) *
            ((p : ℚ) ^ 2 - (p : ℚ) * (q : ℚ) - (q : ℚ) ^ 2) := by
      have hrat := h
      rw [hu_eq] at hrat
      field_simp [hqne', hq2ne', hq3ne'] at hrat ⊢
      ring_nf at hrat ⊢
      nlinarith

    have hp_abs : |p| ≤ 1 := by
      dsimp [p]
      exact num_abs_le_one_N16 u w h hne

    have hp_cases : p = -1 ∨ p = 0 ∨ p = 1 := by
      have hp_bounds := abs_le.mp hp_abs
      have hp_ge : (-1 : ℤ) ≤ p := hp_bounds.1
      have hp_le : p ≤ (1 : ℤ) := hp_bounds.2
      omega

    rcases hp_cases with hp | hp | hp
    · have hu_neg : u = ((-1 : ℚ) / (q : ℚ)) := by
        rw [hu_eq, hp]
        norm_num
      have hneg :
          w ^ 2 =
            ((-1 : ℚ) / (q : ℚ)) ^ 3 -
            ((-1 : ℚ) / (q : ℚ)) ^ 2 -
            ((-1 : ℚ) / (q : ℚ)) := by
        have htmp := h
        rw [hu_neg] at htmp
        simpa using htmp
      exact neg_one_case_false_N16 q w hq_ge hneg

    · have hu0 : u = 0 := by
        rw [hu_eq, hp]
        norm_num
      exact hu hu0

    · have hmul1 :
          w ^ 2 * (q : ℚ) ^ 3 =
            (1 : ℚ) - (q : ℚ) - (q : ℚ) ^ 2 := by
        have htmp := hmul
        rw [hp] at htmp
        ring_nf at htmp ⊢
        exact htmp

      have lhs_nonneg : 0 ≤ w ^ 2 * (q : ℚ) ^ 3 := by
        exact mul_nonneg (sq_nonneg w) (pow_nonneg (le_of_lt hqposQ) 3)

      have rhs_neg : (1 : ℚ) - (q : ℚ) - (q : ℚ) ^ 2 < 0 := by
        have hqQ : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq_ge
        nlinarith

      nlinarith

  have huZ := rat_eq_num u hden

  have hw_eq :
      w ^ 2 =
        ((u.num : ℤ) : ℚ) ^ 3 -
        ((u.num : ℤ) : ℚ) ^ 2 -
        (u.num : ℤ) := by
    rw [← huZ]
    exact h

  have hwden : w.den = 1 :=
    rat_sq_int_den_one w (u.num ^ 3 - u.num ^ 2 - u.num) (by
      push_cast
      exact hw_eq)

  have hwZ := rat_eq_num w hwden

  have hint : w.num ^ 2 = u.num ^ 3 - u.num ^ 2 - u.num := by
    have h1 :
        (w.num : ℚ) ^ 2 =
          (u.num : ℚ) ^ 3 - (u.num : ℚ) ^ 2 - (u.num : ℚ) := by
      have h1 := h
      rw [show u = (u.num : ℚ) from huZ,
          show w = (w.num : ℚ) from hwZ] at h1
      simpa using h1
    exact_mod_cast h1

  rcases int_solutions_N16 u.num w.num hint with h1 | h2 | h3
  · left
    rw [huZ, h1]
    norm_num
  · right
    left
    rw [huZ, h2]
    norm_num
  · right
    right
    rw [huZ, h3]
    norm_num
