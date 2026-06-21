import Mathlib
import scratch.CoprimeFactorSplit
import scratch.IsSquareCube

set_option maxHeartbeats 1200000

open Scratch.ChatGPTDropDM1

namespace ObstructionQ14

private lemma int_gcd_eq_one_of_nat_coprime {a b : ℤ}
    (h : Nat.Coprime a.natAbs b.natAbs) :
    Int.gcd a b = 1 := by
  simpa [Int.gcd_def, Nat.Coprime] using h

private lemma nat_coprime_of_int_gcd_eq_one {a b : ℤ}
    (h : Int.gcd a b = 1) :
    Nat.Coprime a.natAbs b.natAbs := by
  simpa [Int.gcd_def, Nat.Coprime] using h

private lemma q14_factor_coprime_den
    (A q : ℤ) (hAq : Nat.Coprime A.natAbs q.natAbs) :
    Nat.Coprime
      ((A * (A ^ 2 + 22 * A * q - 7 * q ^ 2)).natAbs)
      q.natAbs := by
  have hAqI : IsCoprime A q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact int_gcd_eq_one_of_nat_coprime hAq
  have hA2q : IsCoprime (A ^ 2) q := hAqI.pow_left (m := 2)
  have hquad : IsCoprime (A ^ 2 + 22 * A * q - 7 * q ^ 2) q := by
    have h := hA2q.add_mul_right_left (22 * A - 7 * q)
    have hshape :
        A ^ 2 + (22 * A - 7 * q) * q =
          A ^ 2 + 22 * A * q - 7 * q ^ 2 := by
      ring
    simpa [hshape] using h
  have hprod : IsCoprime (A * (A ^ 2 + 22 * A * q - 7 * q ^ 2)) q :=
    hAqI.mul_left hquad
  rw [Int.isCoprime_iff_gcd_eq_one] at hprod
  exact nat_coprime_of_int_gcd_eq_one hprod

private lemma rat_q14_rhs_num_den (v : ℚ) :
    let A : ℤ := v.num
    let q : ℤ := v.den
    let M : ℤ := A * (A ^ 2 + 22 * A * q - 7 * q ^ 2)
    (v ^ 3 + 22 * v ^ 2 - 7 * v).num = M ∧
      (v ^ 3 + 22 * v ^ 2 - 7 * v).den = v.den ^ 3 := by
  classical
  let A : ℤ := v.num
  let qN : ℕ := v.den
  let q : ℤ := qN
  let M : ℤ := A * (A ^ 2 + 22 * A * q - 7 * q ^ 2)
  have hqposN : 0 < qN := v.pos
  have hqpos : 0 < q := by
    dsimp [q]
    exact Int.natCast_pos.mpr hqposN
  have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hv : v = (A : ℚ) / (q : ℚ) := by
    dsimp [A, q, qN]
    exact (Rat.num_div_den v).symm
  have hrhs :
      v ^ 3 + 22 * v ^ 2 - 7 * v =
        ((M : ℤ) : ℚ) / ((q ^ 3 : ℤ) : ℚ) := by
    rw [hv]
    field_simp [hq_ne]
    dsimp [M]
    push_cast
    ring
  have hAq : Nat.Coprime A.natAbs q.natAbs := by
    dsimp [A, q, qN]
    simpa [Int.natAbs_natCast] using v.reduced
  have hMq : Nat.Coprime M.natAbs q.natAbs := by
    dsimp [M]
    exact q14_factor_coprime_den A q hAq
  have hcop_den : Nat.Coprime M.natAbs (q ^ 3).natAbs := by
    have hpow : Nat.Coprime M.natAbs (q.natAbs ^ 3) := hMq.pow_right 3
    simpa [Int.natAbs_pow] using hpow
  have hq3pos : 0 < q ^ 3 := by positivity
  constructor
  · rw [hrhs]
    exact Rat.num_div_eq_of_coprime hq3pos hcop_den
  · rw [hrhs]
    have hden :=
      Rat.den_div_eq_of_coprime
        (a := M) (b := q ^ 3) hq3pos hcop_den
    apply Int.ofNat_inj.1
    simpa [q, qN, Int.natAbs_pow, Int.natAbs_natCast] using hden

private theorem q14_clear_denominators (v z : ℚ)
    (h : z ^ 2 = v ^ 3 + 22 * v ^ 2 - 7 * v) :
    ∃ A N C : ℤ, 0 < N ∧ Int.gcd A N = 1 ∧
      v = (A : ℚ) / ((N ^ 2 : ℤ) : ℚ) ∧
      C ^ 2 = A * (A ^ 2 + 22 * A * N ^ 2 - 7 * N ^ 4) := by
  classical
  let A : ℤ := v.num
  let qN : ℕ := v.den
  let q : ℤ := qN
  let M : ℤ := A * (A ^ 2 + 22 * A * q - 7 * q ^ 2)
  have hnumden := rat_q14_rhs_num_den v
  have hnumR : (v ^ 3 + 22 * v ^ 2 - 7 * v).num = M := by
    simpa [A, q, qN, M] using hnumden.1
  have hdenR : (v ^ 3 + 22 * v ^ 2 - 7 * v).den = qN ^ 3 := by
    simpa [A, q, qN, M] using hnumden.2
  have hsR : IsSquare (v ^ 3 + 22 * v ^ 2 - 7 * v) :=
    ⟨z, by simpa [pow_two] using h.symm⟩
  have hs_numden := Rat.isSquare_iff.mp hsR
  have hsM : IsSquare M := by
    simpa [hnumR] using hs_numden.1
  have hsq_q3 : IsSquare (qN ^ 3) := by
    simpa [hdenR] using hs_numden.2
  obtain ⟨N0, hN0sq⟩ := isSquare_of_isSquare_cube qN hsq_q3
  let N : ℤ := N0
  have hqN : qN = N0 ^ 2 := by
    simpa [pow_two] using hN0sq
  have hq : q = N ^ 2 := by
    dsimp [q, N]
    exact_mod_cast hqN
  have hNpos : 0 < N := by
    have hqpos : 0 < qN := v.pos
    have hN0pos : 0 < N0 := by
      by_contra hle
      have hN0zero : N0 = 0 := by omega
      rw [hN0zero] at hqN
      norm_num at hqN
      omega
    dsimp [N]
    exact_mod_cast hN0pos
  obtain ⟨C, hC⟩ := hsM
  have hAq : Nat.Coprime A.natAbs q.natAbs := by
    dsimp [A, q, qN]
    simpa [Int.natAbs_natCast] using v.reduced
  have hAqI : IsCoprime A q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact int_gcd_eq_one_of_nat_coprime hAq
  have hAN : IsCoprime A N := by
    have hAN2 : IsCoprime A (N ^ 2) := by
      simpa [hq] using hAqI
    exact (IsCoprime.pow_right_iff (x := A) (y := N) (m := 2) (by norm_num)).mp hAN2
  refine ⟨A, N, C, hNpos, Int.isCoprime_iff_gcd_eq_one.mp hAN, ?_, ?_⟩
  · have hv : v = (A : ℚ) / (q : ℚ) := by
      dsimp [A, q, qN]
      exact (Rat.num_div_den v).symm
    rw [hv, hq]
  · have hM : M = C ^ 2 := by
      simpa [pow_two] using hC
    rw [← hM]
    dsimp [M]
    rw [hq]
    ring

private lemma q14_gcd_A_quad_dvd_seven
    (A N : ℤ) (hcop : IsCoprime A N) :
    (Int.gcd A (A ^ 2 + 22 * A * N ^ 2 - 7 * N ^ 4) : ℤ) ∣ (7 : ℤ) := by
  let B : ℤ := A ^ 2 + 22 * A * N ^ 2 - 7 * N ^ 4
  let g : ℤ := Int.gcd A B
  have hgA : g ∣ A := by
    dsimp [g]
    exact Int.gcd_dvd_left _ _
  have hgB : g ∣ B := by
    dsimp [g]
    exact Int.gcd_dvd_right _ _
  have hg7N4 : g ∣ 7 * N ^ 4 := by
    have hgA_mul : g ∣ A * (A + 22 * N ^ 2) := dvd_mul_of_dvd_left hgA _
    have hsub : g ∣ A * (A + 22 * N ^ 2) - B := dvd_sub hgA_mul hgB
    convert hsub using 1
    dsimp [B]
    ring
  have hgN : IsCoprime g N := by
    rcases hcop with ⟨r, s, hrs⟩
    rcases hgA with ⟨t, ht⟩
    refine ⟨r * t, s, ?_⟩
    rw [ht] at hrs
    nlinarith
  have hgN4 : IsCoprime g (N ^ 4) := hgN.pow_right
  exact hgN4.dvd_of_dvd_mul_right hg7N4

private lemma q14_gcd_pos_of_left_ne_zero (a b : ℤ) (ha : a ≠ 0) :
    0 < (Int.gcd a b : ℤ) := by
  have hg : Int.gcd a b ≠ 0 := by
    intro hg0
    have hd : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
    rw [hg0] at hd
    exact ha (by simpa using hd)
  exact_mod_cast Nat.pos_of_ne_zero hg

private lemma q14_gcd_dvd_seven_cases (a b : ℤ) (ha : a ≠ 0)
    (h : (Int.gcd a b : ℤ) ∣ (7 : ℤ)) :
    Int.gcd a b = 1 ∨ Int.gcd a b = 7 := by
  let g : ℕ := Int.gcd a b
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using q14_gcd_pos_of_left_ne_zero a b ha
  rcases h with ⟨k, hk⟩
  have hk' : (g : ℤ) * k = 7 := by simpa [g, mul_comm] using hk.symm
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 7 := by nlinarith
  interval_cases k <;> omega

private lemma q14_gcd_scaled_seven (a b : ℤ) :
    Int.gcd (7 * a) (7 * b) = 7 * Int.gcd a b := by
  rw [Int.gcd_def, Int.gcd_def]
  rw [Int.natAbs_mul, Int.natAbs_mul]
  norm_num
  rw [Nat.gcd_mul_left]

private lemma q14_squareclass_of_product_square
    (A B C : ℤ) (hA0 : A ≠ 0)
    (hgcd7 : (Int.gcd A B : ℤ) ∣ (7 : ℤ))
    (hprod : C ^ 2 = A * B) :
    ∃ d M : ℤ,
      d ∈ ({1, -1, 7, -7} : Finset ℤ) ∧ A = d * M ^ 2 := by
  have hfact : A * B = C ^ 2 := by nlinarith
  rcases q14_gcd_dvd_seven_cases A B hA0 hgcd7 with hgcd1 | hgcd7eq
  · have hcop : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hgcd1
    obtain ⟨M, hM | hM⟩ := Int.sq_of_isCoprime hcop hfact
    · refine ⟨1, M, ?_, ?_⟩
      · norm_num
      · nlinarith
    · refine ⟨-1, M, ?_, ?_⟩
      · norm_num
      · nlinarith
  · have h7A : (7 : ℤ) ∣ A := by
      simpa [hgcd7eq] using (Int.gcd_dvd_left A B : (Int.gcd A B : ℤ) ∣ A)
    have h7B : (7 : ℤ) ∣ B := by
      simpa [hgcd7eq] using (Int.gcd_dvd_right A B : (Int.gcd A B : ℤ) ∣ B)
    rcases h7A with ⟨A1, hA⟩
    rcases h7B with ⟨B1, hB⟩
    have h7C2 : (7 : ℤ) ∣ C ^ 2 := by
      rw [hprod, hA, hB]
      exact ⟨7 * A1 * B1, by ring⟩
    have h7C : (7 : ℤ) ∣ C :=
      (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (7 : ℤ)).dvd_of_dvd_pow h7C2
    rcases h7C with ⟨C1, hC⟩
    have hC1prod : C1 ^ 2 = A1 * B1 := by
      rw [hA, hB, hC] at hprod
      nlinarith
    have hgcdA1B1 : Int.gcd A1 B1 = 1 := by
      have hscaled : Int.gcd A B = 7 * Int.gcd A1 B1 := by
        rw [hA, hB]
        exact q14_gcd_scaled_seven A1 B1
      omega
    have hcopA1B1 : IsCoprime A1 B1 := Int.isCoprime_iff_gcd_eq_one.mpr hgcdA1B1
    have hfact1 : A1 * B1 = C1 ^ 2 := by nlinarith
    obtain ⟨M, hM | hM⟩ := Int.sq_of_isCoprime hcopA1B1 hfact1
    · refine ⟨7, M, ?_, ?_⟩
      · norm_num
      · rw [hA, hM]
    · refine ⟨-7, M, ?_, ?_⟩
      · norm_num
      · rw [hA, hM]
        ring

private lemma q14_squareclass_pair_of_product_square
    (A B C : ℤ) (hA0 : A ≠ 0)
    (hgcd7 : (Int.gcd A B : ℤ) ∣ (7 : ℤ))
    (hprod : C ^ 2 = A * B) :
    ∃ d M Y : ℤ,
      d ∈ ({1, -1, 7, -7} : Finset ℤ) ∧
        A = d * M ^ 2 ∧ B = d * Y ^ 2 := by
  have hfact : A * B = C ^ 2 := by nlinarith
  rcases q14_gcd_dvd_seven_cases A B hA0 hgcd7 with hgcd1 | hgcd7eq
  · have hcop : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hgcd1
    obtain ⟨M, hMpos | hMneg⟩ := Int.sq_of_isCoprime hcop hfact
    · obtain ⟨Y, hYpos | hYneg⟩ :=
        Int.sq_of_isCoprime hcop.symm (show B * A = C ^ 2 by nlinarith)
      · refine ⟨1, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · nlinarith
        · nlinarith
      · have hM0 : M ≠ 0 := by
          intro hM0
          rw [hM0] at hMpos
          exact hA0 (by nlinarith)
        have hY0 : Y = 0 := by
          by_contra hY0
          have hneg : C ^ 2 < 0 := by
            rw [hprod, hMpos, hYneg]
            nlinarith [sq_pos_of_ne_zero hM0, sq_pos_of_ne_zero hY0]
          nlinarith [sq_nonneg C]
        refine ⟨1, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · nlinarith
        · rw [hYneg, hY0]
          norm_num
    · obtain ⟨Y, hYpos | hYneg⟩ :=
        Int.sq_of_isCoprime hcop.symm (show B * A = C ^ 2 by nlinarith)
      · have hM0 : M ≠ 0 := by
          intro hM0
          rw [hM0] at hMneg
          exact hA0 (by nlinarith)
        have hY0 : Y = 0 := by
          by_contra hY0
          have hneg : C ^ 2 < 0 := by
            rw [hprod, hMneg, hYpos]
            nlinarith [sq_pos_of_ne_zero hM0, sq_pos_of_ne_zero hY0]
          nlinarith [sq_nonneg C]
        refine ⟨-1, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · nlinarith
        · rw [hYpos, hY0]
          norm_num
      · refine ⟨-1, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · nlinarith
        · nlinarith
  · have h7A : (7 : ℤ) ∣ A := by
      simpa [hgcd7eq] using (Int.gcd_dvd_left A B : (Int.gcd A B : ℤ) ∣ A)
    have h7B : (7 : ℤ) ∣ B := by
      simpa [hgcd7eq] using (Int.gcd_dvd_right A B : (Int.gcd A B : ℤ) ∣ B)
    rcases h7A with ⟨A1, hA⟩
    rcases h7B with ⟨B1, hB⟩
    have h7C2 : (7 : ℤ) ∣ C ^ 2 := by
      rw [hprod, hA, hB]
      exact ⟨7 * A1 * B1, by ring⟩
    have h7C : (7 : ℤ) ∣ C :=
      (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (7 : ℤ)).dvd_of_dvd_pow h7C2
    rcases h7C with ⟨C1, hC⟩
    have hC1prod : C1 ^ 2 = A1 * B1 := by
      rw [hA, hB, hC] at hprod
      nlinarith
    have hgcdA1B1 : Int.gcd A1 B1 = 1 := by
      have hscaled : Int.gcd A B = 7 * Int.gcd A1 B1 := by
        rw [hA, hB]
        exact q14_gcd_scaled_seven A1 B1
      omega
    have hcopA1B1 : IsCoprime A1 B1 := Int.isCoprime_iff_gcd_eq_one.mpr hgcdA1B1
    have hfact1 : A1 * B1 = C1 ^ 2 := by nlinarith
    obtain ⟨M, hMpos | hMneg⟩ := Int.sq_of_isCoprime hcopA1B1 hfact1
    · obtain ⟨Y, hYpos | hYneg⟩ :=
        Int.sq_of_isCoprime hcopA1B1.symm (show B1 * A1 = C1 ^ 2 by nlinarith)
      · refine ⟨7, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · rw [hA, hMpos]
        · rw [hB, hYpos]
      · have hA10 : A1 ≠ 0 := by
          intro hA10
          apply hA0
          rw [hA, hA10]
          ring
        have hM0 : M ≠ 0 := by
          intro hM0
          rw [hM0] at hMpos
          exact hA10 (by nlinarith)
        have hY0 : Y = 0 := by
          by_contra hY0
          have hneg : C1 ^ 2 < 0 := by
            rw [hC1prod, hMpos, hYneg]
            nlinarith [sq_pos_of_ne_zero hM0, sq_pos_of_ne_zero hY0]
          nlinarith [sq_nonneg C1]
        refine ⟨7, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · rw [hA, hMpos]
        · rw [hB, hYneg, hY0]
          norm_num
    · obtain ⟨Y, hYpos | hYneg⟩ :=
        Int.sq_of_isCoprime hcopA1B1.symm (show B1 * A1 = C1 ^ 2 by nlinarith)
      · have hA10 : A1 ≠ 0 := by
          intro hA10
          apply hA0
          rw [hA, hA10]
          ring
        have hM0 : M ≠ 0 := by
          intro hM0
          rw [hM0] at hMneg
          exact hA10 (by nlinarith)
        have hY0 : Y = 0 := by
          by_contra hY0
          have hneg : C1 ^ 2 < 0 := by
            rw [hC1prod, hMneg, hYpos]
            nlinarith [sq_pos_of_ne_zero hM0, sq_pos_of_ne_zero hY0]
          nlinarith [sq_nonneg C1]
        refine ⟨-7, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · rw [hA, hMneg]
          ring
        · rw [hB, hYpos, hY0]
          norm_num
      · refine ⟨-7, M, Y, ?_, ?_, ?_⟩
        · norm_num
        · rw [hA, hMneg]
          ring
        · rw [hB, hYneg]
          ring

structure Q14DescentDatum (v z : ℚ) where
  d : ℤ
  M : ℤ
  N : ℤ
  Y : ℤ
  d_mem : d ∈ ({1, -1, 7, -7} : Finset ℤ)
  N_pos : 0 < N
  coprime_MN : IsCoprime M N
  v_eq : v = (d : ℚ) * ((M : ℚ) / (N : ℚ)) ^ 2
  descent_eq :
    d * Y ^ 2 = d ^ 2 * M ^ 4 + 22 * d * M ^ 2 * N ^ 2 - 7 * N ^ 4

private lemma q14_coprime_MN_of_A_eq
    {A d M N : ℤ} (hcopAN : IsCoprime A N)
    (hA : A = d * M ^ 2) :
    IsCoprime M N := by
  have hMdvdA : M ∣ A := by
    rw [hA]
    exact ⟨d * M, by ring⟩
  exact hcopAN.of_isCoprime_of_dvd_left hMdvdA

lemma Q14_squareclass_descent
    {v z : ℚ}
    (hv : v ≠ 0)
    (h : z ^ 2 = v ^ 3 + 22 * v ^ 2 - 7 * v) :
    ∃ _D : Q14DescentDatum v z, True := by
  rcases q14_clear_denominators v z h with
    ⟨A, N, C, hNpos, hAN, hvA, hC⟩
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hA0 : A ≠ 0 := by
    intro hA0
    apply hv
    rw [hvA, hA0]
    norm_num
  let B : ℤ := A ^ 2 + 22 * A * N ^ 2 - 7 * N ^ 4
  have hcopAN : IsCoprime A N := Int.isCoprime_iff_gcd_eq_one.mpr hAN
  have hgcd7 : (Int.gcd A B : ℤ) ∣ (7 : ℤ) := by
    dsimp [B]
    exact q14_gcd_A_quad_dvd_seven A N hcopAN
  have hprod : C ^ 2 = A * B := by
    simpa [B] using hC
  obtain ⟨d, M, Y, hdmem, hA, hB⟩ :=
    q14_squareclass_pair_of_product_square A B C hA0 hgcd7 hprod
  have hcopMN : IsCoprime M N := q14_coprime_MN_of_A_eq hcopAN hA
  have hvD : v = (d : ℚ) * ((M : ℚ) / (N : ℚ)) ^ 2 := by
    rw [hvA, hA]
    field_simp [hNne]
    push_cast
    ring
  have hdesc :
      d * Y ^ 2 =
        d ^ 2 * M ^ 4 + 22 * d * M ^ 2 * N ^ 2 - 7 * N ^ 4 := by
    calc
      d * Y ^ 2 = B := hB.symm
      _ = A ^ 2 + 22 * A * N ^ 2 - 7 * N ^ 4 := rfl
      _ = d ^ 2 * M ^ 4 + 22 * d * M ^ 2 * N ^ 2 - 7 * N ^ 4 := by
        rw [hA]
        ring
  refine ⟨{
    d := d
    M := M
    N := N
    Y := Y
    d_mem := hdmem
    N_pos := hNpos
    coprime_MN := hcopMN
    v_eq := hvD
    descent_eq := hdesc
  }, trivial⟩

private lemma mem_Q14_target_rat {v : ℚ} :
    v ∈ ({-7, 0, 1} : Finset ℚ) ↔ v = -7 ∨ v = 0 ∨ v = 1 := by
  norm_num [Finset.mem_insert, Finset.mem_singleton]

private lemma mem_Q14_squareclasses_int {d : ℤ} :
    d ∈ ({1, -1, 7, -7} : Finset ℤ) ↔
      d = 1 ∨ d = -1 ∨ d = 7 ∨ d = -7 := by
  norm_num [Finset.mem_insert, Finset.mem_singleton]

private def zmod16_even_residue (x : ZMod 16) : Prop :=
  x = 0 ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨
    x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 14

private lemma even_of_zmod16_eq_even_int {x r : ℤ}
    (hr : (2 : ℤ) ∣ r)
    (h : (x : ZMod 16) = (r : ZMod 16)) :
    (2 : ℤ) ∣ x := by
  have hzero : ((x - r : ℤ) : ZMod 16) = 0 := by
    rw [Int.cast_sub, h, sub_self]
  have h16 : (16 : ℤ) ∣ x - r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (x - r) 16).mp hzero
  rcases h16 with ⟨k, hk⟩
  rcases hr with ⟨s, hs⟩
  refine ⟨8 * k + s, ?_⟩
  omega

private lemma even_of_int_cast_zmod16_even_residue {x : ℤ}
    (hx : zmod16_even_residue (x : ZMod 16)) :
    (2 : ℤ) ∣ x := by
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx
  · exact even_of_zmod16_eq_even_int (x := x) (r := 0) (by norm_num) (by simpa using hx)
  · exact even_of_zmod16_eq_even_int (x := x) (r := 2) (by norm_num) (by simpa using hx)
  · exact even_of_zmod16_eq_even_int (x := x) (r := 4) (by norm_num) (by simpa using hx)
  · exact even_of_zmod16_eq_even_int (x := x) (r := 6) (by norm_num) (by simpa using hx)
  · exact even_of_zmod16_eq_even_int (x := x) (r := 8) (by norm_num) (by simpa using hx)
  · exact even_of_zmod16_eq_even_int (x := x) (r := 10) (by norm_num) (by simpa using hx)
  · exact even_of_zmod16_eq_even_int (x := x) (r := 12) (by norm_num) (by simpa using hx)
  · exact even_of_zmod16_eq_even_int (x := x) (r := 14) (by norm_num) (by simpa using hx)

private lemma q14_mod16_d_neg_one_false
    (m n y : ZMod 16)
    (hprim : ¬ (zmod16_even_residue m ∧ zmod16_even_residue n))
    (h : y ^ 2 = -m ^ 4 + 22 * m ^ 2 * n ^ 2 + 7 * n ^ 4) :
    False := by
  unfold zmod16_even_residue at hprim
  revert m n y
  decide

private lemma q14_mod16_d_pos_seven_false
    (m n y : ZMod 16)
    (hprim : ¬ (zmod16_even_residue m ∧ zmod16_even_residue n))
    (h : y ^ 2 = 7 * m ^ 4 + 22 * m ^ 2 * n ^ 2 - n ^ 4) :
    False := by
  unfold zmod16_even_residue at hprim
  revert m n y
  decide

private lemma not_both_even_of_coprime {M N : ℤ}
    (hcop : IsCoprime M N) :
    ¬ ((2 : ℤ) ∣ M ∧ (2 : ℤ) ∣ N) := by
  rintro ⟨hM, hN⟩
  have h2gcd : (2 : ℤ) ∣ (Int.gcd M N : ℤ) := Int.dvd_coe_gcd hM hN
  have hgcd : Int.gcd M N = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  rw [hgcd] at h2gcd
  norm_num at h2gcd

/-- The `d = -1` quartic has no primitive integer solution. -/
lemma Q14_quartic_d_neg_one_no_solution
    {M N Y : ℤ}
    (_hN : 0 < N)
    (hcop : IsCoprime M N)
    (h :
      Y ^ 2 = -M ^ 4 + 22 * M ^ 2 * N ^ 2 + 7 * N ^ 4) :
    False := by
  have hprim :
      ¬ (zmod16_even_residue (M : ZMod 16) ∧
          zmod16_even_residue (N : ZMod 16)) := by
    intro hMN
    have hM2 : (2 : ℤ) ∣ M := even_of_int_cast_zmod16_even_residue hMN.1
    have hN2 : (2 : ℤ) ∣ N := even_of_int_cast_zmod16_even_residue hMN.2
    exact not_both_even_of_coprime hcop ⟨hM2, hN2⟩
  have hz : ((Y : ZMod 16) ^ 2 =
      -(M : ZMod 16) ^ 4 + 22 * (M : ZMod 16) ^ 2 * (N : ZMod 16) ^ 2 +
        7 * (N : ZMod 16) ^ 4) := by
    have hcast := congrArg (fun t : ℤ => (t : ZMod 16)) h
    norm_num at hcast ⊢
    simpa using hcast
  exact q14_mod16_d_neg_one_false (M : ZMod 16) (N : ZMod 16) (Y : ZMod 16) hprim hz

/-- The `d = 7` quartic has no primitive integer solution. -/
lemma Q14_quartic_d_pos_seven_no_solution
    {M N Y : ℤ}
    (_hN : 0 < N)
    (hcop : IsCoprime M N)
    (h :
      Y ^ 2 = 7 * M ^ 4 + 22 * M ^ 2 * N ^ 2 - N ^ 4) :
    False := by
  have hprim :
      ¬ (zmod16_even_residue (M : ZMod 16) ∧
          zmod16_even_residue (N : ZMod 16)) := by
    intro hMN
    have hM2 : (2 : ℤ) ∣ M := even_of_int_cast_zmod16_even_residue hMN.1
    have hN2 : (2 : ℤ) ∣ N := even_of_int_cast_zmod16_even_residue hMN.2
    exact not_both_even_of_coprime hcop ⟨hM2, hN2⟩
  have hz : ((Y : ZMod 16) ^ 2 =
      7 * (M : ZMod 16) ^ 4 + 22 * (M : ZMod 16) ^ 2 * (N : ZMod 16) ^ 2 -
        (N : ZMod 16) ^ 4) := by
    have hcast := congrArg (fun t : ℤ => (t : ZMod 16)) h
    norm_num at hcast ⊢
    simpa using hcast
  exact q14_mod16_d_pos_seven_false (M : ZMod 16) (N : ZMod 16) (Y : ZMod 16) hprim hz

/--
Residual Q14 rank-zero seam.

The squareclass descent above reduces the two surviving branches to the
`d = 1` and `d = -7` quartic descent tails.  The `d = -1` and `d = 7`
branches are already closed by the mod-16 obstructions.
-/
theorem Q14_rank_zero_descent_tail_seam
    {v z : ℚ} {d M N Y : ℤ}
    (hd : d = 1 ∨ d = -7)
    (_hN : 0 < N)
    (_hcop : IsCoprime M N)
    (hv : v = (d : ℚ) * ((M : ℚ) / (N : ℚ)) ^ 2)
    (_hdesc :
      d * Y ^ 2 =
        d ^ 2 * M ^ 4 + 22 * d * M ^ 2 * N ^ 2 - 7 * N ^ 4) :
    v ∈ ({-7, 0, 1} : Finset ℚ) := by
  -- TODO: finish the two quartic descent tails:
  --   d = 1  forces M^2 = N^2, hence v = 1;
  --   d = -7 forces M = 0 or M^2 = N^2, hence v = 0 or v = -7.
  -- This is the remaining rank-zero enumeration work for Q14.
  sorry

/-- Rational points on `Q14 : z^2 = v^3 + 22v^2 - 7v` have `v ∈ {-7,0,1}`. -/
theorem obstruction_Q14
    (v z : ℚ)
    (h : z ^ 2 = v ^ 3 + 22 * v ^ 2 - 7 * v) :
    v ∈ ({-7, 0, 1} : Finset ℚ) := by
  classical
  by_cases hv0 : v = 0
  · rw [hv0]
    norm_num
  obtain ⟨D, _⟩ := Q14_squareclass_descent hv0 h
  obtain ⟨d, M, N, Y, hdmem, hNpos, hcopMN, hvD, hdesc⟩ := D
  rw [mem_Q14_squareclasses_int] at hdmem
  rcases hdmem with hd | hd | hd | hd
  · exact Q14_rank_zero_descent_tail_seam
      (v := v) (z := z) (d := d) (M := M) (N := N) (Y := Y)
      (Or.inl hd) hNpos hcopMN hvD hdesc
  · subst d
    have hq :
        Y ^ 2 = -M ^ 4 + 22 * M ^ 2 * N ^ 2 + 7 * N ^ 4 := by
      nlinarith [hdesc]
    exact False.elim <|
      Q14_quartic_d_neg_one_no_solution
        (M := M) (N := N) (Y := Y) hNpos hcopMN hq
  · subst d
    have hq :
        Y ^ 2 = 7 * M ^ 4 + 22 * M ^ 2 * N ^ 2 - N ^ 4 := by
      nlinarith [hdesc]
    exact False.elim <|
      Q14_quartic_d_pos_seven_no_solution
        (M := M) (N := N) (Y := Y) hNpos hcopMN hq
  · exact Q14_rank_zero_descent_tail_seam
      (v := v) (z := z) (d := d) (M := M) (N := N) (Y := Y)
      (Or.inr hd) hNpos hcopMN hvD hdesc

end ObstructionQ14
