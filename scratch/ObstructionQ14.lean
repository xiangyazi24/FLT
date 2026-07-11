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

/-! ## Coprime fourth-power splitting with the exceptional prime seven -/

/-- If positive coprime factors have product `7 * q⁴`, then the factor carrying
the prime seven is seven times a fourth power and the other factor is a fourth
power.  The positive fourth roots multiply to `q`. -/
lemma coprime_factor_seven_fourth
    {A B q : ℤ}
    (hAB : A * B = 7 * q ^ 4)
    (hcop : IsCoprime A B)
    (hApos : 0 < A) (hBpos : 0 < B) (hqpos : 0 < q) :
    ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ m * n = q ∧
      ((A = 7 * m ^ 4 ∧ B = n ^ 4) ∨
        (A = m ^ 4 ∧ B = 7 * n ^ 4)) := by
  have h7prod : (7 : ℤ) ∣ A * B := ⟨q ^ 4, by linarith⟩
  rcases Int.Prime.dvd_mul' (by norm_num : Nat.Prime 7) h7prod with h7A | h7B
  · obtain ⟨A₀, hA⟩ := h7A
    have hA₀pos : 0 < A₀ := by
      rw [hA] at hApos
      nlinarith
    have hA₀B : A₀ * B = q ^ 4 := by
      rw [hA] at hAB
      have h : (7 : ℤ) * (A₀ * B) = 7 * q ^ 4 := by
        simpa [mul_assoc] using hAB
      exact mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0) h
    have hcop₀ : IsCoprime A₀ B := by
      have h := hcop
      rw [hA] at h
      exact h.of_mul_left_right
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      coprime_product_eq_fourth_power
        A₀ B q hA₀pos hBpos hqpos hcop₀ hA₀B
    refine ⟨m, n, hmpos, hnpos, hmn, Or.inl ⟨?_, hn⟩⟩
    rw [hA, hm]
    norm_num
  · obtain ⟨B₀, hB⟩ := h7B
    have hB₀pos : 0 < B₀ := by
      rw [hB] at hBpos
      nlinarith
    have hAB₀ : A * B₀ = q ^ 4 := by
      rw [hB] at hAB
      have h : (7 : ℤ) * (A * B₀) = 7 * q ^ 4 := by
        simpa [mul_left_comm, mul_assoc] using hAB
      exact mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0) h
    have hcop₀ : IsCoprime A B₀ := by
      have h := hcop
      rw [hB] at h
      exact h.of_mul_right_right
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      coprime_product_eq_fourth_power
        A B₀ q hApos hB₀pos hqpos hcop₀ hAB₀
    refine ⟨m, n, hmpos, hnpos, hmn, Or.inr ⟨hm, ?_⟩⟩
    rw [hB, hn]
    norm_num

/-- The corresponding split for `2 * q⁴`.  This is the 2-adic first stage
of the order-14 quartic descent. -/
lemma coprime_factor_two_fourth
    {A B q : ℤ}
    (hAB : A * B = 2 * q ^ 4)
    (hcop : IsCoprime A B)
    (hApos : 0 < A) (hBpos : 0 < B) (hqpos : 0 < q) :
    ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ m * n = q ∧
      ((A = 2 * m ^ 4 ∧ B = n ^ 4) ∨
        (A = m ^ 4 ∧ B = 2 * n ^ 4)) := by
  have h2prod : (2 : ℤ) ∣ A * B := ⟨q ^ 4, by linarith⟩
  rcases Int.Prime.dvd_mul' (by norm_num : Nat.Prime 2) h2prod with h2A | h2B
  · obtain ⟨A₀, hA⟩ := h2A
    have hA₀pos : 0 < A₀ := by
      rw [hA] at hApos
      nlinarith
    have hA₀B : A₀ * B = q ^ 4 := by
      rw [hA] at hAB
      have h : (2 : ℤ) * (A₀ * B) = 2 * q ^ 4 := by
        simpa [mul_assoc] using hAB
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h
    have hcop₀ : IsCoprime A₀ B := by
      have h := hcop
      rw [hA] at h
      exact h.of_mul_left_right
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      coprime_product_eq_fourth_power
        A₀ B q hA₀pos hBpos hqpos hcop₀ hA₀B
    refine ⟨m, n, hmpos, hnpos, hmn, Or.inl ⟨?_, hn⟩⟩
    rw [hA, hm]
    norm_num
  · obtain ⟨B₀, hB⟩ := h2B
    have hB₀pos : 0 < B₀ := by
      rw [hB] at hBpos
      nlinarith
    have hAB₀ : A * B₀ = q ^ 4 := by
      rw [hB] at hAB
      have h : (2 : ℤ) * (A * B₀) = 2 * q ^ 4 := by
        simpa [mul_left_comm, mul_assoc] using hAB
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h
    have hcop₀ : IsCoprime A B₀ := by
      have h := hcop
      rw [hB] at h
      exact h.of_mul_right_right
    obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
      coprime_product_eq_fourth_power
        A B₀ q hApos hB₀pos hqpos hcop₀ hAB₀
    refine ⟨m, n, hmpos, hnpos, hmn, Or.inr ⟨hm, ?_⟩⟩
    rw [hB, hn]
    norm_num

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

/-! ## Algebraic core of the two surviving descent tails -/

def Q14PlusQuartic (M N Y : ℤ) : Prop :=
  Y ^ 2 = M ^ 4 + 22 * M ^ 2 * N ^ 2 - 7 * N ^ 4

def Q14MinusQuartic (M N Y : ℤ) : Prop :=
  Y ^ 2 = -7 * M ^ 4 + 22 * M ^ 2 * N ^ 2 + N ^ 4

def Q14DualQuartic (x y Z : ℤ) : Prop :=
  Z ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 + 32 * y ^ 4

private lemma q14_plus_both_odd_y_mod_eight
    {M N Y : ℤ}
    (hM : M % 2 = 1) (hN : N % 2 = 1)
    (h : Q14PlusQuartic M N Y) :
    Y % 8 = 4 := by
  obtain ⟨m, hm⟩ : ∃ m, M = 2 * m + 1 := ⟨M / 2, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, N = 2 * n + 1 := ⟨N / 2, by omega⟩
  rw [hm, hn] at h
  simp only [Q14PlusQuartic] at h
  have hYeven : Y % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one Y with hY | hY
    · exact hY
    · obtain ⟨y, hy⟩ : ∃ y, Y = 2 * y + 1 := ⟨Y / 2, by omega⟩
      rw [hy] at h
      ring_nf at h
      omega
  obtain ⟨y, hy⟩ : ∃ y, Y = 2 * y := ⟨Y / 2, by omega⟩
  have hyeven : y % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one y with hy0 | hy1
    · exact hy0
    · obtain ⟨k, hk⟩ : ∃ k, y = 2 * k + 1 := ⟨y / 2, by omega⟩
      rw [hy, hk] at h
      ring_nf at h
      omega
  obtain ⟨k, hk⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
  have hkodd : k % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, k = 2 * ℓ := ⟨k / 2, by omega⟩
      rcases Int.emod_two_eq_zero_or_one m with hm0 | hm1
      · obtain ⟨p, hp⟩ : ∃ p, m = 2 * p := ⟨m / 2, by omega⟩
        rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
        · obtain ⟨q, hq⟩ : ∃ q, n = 2 * q := ⟨n / 2, by omega⟩
          rw [hy, hk, hℓ, hp, hq] at h
          ring_nf at h
          omega
        · obtain ⟨q, hq⟩ : ∃ q, n = 2 * q + 1 := ⟨n / 2, by omega⟩
          rw [hy, hk, hℓ, hp, hq] at h
          ring_nf at h
          omega
      · obtain ⟨p, hp⟩ : ∃ p, m = 2 * p + 1 := ⟨m / 2, by omega⟩
        rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
        · obtain ⟨q, hq⟩ : ∃ q, n = 2 * q := ⟨n / 2, by omega⟩
          rw [hy, hk, hℓ, hp, hq] at h
          ring_nf at h
          omega
        · obtain ⟨q, hq⟩ : ∃ q, n = 2 * q + 1 := ⟨n / 2, by omega⟩
          rw [hy, hk, hℓ, hp, hq] at h
          ring_nf at h
          omega
    · exact hk1
  rw [hy, hk]
  omega

set_option maxHeartbeats 2400000 in
/-- The complete first factor split in the both-odd branch. -/
theorem Q14_plus_both_odd_first_split
    {M N Y : ℤ}
    (hM : M % 2 = 1) (hNodd : N % 2 = 1)
    (hNpos : 0 < N) (hcopMN : IsCoprime M N)
    (h : Q14PlusQuartic M N Y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ IsCoprime a b ∧ N = a * b ∧
      (((M ^ 2 + 11 * N ^ 2 - Y = 8 * a ^ 4) ∧
          (M ^ 2 + 11 * N ^ 2 + Y = 16 * b ^ 4)) ∨
        ((M ^ 2 + 11 * N ^ 2 - Y = 16 * a ^ 4) ∧
          (M ^ 2 + 11 * N ^ 2 + Y = 8 * b ^ 4))) := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, M = 2 * m₀ + 1 := ⟨M / 2, by omega⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, N = 2 * n₀ + 1 := ⟨N / 2, by omega⟩
  have hYmod := q14_plus_both_odd_y_mod_eight hM hNodd h
  have h4A : (4 : ℤ) ∣ M ^ 2 + 11 * N ^ 2 := by
    refine ⟨m₀ ^ 2 + m₀ + 11 * n₀ ^ 2 + 11 * n₀ + 3, ?_⟩
    rw [hm₀, hn₀]
    ring
  have h4Y : (4 : ℤ) ∣ Y := ⟨Y / 4, by omega⟩
  let A₀ := (M ^ 2 + 11 * N ^ 2) / 4
  let y₀ := Y / 4
  have hA₀val : 4 * A₀ = M ^ 2 + 11 * N ^ 2 :=
    Int.mul_ediv_cancel' h4A
  have hy₀val : 4 * y₀ = Y := Int.mul_ediv_cancel' h4Y
  have hA₀formula :
      A₀ = m₀ ^ 2 + m₀ + 11 * n₀ ^ 2 + 11 * n₀ + 3 := by
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    rw [hA₀val, hm₀, hn₀]
    ring
  have hA₀odd : A₀ % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one m₀ with hm | hm <;>
      rcases Int.emod_two_eq_zero_or_one n₀ with hn | hn
    all_goals
      rw [hA₀formula]
      have hmprod : (m₀ ^ 2 + m₀) % 2 = 0 := by
        have : (2 : ℤ) ∣ m₀ * (m₀ + 1) :=
          (Int.even_mul_succ_self m₀).two_dvd
        have heq : m₀ ^ 2 + m₀ = m₀ * (m₀ + 1) := by ring
        rw [heq]
        exact Int.emod_eq_zero_of_dvd this
      have hnprod : (n₀ ^ 2 + n₀) % 2 = 0 := by
        have : (2 : ℤ) ∣ n₀ * (n₀ + 1) :=
          (Int.even_mul_succ_self n₀).two_dvd
        have heq : n₀ ^ 2 + n₀ = n₀ * (n₀ + 1) := by ring
        rw [heq]
        exact Int.emod_eq_zero_of_dvd this
      omega
  have hy₀odd : y₀ % 2 = 1 := by
    dsimp [y₀]
    omega
  have hAY :
      (M ^ 2 + 11 * N ^ 2) ^ 2 - Y ^ 2 = 128 * N ^ 4 := by
    simp only [Q14PlusQuartic] at h
    nlinarith
  have hA₀y₀ : A₀ ^ 2 - y₀ ^ 2 = 8 * N ^ 4 := by
    rw [← hA₀val, ← hy₀val] at hAY
    ring_nf at hAY ⊢
    linarith
  have hApos : 0 < M ^ 2 + 11 * N ^ 2 := by positivity
  have hminusPos : 0 < M ^ 2 + 11 * N ^ 2 - Y := by
    by_contra hle
    push_neg at hle
    nlinarith [hAY, pow_pos hNpos 4]
  have hplusPos : 0 < M ^ 2 + 11 * N ^ 2 + Y := by
    by_contra hle
    push_neg at hle
    nlinarith [hAY, pow_pos hNpos 4]
  have h2minus : (2 : ℤ) ∣ A₀ - y₀ := ⟨(A₀ - y₀) / 2, by omega⟩
  have h2plus : (2 : ℤ) ∣ A₀ + y₀ := ⟨(A₀ + y₀) / 2, by omega⟩
  let F₁ := (A₀ - y₀) / 2
  let F₂ := (A₀ + y₀) / 2
  have hF₁val : 2 * F₁ = A₀ - y₀ := Int.mul_ediv_cancel' h2minus
  have hF₂val : 2 * F₂ = A₀ + y₀ := Int.mul_ediv_cancel' h2plus
  have hUval : 8 * F₁ = M ^ 2 + 11 * N ^ 2 - Y := by
    nlinarith [hA₀val, hy₀val, hF₁val]
  have hVval : 8 * F₂ = M ^ 2 + 11 * N ^ 2 + Y := by
    nlinarith [hA₀val, hy₀val, hF₂val]
  have hF₁pos : 0 < F₁ := by nlinarith [hUval, hminusPos]
  have hF₂pos : 0 < F₂ := by nlinarith [hVval, hplusPos]
  have hFprod : F₁ * F₂ = 2 * N ^ 4 := by
    have hprod :
        (M ^ 2 + 11 * N ^ 2 - Y) *
          (M ^ 2 + 11 * N ^ 2 + Y) = 128 * N ^ 4 := by
      nlinarith [hAY]
    rw [← hUval, ← hVval] at hprod
    ring_nf at hprod ⊢
    linarith
  have hA₀N : IsCoprime A₀ N := by
    have hM2N : IsCoprime (M ^ 2) N := hcopMN.pow_left
    have hsum : IsCoprime (M ^ 2 + (11 * N) * N) N :=
      hM2N.add_mul_right_left (11 * N)
    have hsum' : IsCoprime (4 * A₀) N := by
      simpa [hA₀val, pow_two, mul_assoc] using hsum
    exact hsum'.of_mul_left_right
  have hA₀y₀cop : IsCoprime A₀ y₀ := by
    by_contra hnot
    rw [Int.isCoprime_iff_gcd_eq_one] at hnot
    have hg_gt1 : 1 < Int.gcd A₀ y₀ := by
      have hA₀ne : A₀ ≠ 0 := by
        intro hz
        rw [hz] at hA₀odd
        norm_num at hA₀odd
      have hg_ne : Int.gcd A₀ y₀ ≠ 0 := by
        rw [Int.gcd_def]
        exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr hA₀ne)
      omega
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
    have hpA : (↑p : ℤ) ∣ A₀ :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
    have hpy : (↑p : ℤ) ∣ y₀ :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hp8N : (↑p : ℤ) ∣ 8 * N ^ 4 := by
      rw [← hA₀y₀]
      exact dvd_sub (dvd_pow hpA (by norm_num : 2 ≠ 0))
        (dvd_pow hpy (by norm_num : 2 ≠ 0))
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      have : A₀ % 2 = 0 := Int.emod_eq_zero_of_dvd hpA
      omega
    have hpN4 : (↑p : ℤ) ∣ N ^ 4 := by
      rcases hpint.dvd_or_dvd hp8N with hp8 | hpN4
      · have hp2 : (↑p : ℤ) ∣ (2 : ℤ) := by
          apply Int.Prime.dvd_pow' hp
          have hp2cube : (↑p : ℤ) ∣ (2 : ℤ) ^ 3 := by
            norm_num
            exact hp8
          exact hp2cube
        have hp_nat : p ∣ 2 := Int.natCast_dvd.mp hp2
        have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_nat
        exact False.elim (hpne2 (Nat.le_antisymm hp_le hp.two_le))
      · exact hpN4
    have hpN : (↑p : ℤ) ∣ N := Int.Prime.dvd_pow' hp hpN4
    exact hpint.not_unit (hA₀N.isUnit_of_dvd' hpA hpN)
  have hFcop : IsCoprime F₁ F₂ := by
    rcases hA₀y₀cop with ⟨r, s, hrs⟩
    refine ⟨r - s, r + s, ?_⟩
    have hsum : F₁ + F₂ = A₀ := by omega
    have hdiff : F₂ - F₁ = y₀ := by omega
    calc
      (r - s) * F₁ + (r + s) * F₂ =
          r * (F₁ + F₂) + s * (F₂ - F₁) := by ring
      _ = 1 := by rw [hsum, hdiff]; exact hrs
  obtain ⟨a, b, ha, hb, hab, hfac⟩ :=
    coprime_factor_two_fourth hFprod hFcop hF₁pos hF₂pos hNpos
  rcases hfac with hfac | hfac
  · have habcop : IsCoprime a b := by
      have hpows : IsCoprime (a ^ 4) (b ^ 4) := by
        have hcop' := hFcop
        rw [hfac.1, hfac.2] at hcop'
        exact hcop'.of_mul_left_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
    refine ⟨a, b, ha, hb, habcop, hab.symm, Or.inr ⟨?_, ?_⟩⟩
    · rw [← hUval, hfac.1]
      ring
    · rw [← hVval, hfac.2]
  · have habcop : IsCoprime a b := by
      have hpows : IsCoprime (a ^ 4) (b ^ 4) := by
        have hcop' := hFcop
        rw [hfac.1, hfac.2] at hcop'
        exact hcop'.of_mul_right_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
    refine ⟨a, b, ha, hb, habcop, hab.symm, Or.inl ⟨?_, ?_⟩⟩
    · rw [← hUval, hfac.1]
    · rw [← hVval, hfac.2]
      ring

set_option maxHeartbeats 2400000 in
/-- The first factor split when the midpoint `M² + 11N²` is odd.  The root
outside the factor carrying the full power of two is odd. -/
theorem Q14_plus_odd_midpoint_first_split
    {M N Y : ℤ}
    (hAodd : (M ^ 2 + 11 * N ^ 2) % 2 = 1)
    (hNpos : 0 < N) (hcopMN : IsCoprime M N)
    (h : Q14PlusQuartic M N Y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ IsCoprime a b ∧ N = a * b ∧
      (((M ^ 2 + 11 * N ^ 2 - Y = 64 * a ^ 4) ∧
          (M ^ 2 + 11 * N ^ 2 + Y = 2 * b ^ 4) ∧ b % 2 = 1) ∨
        ((M ^ 2 + 11 * N ^ 2 - Y = 2 * a ^ 4) ∧
          (M ^ 2 + 11 * N ^ 2 + Y = 64 * b ^ 4) ∧ a % 2 = 1)) := by
  let A : ℤ := M ^ 2 + 11 * N ^ 2
  have hAY : A ^ 2 - Y ^ 2 = 128 * N ^ 4 := by
    dsimp [A]
    simp only [Q14PlusQuartic] at h
    nlinarith
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, A = 2 * A₀ + 1 := ⟨A / 2, by
    dsimp [A] at hAodd ⊢
    omega⟩
  have hYodd : Y % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one Y with hY | hY
    · obtain ⟨y₀, hy₀⟩ : ∃ y₀, Y = 2 * y₀ := ⟨Y / 2, by omega⟩
      rw [hA₀, hy₀] at hAY
      ring_nf at hAY
      omega
    · exact hY
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, Y = 2 * y₀ + 1 := ⟨Y / 2, by omega⟩
  have hminusPos : 0 < A - Y := by
    by_contra hle
    push Not at hle
    nlinarith [hAY, pow_pos hNpos 4]
  have hplusPos : 0 < A + Y := by
    by_contra hle
    push Not at hle
    nlinarith [hAY, pow_pos hNpos 4]
  have h2minus : (2 : ℤ) ∣ A - Y := ⟨A₀ - y₀, by
    rw [hA₀, hy₀]
    ring⟩
  have h2plus : (2 : ℤ) ∣ A + Y := ⟨A₀ + y₀ + 1, by
    rw [hA₀, hy₀]
    ring⟩
  let F₁ : ℤ := (A - Y) / 2
  let F₂ : ℤ := (A + Y) / 2
  have hF₁val : 2 * F₁ = A - Y := Int.mul_ediv_cancel' h2minus
  have hF₂val : 2 * F₂ = A + Y := Int.mul_ediv_cancel' h2plus
  have hF₁pos : 0 < F₁ := by nlinarith
  have hF₂pos : 0 < F₂ := by nlinarith
  have hFprod : F₁ * F₂ = 32 * N ^ 4 := by
    have hprod : (A - Y) * (A + Y) = 128 * N ^ 4 := by
      nlinarith [hAY]
    rw [← hF₁val, ← hF₂val] at hprod
    ring_nf at hprod ⊢
    linarith
  have hAN : IsCoprime A N := by
    have hM2N : IsCoprime (M ^ 2) N := hcopMN.pow_left
    have hsum : IsCoprime (M ^ 2 + (11 * N) * N) N :=
      hM2N.add_mul_right_left (11 * N)
    simpa [A, pow_two, mul_assoc] using hsum
  have hAYcop : IsCoprime A Y := by
    by_contra hnot
    rw [Int.isCoprime_iff_gcd_eq_one] at hnot
    have hg_gt1 : 1 < Int.gcd A Y := by
      have hAne : A ≠ 0 := by
        intro hz
        rw [hz] at hA₀
        omega
      have hg_ne : Int.gcd A Y ≠ 0 := by
        rw [Int.gcd_def]
        exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr hAne)
      omega
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
    have hpA : (↑p : ℤ) ∣ A :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
    have hpY : (↑p : ℤ) ∣ Y :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hp128N : (↑p : ℤ) ∣ 128 * N ^ 4 := by
      rw [← hAY]
      exact dvd_sub (dvd_pow hpA (by norm_num : 2 ≠ 0))
        (dvd_pow hpY (by norm_num : 2 ≠ 0))
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      have : A % 2 = 0 := Int.emod_eq_zero_of_dvd hpA
      omega
    have hpN4 : (↑p : ℤ) ∣ N ^ 4 := by
      rcases hpint.dvd_or_dvd hp128N with hp128 | hpN4
      · have hp2 : (↑p : ℤ) ∣ (2 : ℤ) := by
          apply Int.Prime.dvd_pow' hp
          have hp2pow : (↑p : ℤ) ∣ (2 : ℤ) ^ 7 := by
            norm_num
            exact hp128
          exact hp2pow
        have hp_nat : p ∣ 2 := Int.natCast_dvd.mp hp2
        exact False.elim (hpne2 (Nat.le_antisymm
          (Nat.le_of_dvd (by norm_num) hp_nat) hp.two_le))
      · exact hpN4
    have hpN : (↑p : ℤ) ∣ N := Int.Prime.dvd_pow' hp hpN4
    exact hpint.not_unit (hAN.isUnit_of_dvd' hpA hpN)
  have hFcop : IsCoprime F₁ F₂ := by
    rcases hAYcop with ⟨r, s, hrs⟩
    refine ⟨r - s, r + s, ?_⟩
    have hsum : F₁ + F₂ = A := by omega
    have hdiff : F₂ - F₁ = Y := by omega
    calc
      (r - s) * F₁ + (r + s) * F₂ =
          r * (F₁ + F₂) + s * (F₂ - F₁) := by ring
      _ = 1 := by rw [hsum, hdiff]; exact hrs
  have hFprod' : F₁ * F₂ = 2 * (2 * N) ^ 4 := by
    rw [hFprod]
    ring
  obtain ⟨m, n, hmpos, hnpos, hmn, hfac⟩ :=
    coprime_factor_two_fourth hFprod' hFcop hF₁pos hF₂pos (by nlinarith : 0 < 2 * N)
  rcases hfac with hfac | hfac
  · have hrootcop : IsCoprime m n := by
      have hcop' := hFcop
      rw [hfac.1, hfac.2] at hcop'
      have hpows : IsCoprime (m ^ 4) (n ^ 4) := hcop'.of_mul_left_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
    have hnodd : n % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
      · obtain ⟨n₀, hn₀⟩ : ∃ n₀, n = 2 * n₀ := ⟨n / 2, by omega⟩
        have h2F₁ : (2 : ℤ) ∣ F₁ := by rw [hfac.1]; exact ⟨m ^ 4, rfl⟩
        have h2F₂ : (2 : ℤ) ∣ F₂ := by
          rw [hfac.2, hn₀]
          exact ⟨8 * n₀ ^ 4, by ring⟩
        exact False.elim <| (by norm_num : Prime (2 : ℤ)).not_unit
          (hFcop.isUnit_of_dvd' h2F₁ h2F₂)
      · exact hn1
    have hmeven : m % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one m with hm0 | hm1
      · exact hm0
      · obtain ⟨m₀, hm₀⟩ : ∃ m₀, m = 2 * m₀ + 1 := ⟨m / 2, by omega⟩
        obtain ⟨n₀, hn₀⟩ : ∃ n₀, n = 2 * n₀ + 1 := ⟨n / 2, by omega⟩
        rw [hm₀, hn₀] at hmn
        ring_nf at hmn
        omega
    obtain ⟨a, hma⟩ : ∃ a, m = 2 * a := ⟨m / 2, by omega⟩
    have hapos : 0 < a := by rw [hma] at hmpos; nlinarith
    have haN : a * n = N := by rw [hma] at hmn; nlinarith
    have hancop : IsCoprime a n := by
      rw [hma] at hrootcop
      exact hrootcop.of_mul_left_right
    refine ⟨a, n, hapos, hnpos, hancop, haN.symm, Or.inl ⟨?_, ?_, hnodd⟩⟩
    · dsimp [A] at hF₁val
      rw [hfac.1, hma] at hF₁val
      nlinarith
    · dsimp [A] at hF₂val
      rw [hfac.2] at hF₂val
      exact hF₂val.symm
  · have hrootcop : IsCoprime m n := by
      have hcop' := hFcop
      rw [hfac.1, hfac.2] at hcop'
      have hpows : IsCoprime (m ^ 4) (n ^ 4) := hcop'.of_mul_right_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
    have hmodd : m % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one m with hm0 | hm1
      · obtain ⟨m₀, hm₀⟩ : ∃ m₀, m = 2 * m₀ := ⟨m / 2, by omega⟩
        have h2F₁ : (2 : ℤ) ∣ F₁ := by
          rw [hfac.1, hm₀]
          exact ⟨8 * m₀ ^ 4, by ring⟩
        have h2F₂ : (2 : ℤ) ∣ F₂ := by rw [hfac.2]; exact ⟨n ^ 4, rfl⟩
        exact False.elim <| (by norm_num : Prime (2 : ℤ)).not_unit
          (hFcop.isUnit_of_dvd' h2F₁ h2F₂)
      · exact hm1
    have hneven : n % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one n with hn0 | hn1
      · exact hn0
      · obtain ⟨m₀, hm₀⟩ : ∃ m₀, m = 2 * m₀ + 1 := ⟨m / 2, by omega⟩
        obtain ⟨n₀, hn₀⟩ : ∃ n₀, n = 2 * n₀ + 1 := ⟨n / 2, by omega⟩
        rw [hm₀, hn₀] at hmn
        ring_nf at hmn
        omega
    obtain ⟨b, hnb⟩ : ∃ b, n = 2 * b := ⟨n / 2, by omega⟩
    have hbpos : 0 < b := by rw [hnb] at hnpos; nlinarith
    have hmN : m * b = N := by rw [hnb] at hmn; nlinarith
    have hmbcop : IsCoprime m b := by
      rw [hnb] at hrootcop
      exact hrootcop.of_mul_right_right
    refine ⟨m, b, hmpos, hbpos, hmbcop, hmN.symm, Or.inr ⟨?_, ?_, hmodd⟩⟩
    · dsimp [A] at hF₁val
      rw [hfac.1] at hF₁val
      exact hF₁val.symm
    · dsimp [A] at hF₂val
      rw [hfac.2, hnb] at hF₂val
      nlinarith

theorem Q14MinusQuartic_iff_swapped_plus (M N Y : ℤ) :
    Q14MinusQuartic M N Y ↔ Q14PlusQuartic N M Y := by
  simp only [Q14MinusQuartic, Q14PlusQuartic]
  constructor <;> intro h <;> nlinarith

/-- First factorization, in the orientation
`A-Y=8a⁴`, `A+Y=16b⁴`, produces the dual quartic. -/
theorem Q14_first_split_to_dual_left
    {M N Y a b : ℤ}
    (hN : N = a * b)
    (hminus : M ^ 2 + 11 * N ^ 2 - Y = 8 * a ^ 4)
    (hplus : M ^ 2 + 11 * N ^ 2 + Y = 16 * b ^ 4) :
    Q14DualQuartic (2 * a) b (2 * M) := by
  have hN2 : N ^ 2 = a ^ 2 * b ^ 2 := by
    rw [hN]
    ring
  simp only [Q14DualQuartic]
  rw [hN2] at hminus hplus
  nlinarith

/-- The opposite 2-adic orientation gives the same dual quartic after
interchanging the two fourth-power roots. -/
theorem Q14_first_split_to_dual_right
    {M N Y a b : ℤ}
    (hN : N = a * b)
    (hminus : M ^ 2 + 11 * N ^ 2 - Y = 16 * a ^ 4)
    (hplus : M ^ 2 + 11 * N ^ 2 + Y = 8 * b ^ 4) :
    Q14DualQuartic (2 * b) a (2 * M) := by
  have hN2 : N ^ 2 = a ^ 2 * b ^ 2 := by
    rw [hN]
    ring
  simp only [Q14DualQuartic]
  rw [hN2] at hminus hplus
  nlinarith

/-- The odd-midpoint orientation with the power of two on the left produces
the unscaled dual quartic. -/
theorem Q14_odd_midpoint_split_to_dual_left
    {M N Y a b : ℤ}
    (hN : N = a * b)
    (hminus : M ^ 2 + 11 * N ^ 2 - Y = 64 * a ^ 4)
    (hplus : M ^ 2 + 11 * N ^ 2 + Y = 2 * b ^ 4) :
    Q14DualQuartic b a M := by
  have hN2 : N ^ 2 = a ^ 2 * b ^ 2 := by
    rw [hN]
    ring
  simp only [Q14DualQuartic]
  rw [hN2] at hminus hplus
  nlinarith

/-- The opposite odd-midpoint orientation gives the same unscaled dual
quartic after interchanging the fourth-power roots. -/
theorem Q14_odd_midpoint_split_to_dual_right
    {M N Y a b : ℤ}
    (hN : N = a * b)
    (hminus : M ^ 2 + 11 * N ^ 2 - Y = 2 * a ^ 4)
    (hplus : M ^ 2 + 11 * N ^ 2 + Y = 64 * b ^ 4) :
    Q14DualQuartic a b M := by
  have hN2 : N ^ 2 = a ^ 2 * b ^ 2 := by
    rw [hN]
    ring
  simp only [Q14DualQuartic]
  rw [hN2] at hminus hplus
  nlinarith

theorem Q14_dual_factor_identity
    {x y Z : ℤ} (h : Q14DualQuartic x y Z) :
    (2 * Z - (2 * x ^ 2 - 11 * y ^ 2)) *
        (2 * Z + (2 * x ^ 2 - 11 * y ^ 2)) = 7 * y ^ 4 := by
  simp only [Q14DualQuartic] at h
  nlinarith

set_option maxHeartbeats 1600000 in
/-- If the second dual parameter is odd, the two positive factors of `7*y⁴`
are coprime, hence split into a fourth power and seven times a fourth power. -/
theorem Q14_dual_y_odd_second_split
    {x y Z : ℤ}
    (hyodd : y % 2 = 1)
    (hypos : 0 < y) (hZpos : 0 < Z)
    (hcopxy : IsCoprime x y)
    (hdual : Q14DualQuartic x y Z) :
    ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ IsCoprime r s ∧ y = r * s ∧
      ((2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = 7 * r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = s ^ 4) ∨
        (2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = 7 * s ^ 4)) := by
  let H : ℤ := 2 * x ^ 2 - 11 * y ^ 2
  let P : ℤ := 2 * Z - H
  let Q : ℤ := 2 * Z + H
  have hfac : P * Q = 7 * y ^ 4 := by
    dsimp [P, Q, H]
    exact Q14_dual_factor_identity hdual
  have hPpos : 0 < P := by
    dsimp [P, H]
    simp only [Q14DualQuartic] at hdual
    by_contra hle
    push Not at hle
    nlinarith [pow_pos hypos 4]
  have hQpos : 0 < Q := by
    dsimp [Q, H]
    simp only [Q14DualQuartic] at hdual
    by_contra hle
    push Not at hle
    nlinarith [pow_pos hypos 4]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y = 2 * y₀ + 1 := ⟨y / 2, by omega⟩
  have hPodd : P % 2 = 1 := by
    dsimp [P, H]
    rw [hy₀]
    ring_nf
    omega
  have hHy : IsCoprime H y := by
    have h2y : IsCoprime (2 : ℤ) y := by
      refine ⟨-y₀, 1, ?_⟩
      rw [hy₀]
      ring
    have hx2y : IsCoprime (x ^ 2) y := hcopxy.pow_left
    have h2x2y : IsCoprime (2 * x ^ 2) y := h2y.mul_left hx2y
    rcases h2x2y with ⟨r, s, hrs⟩
    refine ⟨r, s + 11 * r * y, ?_⟩
    dsimp [H]
    linear_combination hrs
  have hPQcop : IsCoprime P Q := by
    by_contra hnot
    rw [Int.isCoprime_iff_gcd_eq_one] at hnot
    have hg_gt1 : 1 < Int.gcd P Q := by
      have hg_ne : Int.gcd P Q ≠ 0 := by
        rw [Int.gcd_def]
        exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr (ne_of_gt hPpos))
      omega
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
    have hpP : (↑p : ℤ) ∣ P :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
    have hpQ : (↑p : ℤ) ∣ Q :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      have : P % 2 = 0 := Int.emod_eq_zero_of_dvd hpP
      omega
    have hp4Z : (↑p : ℤ) ∣ 4 * Z := by
      have := dvd_add hpP hpQ
      have hsum : P + Q = 4 * Z := by
        dsimp [P, Q]
        ring
      rwa [hsum] at this
    have hpZ : (↑p : ℤ) ∣ Z := by
      have hp4or := hpint.dvd_or_dvd hp4Z
      rcases hp4or with hp4 | hpZ
      · have hp2 : (↑p : ℤ) ∣ (2 : ℤ) := by
          apply Int.Prime.dvd_pow' hp
          have : (↑p : ℤ) ∣ (2 : ℤ) ^ 2 := by
            norm_num
            exact hp4
          exact this
        have hp_nat : p ∣ 2 := Int.natCast_dvd.mp hp2
        exact False.elim (hpne2 (Nat.le_antisymm
          (Nat.le_of_dvd (by norm_num) hp_nat) hp.two_le))
      · exact hpZ
    have hp2H : (↑p : ℤ) ∣ 2 * H := by
      have := dvd_sub hpQ hpP
      have hdiff : Q - P = 2 * H := by
        dsimp [P, Q]
        ring
      rwa [hdiff] at this
    have hpH : (↑p : ℤ) ∣ H :=
      (hpint.dvd_or_dvd hp2H).resolve_left (by
        intro hp2
        have hp_nat : p ∣ 2 := Int.natCast_dvd.mp hp2
        exact hpne2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hp_nat) hp.two_le))
    have hp2rhs : (↑p : ℤ) ^ 2 ∣ 7 * y ^ 4 := by
      have hpZ2 : (↑p : ℤ) ^ 2 ∣ 4 * Z ^ 2 :=
        dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpZ 2) 4
      have hpH2 : (↑p : ℤ) ^ 2 ∣ H ^ 2 :=
        pow_dvd_pow_of_dvd hpH 2
      have hd := dvd_sub hpZ2 hpH2
      have heq : 4 * Z ^ 2 - H ^ 2 = 7 * y ^ 4 := by
        dsimp [H]
        simp only [Q14DualQuartic] at hdual
        nlinarith
      rwa [heq] at hd
    have hprhs : (↑p : ℤ) ∣ 7 * y ^ 4 :=
      dvd_trans (dvd_pow_self (↑p : ℤ) (by norm_num : 2 ≠ 0)) hp2rhs
    rcases hpint.dvd_or_dvd hprhs with hp7 | hpy4
    · have hp_eq7 : p = 7 := by
        have hp_nat : p ∣ 7 := Int.natCast_dvd.mp hp7
        rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd p hp_nat with hp1 | hp7'
        · exact False.elim (hp.not_dvd_one (by simpa [hp1]))
        · exact hp7'
      subst p
      have h49 : (49 : ℤ) ∣ 7 * y ^ 4 := by
        simpa using hp2rhs
      obtain ⟨k, hk⟩ := h49
      have h7y4 : (7 : ℤ) ∣ y ^ 4 := by
        refine ⟨k, ?_⟩
        nlinarith
      have h7y : (7 : ℤ) ∣ y :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7y4
      exact (by norm_num : Prime (7 : ℤ)).not_unit
        (hHy.isUnit_of_dvd' hpH h7y)
    · have hpy : (↑p : ℤ) ∣ y := Int.Prime.dvd_pow' hp hpy4
      exact hpint.not_unit (hHy.isUnit_of_dvd' hpH hpy)
  obtain ⟨r, s, hr, hs, hrs, hsplit⟩ :=
    coprime_factor_seven_fourth hfac hPQcop hPpos hQpos hypos
  have hrscop : IsCoprime r s := by
    rcases hsplit with hsplit | hsplit
    · have hcop' := hPQcop
      rw [hsplit.1, hsplit.2] at hcop'
      have hpows : IsCoprime (r ^ 4) (s ^ 4) := hcop'.of_mul_left_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
    · have hcop' := hPQcop
      rw [hsplit.1, hsplit.2] at hcop'
      have hpows : IsCoprime (r ^ 4) (s ^ 4) := hcop'.of_mul_right_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
  exact ⟨r, s, hr, hs, hrscop, hrs.symm, by simpa [P, Q, H] using hsplit⟩

set_option maxHeartbeats 2000000 in
/-- In the odd/even dual branch, division of both factors by four leaves
positive coprime factors of `7 * (y/2)⁴`. -/
theorem Q14_dual_odd_even_second_split
    {x y Z : ℤ}
    (hxodd : x % 2 = 1) (hyeven : y % 2 = 0)
    (hypos : 0 < y) (hZpos : 0 < Z)
    (hcopxy : IsCoprime x y)
    (hdual : Q14DualQuartic x y Z) :
    ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ IsCoprime r s ∧ y = 2 * r * s ∧
      ((2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = 28 * r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = 4 * s ^ 4) ∨
        (2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = 4 * r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = 28 * s ^ 4)) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x = 2 * x₀ + 1 := ⟨x / 2, by omega⟩
  obtain ⟨u, hyu⟩ : ∃ u, y = 2 * u := ⟨y / 2, by omega⟩
  have hupos : 0 < u := by rw [hyu] at hypos; nlinarith
  have hZodd : Z % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one Z with hZ0 | hZ1
    · obtain ⟨z₀, hz₀⟩ : ∃ z₀, Z = 2 * z₀ := ⟨Z / 2, by omega⟩
      simp only [Q14DualQuartic] at hdual
      rw [hx₀, hyu, hz₀] at hdual
      ring_nf at hdual
      omega
    · exact hZ1
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, Z = 2 * z₀ + 1 := ⟨Z / 2, by omega⟩
  let H : ℤ := 2 * x ^ 2 - 11 * y ^ 2
  let P : ℤ := 2 * Z - H
  let Q : ℤ := 2 * Z + H
  have hfac : P * Q = 7 * y ^ 4 := by
    dsimp [P, Q, H]
    exact Q14_dual_factor_identity hdual
  have hPpos : 0 < P := by
    dsimp [P, H]
    simp only [Q14DualQuartic] at hdual
    by_contra hle
    push Not at hle
    nlinarith [pow_pos hypos 4]
  have hQpos : 0 < Q := by
    dsimp [Q, H]
    simp only [Q14DualQuartic] at hdual
    by_contra hle
    push Not at hle
    nlinarith [pow_pos hypos 4]
  have h4P : (4 : ℤ) ∣ P := by
    refine ⟨z₀ - 2 * x₀ ^ 2 - 2 * x₀ + 11 * u ^ 2, ?_⟩
    dsimp [P, H]
    rw [hx₀, hyu, hz₀]
    ring
  have h4Q : (4 : ℤ) ∣ Q := by
    refine ⟨z₀ + 2 * x₀ ^ 2 + 2 * x₀ + 1 - 11 * u ^ 2, ?_⟩
    dsimp [Q, H]
    rw [hx₀, hyu, hz₀]
    ring
  let P₀ : ℤ := P / 4
  let Q₀ : ℤ := Q / 4
  have hP₀val : 4 * P₀ = P := Int.mul_ediv_cancel' h4P
  have hQ₀val : 4 * Q₀ = Q := Int.mul_ediv_cancel' h4Q
  have hP₀pos : 0 < P₀ := by nlinarith
  have hQ₀pos : 0 < Q₀ := by nlinarith
  have hP₀Q₀ : P₀ * Q₀ = 7 * u ^ 4 := by
    rw [← hP₀val, ← hQ₀val, hyu] at hfac
    ring_nf at hfac ⊢
    linarith
  let K : ℤ := x ^ 2 - 22 * u ^ 2
  have hKval : 2 * K = H := by
    dsimp [K, H]
    rw [hyu]
    ring
  have hsum : P₀ + Q₀ = Z := by
    have : P + Q = 4 * Z := by
      dsimp [P, Q]
      ring
    rw [← hP₀val, ← hQ₀val] at this
    nlinarith
  have hdiff : Q₀ - P₀ = K := by
    have : Q - P = 2 * H := by
      dsimp [P, Q]
      ring
    rw [← hP₀val, ← hQ₀val, ← hKval] at this
    nlinarith
  have hxu : IsCoprime x u := by
    rw [hyu] at hcopxy
    exact hcopxy.of_mul_right_right
  have hKu : IsCoprime K u := by
    have hx2u : IsCoprime (x ^ 2) u := hxu.pow_left
    have hcop := hx2u.add_mul_right_left (-22 * u)
    have hshape : x ^ 2 + (-22 * u) * u = K := by
      dsimp [K]
      ring
    rw [hshape] at hcop
    exact hcop
  have hP₀Q₀cop : IsCoprime P₀ Q₀ := by
    by_contra hnot
    rw [Int.isCoprime_iff_gcd_eq_one] at hnot
    have hg_gt1 : 1 < Int.gcd P₀ Q₀ := by
      have hg_ne : Int.gcd P₀ Q₀ ≠ 0 := by
        rw [Int.gcd_def]
        exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr (ne_of_gt hP₀pos))
      omega
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
    have hpP : (↑p : ℤ) ∣ P₀ :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
    have hpQ : (↑p : ℤ) ∣ Q₀ :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      have h2Z : (2 : ℤ) ∣ Z := by
        rw [← hsum]
        exact dvd_add hpP hpQ
      have : Z % 2 = 0 := Int.emod_eq_zero_of_dvd h2Z
      omega
    have hpK : (↑p : ℤ) ∣ K := by
      rw [← hdiff]
      exact dvd_sub hpQ hpP
    have hp2rhs : (↑p : ℤ) ^ 2 ∣ 7 * u ^ 4 := by
      rw [← hP₀Q₀]
      simpa [pow_two] using mul_dvd_mul hpP hpQ
    have hprhs : (↑p : ℤ) ∣ 7 * u ^ 4 :=
      dvd_trans (dvd_pow_self (↑p : ℤ) (by norm_num : 2 ≠ 0)) hp2rhs
    rcases hpint.dvd_or_dvd hprhs with hp7 | hpu4
    · have hp_eq7 : p = 7 := by
        have hp_nat : p ∣ 7 := Int.natCast_dvd.mp hp7
        rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd p hp_nat with hp1 | hp7'
        · exact False.elim (hp.not_dvd_one (by simpa [hp1]))
        · exact hp7'
      subst p
      have h49 : (49 : ℤ) ∣ 7 * u ^ 4 := by simpa using hp2rhs
      obtain ⟨k, hk⟩ := h49
      have h7u4 : (7 : ℤ) ∣ u ^ 4 := by
        refine ⟨k, ?_⟩
        nlinarith
      have h7u : (7 : ℤ) ∣ u :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7u4
      exact (by norm_num : Prime (7 : ℤ)).not_unit
        (hKu.isUnit_of_dvd' hpK h7u)
    · have hpu : (↑p : ℤ) ∣ u := Int.Prime.dvd_pow' hp hpu4
      exact hpint.not_unit (hKu.isUnit_of_dvd' hpK hpu)
  obtain ⟨r, s, hr, hs, hrs, hsplit⟩ :=
    coprime_factor_seven_fourth hP₀Q₀ hP₀Q₀cop hP₀pos hQ₀pos hupos
  have hrscop : IsCoprime r s := by
    rcases hsplit with hsplit | hsplit
    · have hcop' := hP₀Q₀cop
      rw [hsplit.1, hsplit.2] at hcop'
      have hpows : IsCoprime (r ^ 4) (s ^ 4) := hcop'.of_mul_left_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
    · have hcop' := hP₀Q₀cop
      rw [hsplit.1, hsplit.2] at hcop'
      have hpows : IsCoprime (r ^ 4) (s ^ 4) := hcop'.of_mul_right_right
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hpows)
  have hyr : y = 2 * r * s := by rw [hyu, ← hrs]; ring
  refine ⟨r, s, hr, hs, hrscop, hyr, ?_⟩
  rcases hsplit with hsplit | hsplit
  · left
    constructor
    · have hp := congrArg (fun t : ℤ => 4 * t) hsplit.1
      rw [hP₀val] at hp
      calc
        2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = 4 * (7 * r ^ 4) := by
          simpa [P, H] using hp
        _ = 28 * r ^ 4 := by ring
    · have hq := congrArg (fun t : ℤ => 4 * t) hsplit.2
      rw [hQ₀val] at hq
      simpa [Q, H] using hq
  · right
    constructor
    · have hp := congrArg (fun t : ℤ => 4 * t) hsplit.1
      rw [hP₀val] at hp
      simpa [P, H, mul_assoc] using hp
    · have hq := congrArg (fun t : ℤ => 4 * t) hsplit.2
      rw [hQ₀val] at hq
      calc
        2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = 4 * (7 * s ^ 4) := by
          simpa [Q, H] using hq
        _ = 28 * s ^ 4 := by ring

/-- A `7·fourth-power` split of the dual quartic either lands on the
already impossible `d=-1` quartic or produces a new `d=-7` solution. -/
theorem Q14_second_split_from_dual
    {x y Z r s : ℤ}
    (hy : y = r * s)
    (hleft_right :
      ((2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = 7 * r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = s ^ 4) ∨
        (2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = 7 * s ^ 4))) :
    Q14MinusQuartic r s (2 * x) ∨
      (2 * x) ^ 2 = -r ^ 4 + 22 * r ^ 2 * s ^ 2 + 7 * s ^ 4 := by
  have hy2 : y ^ 2 = r ^ 2 * s ^ 2 := by
    rw [hy]
    ring
  rcases hleft_right with h | h
  · left
    simp only [Q14MinusQuartic]
    rw [hy2] at h
    nlinarith [h.1, h.2]
  · right
    rw [hy2] at h
    nlinarith [h.1, h.2]

/-- Algebraic output of the normalized odd/even dual split. -/
theorem Q14_second_split_from_dual_even_y
    {x y Z r s : ℤ}
    (hy : y = 2 * r * s)
    (hleft_right :
      ((2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = 28 * r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = 4 * s ^ 4) ∨
        (2 * Z - (2 * x ^ 2 - 11 * y ^ 2) = 4 * r ^ 4 ∧
          2 * Z + (2 * x ^ 2 - 11 * y ^ 2) = 28 * s ^ 4))) :
    Q14MinusQuartic r s x ∨
      x ^ 2 = -r ^ 4 + 22 * r ^ 2 * s ^ 2 + 7 * s ^ 4 := by
  have hy2 : y ^ 2 = 4 * r ^ 2 * s ^ 2 := by
    rw [hy]
    ring
  rcases hleft_right with h | h
  · left
    simp only [Q14MinusQuartic]
    rw [hy2] at h
    nlinarith [h.1, h.2]
  · right
    rw [hy2] at h
    nlinarith [h.1, h.2]

private lemma positive_coprime_sq_eq_one
    {r s : ℤ} (hr : 0 < r) (hs : 0 < s)
    (hcop : IsCoprime r s) (heq : r ^ 2 = s ^ 2) :
    r = 1 ∧ s = 1 := by
  have hrs : r = s := (sq_eq_sq₀ hr.le hs.le).mp heq
  have hunit : IsUnit r := hcop.isUnit_of_dvd' (dvd_refl r) (by rw [hrs])
  rcases Int.isUnit_iff.mp hunit with hr1 | hr1
  · exact ⟨hr1, by simpa [hrs] using hr1⟩
  · nlinarith

private lemma Q14MinusQuartic_T_sq_eq_sixteen_of_sq_eq
    {r s T : ℤ} (hr : 0 < r) (hs : 0 < s)
    (hcop : IsCoprime r s) (hminus : Q14MinusQuartic r s T)
    (heq : r ^ 2 = s ^ 2) :
    T ^ 2 = 16 := by
  obtain ⟨hr1, hs1⟩ := positive_coprime_sq_eq_one hr hs hcop heq
  simp only [Q14MinusQuartic] at hminus
  rw [hr1, hs1] at hminus
  norm_num at hminus ⊢
  exact hminus

set_option maxHeartbeats 2400000 in
/-- The both-odd `d=1` branch either is the base solution or yields a
primitive `d=-7` solution with both positive parameters strictly smaller. -/
theorem Q14_plus_both_odd_strict_descent
    {M N Y : ℤ}
    (hM : M % 2 = 1) (hNodd : N % 2 = 1)
    (hNpos : 0 < N) (hcopMN : IsCoprime M N)
    (hplus : Q14PlusQuartic M N Y) :
    M ^ 2 = N ^ 2 ∨
      ∃ r s T : ℤ, 0 < r ∧ 0 < s ∧ IsCoprime r s ∧
        Q14MinusQuartic r s T ∧ r ^ 2 ≠ s ^ 2 ∧ r < N ∧ s < N := by
  have hMne : M ≠ 0 := by
    intro hM0
    subst M
    simp only [Q14PlusQuartic, zero_pow (by norm_num : 4 ≠ 0),
      zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_add] at hplus
    nlinarith [sq_nonneg Y, pow_pos hNpos 4]
  obtain ⟨a, b, ha, hb, habcop, hNab, hfirst⟩ :=
    Q14_plus_both_odd_first_split hM hNodd hNpos hcopMN hplus
  have haodd : a % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one a with ha0 | ha1
    · have h2a : (2 : ℤ) ∣ a := ⟨a / 2, by omega⟩
      have h2N : (2 : ℤ) ∣ N := by
        rw [hNab]
        exact dvd_mul_of_dvd_left h2a b
      have : N % 2 = 0 := Int.emod_eq_zero_of_dvd h2N
      omega
    · exact ha1
  have hbodd : b % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one b with hb0 | hb1
    · have h2b : (2 : ℤ) ∣ b := ⟨b / 2, by omega⟩
      have h2N : (2 : ℤ) ∣ N := by
        rw [hNab]
        exact dvd_mul_of_dvd_right h2b a
      have : N % 2 = 0 := Int.emod_eq_zero_of_dvd h2N
      omega
    · exact hb1
  have h2Mpos : 0 < |2 * M| := abs_pos.mpr (mul_ne_zero (by norm_num) hMne)
  rcases hfirst with hfirst | hfirst
  · have hdual0 : Q14DualQuartic (2 * a) b (2 * M) :=
      Q14_first_split_to_dual_left hNab hfirst.1 hfirst.2
    have hdual : Q14DualQuartic (2 * a) b |2 * M| := by
      simp only [Q14DualQuartic] at hdual0 ⊢
      rw [sq_abs]
      exact hdual0
    have h2b : IsCoprime (2 : ℤ) b := by
      obtain ⟨b₀, hb₀⟩ : ∃ b₀, b = 2 * b₀ + 1 := ⟨b / 2, by omega⟩
      refine ⟨-b₀, 1, ?_⟩
      rw [hb₀]
      ring
    have hcop2ab : IsCoprime (2 * a) b := h2b.mul_left habcop
    obtain ⟨r, s, hr, hs, hrscop, hbrs, hsplit⟩ :=
      Q14_dual_y_odd_second_split
        (x := 2 * a) (y := b) (Z := |2 * M|)
        hbodd hb h2Mpos hcop2ab hdual
    have hreturn := Q14_second_split_from_dual hbrs hsplit
    have hminus : Q14MinusQuartic r s (2 * (2 * a)) := by
      rcases hreturn with hminus | himpossible
      · exact hminus
      · exact False.elim <| Q14_quartic_d_neg_one_no_solution
          (M := r) (N := s) (Y := 2 * (2 * a)) hs hrscop himpossible
    have hNars : N = (a * r) * s := by
      rw [hNab, hbrs]
      ring
    have hrN_or_base : r < N ∨ M ^ 2 = N ^ 2 := by
      by_cases hrN : r < N
      · exact Or.inl hrN
      · right
        have has_ge_one : 1 ≤ a * s := by
          have := mul_pos ha hs
          omega
        have hrle : r ≤ N := by
          rw [hNars]
          have : r ≤ (a * s) * r := le_mul_of_one_le_left hr.le has_ge_one
          nlinarith
        have hrEq : r = N := by omega
        have has : a * s = 1 := by
          have hzero : (a * s - 1) * r = 0 := by
            rw [hrEq] at hNars
            nlinarith
          exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hr))
        have ha1 : a = 1 := by nlinarith
        have hs1 : s = 1 := by nlinarith
        have hr1 : r = 1 := by
          have hq : (r ^ 2 - 1) * (7 * r ^ 2 - 15) = 0 := by
            simp only [Q14MinusQuartic] at hminus
            rw [ha1, hs1] at hminus
            norm_num at hminus
            calc
              (r ^ 2 - 1) * (7 * r ^ 2 - 15) =
                  7 * r ^ 4 - 22 * r ^ 2 + 15 := by ring
              _ = 0 := by nlinarith
          rcases mul_eq_zero.mp hq with hq | hq
          · have : r ^ 2 = 1 := sub_eq_zero.mp hq
            nlinarith
          · omega
        have hb1 : b = 1 := by rw [hbrs, hr1, hs1]; norm_num
        have hN1 : N = 1 := by rw [hNab, ha1, hb1]; norm_num
        rw [hN1, ha1, hb1] at hfirst
        norm_num at hfirst ⊢
        nlinarith [hfirst.1, hfirst.2]
    by_cases hsN : s < N
    · rcases hrN_or_base with hrN | hbase
      · by_cases hneq : r ^ 2 ≠ s ^ 2
        · exact Or.inr ⟨r, s, 2 * (2 * a), hr, hs, hrscop, hminus,
            hneq, hrN, hsN⟩
        · have heq : r ^ 2 = s ^ 2 := not_ne_iff.mp hneq
          obtain ⟨hr1, hs1⟩ := positive_coprime_sq_eq_one hr hs hrscop heq
          have h4aSq := Q14MinusQuartic_T_sq_eq_sixteen_of_sq_eq
            hr hs hrscop hminus heq
          have h4a4 : 2 * (2 * a) = 4 :=
            (sq_eq_sq₀ (by nlinarith : (0 : ℤ) ≤ 2 * (2 * a))
              (by norm_num : (0 : ℤ) ≤ 4)).mp (by
                norm_num
                exact h4aSq)
          have ha1 : a = 1 := by nlinarith
          have hb1 : b = 1 := by rw [hbrs, hr1, hs1]; norm_num
          have hN1 : N = 1 := by rw [hNab, ha1, hb1]; norm_num
          left
          rw [hN1, ha1, hb1] at hfirst
          norm_num at hfirst ⊢
          nlinarith [hfirst.1, hfirst.2]
      · exact Or.inl hbase
    · have hsEq : s = N := by
        have hsle : s ≤ N := by
          rw [hNars]
          have har_ge_one : 1 ≤ a * r := by
            have := mul_pos ha hr
            omega
          exact le_mul_of_one_le_left hs.le har_ge_one
        omega
      have har : a * r = 1 := by
        have hzero : (a * r - 1) * s = 0 := by
          rw [hsEq] at hNars
          nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hs))
      have ha1 : a = 1 := by nlinarith
      have hr1 : r = 1 := by nlinarith
      have hs1 : s = 1 := by
        have hq : (s ^ 2 - 1) * (s ^ 2 + 23) = 0 := by
          simp only [Q14MinusQuartic] at hminus
          rw [hr1, ha1] at hminus
          norm_num at hminus
          calc
            (s ^ 2 - 1) * (s ^ 2 + 23) = s ^ 4 + 22 * s ^ 2 - 23 := by ring
            _ = 0 := by nlinarith
        rcases mul_eq_zero.mp hq with hq | hq
        · have hs2 : s ^ 2 = 1 := sub_eq_zero.mp hq
          nlinarith
        · nlinarith [sq_nonneg s]
      have hb1 : b = 1 := by rw [hbrs, hr1, hs1]; norm_num
      have hN1 : N = 1 := by rw [hNab, ha1, hb1]; norm_num
      left
      rw [hN1, ha1, hb1] at hfirst
      norm_num at hfirst ⊢
      nlinarith [hfirst.1, hfirst.2]
  · have hdual0 : Q14DualQuartic (2 * b) a (2 * M) :=
      Q14_first_split_to_dual_right hNab hfirst.1 hfirst.2
    have hdual : Q14DualQuartic (2 * b) a |2 * M| := by
      simp only [Q14DualQuartic] at hdual0 ⊢
      rw [sq_abs]
      exact hdual0
    have h2a : IsCoprime (2 : ℤ) a := by
      obtain ⟨a₀, ha₀⟩ : ∃ a₀, a = 2 * a₀ + 1 := ⟨a / 2, by omega⟩
      refine ⟨-a₀, 1, ?_⟩
      rw [ha₀]
      ring
    have hcop2ba : IsCoprime (2 * b) a := h2a.mul_left habcop.symm
    obtain ⟨r, s, hr, hs, hrscop, hars, hsplit⟩ :=
      Q14_dual_y_odd_second_split
        (x := 2 * b) (y := a) (Z := |2 * M|)
        haodd ha h2Mpos hcop2ba hdual
    have hreturn := Q14_second_split_from_dual hars hsplit
    have hminus : Q14MinusQuartic r s (2 * (2 * b)) := by
      rcases hreturn with hminus | himpossible
      · exact hminus
      · exact False.elim <| Q14_quartic_d_neg_one_no_solution
          (M := r) (N := s) (Y := 2 * (2 * b)) hs hrscop himpossible
    have hNbrs : N = (b * r) * s := by
      rw [hNab, hars]
      ring
    have hrN_or_base : r < N ∨ M ^ 2 = N ^ 2 := by
      by_cases hrN : r < N
      · exact Or.inl hrN
      · right
        have hbs_ge_one : 1 ≤ b * s := by
          have := mul_pos hb hs
          omega
        have hrle : r ≤ N := by
          rw [hNbrs]
          have : r ≤ (b * s) * r := le_mul_of_one_le_left hr.le hbs_ge_one
          nlinarith
        have hrEq : r = N := by omega
        have hbs : b * s = 1 := by
          have hzero : (b * s - 1) * r = 0 := by
            rw [hrEq] at hNbrs
            nlinarith
          exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hr))
        have hb1 : b = 1 := by nlinarith
        have hs1 : s = 1 := by nlinarith
        have hr1 : r = 1 := by
          have hq : (r ^ 2 - 1) * (7 * r ^ 2 - 15) = 0 := by
            simp only [Q14MinusQuartic] at hminus
            rw [hb1, hs1] at hminus
            norm_num at hminus
            calc
              (r ^ 2 - 1) * (7 * r ^ 2 - 15) =
                  7 * r ^ 4 - 22 * r ^ 2 + 15 := by ring
              _ = 0 := by nlinarith
          rcases mul_eq_zero.mp hq with hq | hq
          · have : r ^ 2 = 1 := sub_eq_zero.mp hq
            nlinarith
          · omega
        have ha1 : a = 1 := by rw [hars, hr1, hs1]; norm_num
        have hN1 : N = 1 := by rw [hNab, ha1, hb1]; norm_num
        rw [hN1, ha1, hb1] at hfirst
        norm_num at hfirst ⊢
        nlinarith [hfirst.1, hfirst.2]
    by_cases hsN : s < N
    · rcases hrN_or_base with hrN | hbase
      · by_cases hneq : r ^ 2 ≠ s ^ 2
        · exact Or.inr ⟨r, s, 2 * (2 * b), hr, hs, hrscop, hminus,
            hneq, hrN, hsN⟩
        · have heq : r ^ 2 = s ^ 2 := not_ne_iff.mp hneq
          obtain ⟨hr1, hs1⟩ := positive_coprime_sq_eq_one hr hs hrscop heq
          have h4bSq := Q14MinusQuartic_T_sq_eq_sixteen_of_sq_eq
            hr hs hrscop hminus heq
          have h4b4 : 2 * (2 * b) = 4 :=
            (sq_eq_sq₀ (by nlinarith : (0 : ℤ) ≤ 2 * (2 * b))
              (by norm_num : (0 : ℤ) ≤ 4)).mp (by
                norm_num
                exact h4bSq)
          have hb1 : b = 1 := by nlinarith
          have ha1 : a = 1 := by rw [hars, hr1, hs1]; norm_num
          have hN1 : N = 1 := by rw [hNab, ha1, hb1]; norm_num
          left
          rw [hN1, ha1, hb1] at hfirst
          norm_num at hfirst ⊢
          nlinarith [hfirst.1, hfirst.2]
      · exact Or.inl hbase
    · have hsEq : s = N := by
        have hsle : s ≤ N := by
          rw [hNbrs]
          have hbr_ge_one : 1 ≤ b * r := by
            have := mul_pos hb hr
            omega
          exact le_mul_of_one_le_left hs.le hbr_ge_one
        omega
      have hbr : b * r = 1 := by
        have hzero : (b * r - 1) * s = 0 := by
          rw [hsEq] at hNbrs
          nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hs))
      have hb1 : b = 1 := by nlinarith
      have hr1 : r = 1 := by nlinarith
      have hs1 : s = 1 := by
        have hq : (s ^ 2 - 1) * (s ^ 2 + 23) = 0 := by
          simp only [Q14MinusQuartic] at hminus
          rw [hr1, hb1] at hminus
          norm_num at hminus
          calc
            (s ^ 2 - 1) * (s ^ 2 + 23) = s ^ 4 + 22 * s ^ 2 - 23 := by ring
            _ = 0 := by nlinarith
        rcases mul_eq_zero.mp hq with hq | hq
        · have hs2 : s ^ 2 = 1 := sub_eq_zero.mp hq
          nlinarith
        · nlinarith [sq_nonneg s]
      have ha1 : a = 1 := by rw [hars, hr1, hs1]; norm_num
      have hN1 : N = 1 := by rw [hNab, ha1, hb1]; norm_num
      left
      rw [hN1, ha1, hb1] at hfirst
      norm_num at hfirst ⊢
      nlinarith [hfirst.1, hfirst.2]

set_option maxHeartbeats 2400000 in
/-- If the midpoint is odd, the `d=1` quartic always yields a primitive
`d=-7` solution with both positive parameters strictly smaller. -/
theorem Q14_plus_odd_midpoint_strict_descent
    {M N Y : ℤ}
    (hAodd : (M ^ 2 + 11 * N ^ 2) % 2 = 1)
    (hNpos : 0 < N) (hcopMN : IsCoprime M N)
    (hplus : Q14PlusQuartic M N Y) :
    ∃ r s T : ℤ, 0 < r ∧ 0 < s ∧ IsCoprime r s ∧
      Q14MinusQuartic r s T ∧ r ^ 2 ≠ s ^ 2 ∧ r < N ∧ s < N := by
  have hMne : M ≠ 0 := by
    intro hM0
    subst M
    simp only [Q14PlusQuartic, zero_pow (by norm_num : 4 ≠ 0),
      zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_add] at hplus
    nlinarith [sq_nonneg Y, pow_pos hNpos 4]
  have hMabspos : 0 < |M| := abs_pos.mpr hMne
  obtain ⟨a, b, ha, hb, habcop, hNab, hfirst⟩ :=
    Q14_plus_odd_midpoint_first_split hAodd hNpos hcopMN hplus
  rcases hfirst with hfirst | hfirst
  · have hdual0 : Q14DualQuartic b a M :=
      Q14_odd_midpoint_split_to_dual_left hNab hfirst.1 hfirst.2.1
    have hdual : Q14DualQuartic b a |M| := by
      simp only [Q14DualQuartic] at hdual0 ⊢
      rw [sq_abs]
      exact hdual0
    rcases Int.emod_two_eq_zero_or_one a with haeven | haodd
    · obtain ⟨r, s, hr, hs, hrscop, hars, hsplit⟩ :=
        Q14_dual_odd_even_second_split
          (x := b) (y := a) (Z := |M|)
          hfirst.2.2 haeven ha hMabspos habcop.symm hdual
      have hreturn := Q14_second_split_from_dual_even_y hars hsplit
      have hminus : Q14MinusQuartic r s b := by
        rcases hreturn with hminus | himpossible
        · exact hminus
        · exact False.elim <| Q14_quartic_d_neg_one_no_solution
            (M := r) (N := s) (Y := b) hs hrscop himpossible
      have hsN : s < N := by
        have hfactor : 1 < 2 * r * b := by
          have hrb := mul_pos hr hb
          nlinarith
        calc
          s < s * (2 * r * b) := lt_mul_of_one_lt_right hs hfactor
          _ = N := by rw [hNab, hars]; ring
      have hrN : r < N := by
        have hfactor : 1 < 2 * s * b := by
          have hsb := mul_pos hs hb
          nlinarith
        calc
          r < r * (2 * s * b) := lt_mul_of_one_lt_right hr hfactor
          _ = N := by rw [hNab, hars]; ring
      have hneq : r ^ 2 ≠ s ^ 2 := by
        intro heq
        have hbSq := Q14MinusQuartic_T_sq_eq_sixteen_of_sq_eq
          hr hs hrscop hminus heq
        have hb4 : b = 4 := (sq_eq_sq₀ hb.le (by norm_num : (0 : ℤ) ≤ 4)).mp (by
          norm_num
          exact hbSq)
        rw [hb4] at hfirst
        norm_num at hfirst
      exact ⟨r, s, b, hr, hs, hrscop, hminus, hneq, hrN, hsN⟩
    · obtain ⟨r, s, hr, hs, hrscop, hars, hsplit⟩ :=
        Q14_dual_y_odd_second_split
          (x := b) (y := a) (Z := |M|)
          haodd ha hMabspos habcop.symm hdual
      have hreturn := Q14_second_split_from_dual hars hsplit
      have hminus : Q14MinusQuartic r s (2 * b) := by
        rcases hreturn with hminus | himpossible
        · exact hminus
        · exact False.elim <| Q14_quartic_d_neg_one_no_solution
            (M := r) (N := s) (Y := 2 * b) hs hrscop himpossible
      have hNbrs : N = (b * r) * s := by
        rw [hNab, hars]
        ring
      have hrN : r < N := by
        by_contra hnot
        have hbs_ge_one : 1 ≤ b * s := by
          have := mul_pos hb hs
          omega
        have hrle : r ≤ N := by
          rw [hNbrs]
          have : r ≤ (b * s) * r := le_mul_of_one_le_left hr.le hbs_ge_one
          nlinarith
        have hrEq : r = N := by omega
        have hbs : b * s = 1 := by
          have hzero : (b * s - 1) * r = 0 := by
            rw [hrEq] at hNbrs
            nlinarith
          exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hr))
        have hb1 : b = 1 := by nlinarith
        have hs1 : s = 1 := by nlinarith
        simp only [Q14MinusQuartic] at hminus
        rw [hb1, hs1] at hminus
        norm_num at hminus
        have hq : (r ^ 2 - 3) * (7 * r ^ 2 - 1) = 0 := by
          calc
            (r ^ 2 - 3) * (7 * r ^ 2 - 1) =
                7 * r ^ 4 - 22 * r ^ 2 + 3 := by ring
            _ = 0 := by nlinarith
        rcases mul_eq_zero.mp hq with hq | hq
        · have hr2 : r ^ 2 = 3 := sub_eq_zero.mp hq
          rcases Int.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
          · rw [hk] at hr2
            ring_nf at hr2
            omega
          · rw [hk] at hr2
            ring_nf at hr2
            omega
        · omega
      have hneq : r ^ 2 ≠ s ^ 2 := by
        intro heq
        have h2bSq := Q14MinusQuartic_T_sq_eq_sixteen_of_sq_eq
          hr hs hrscop hminus heq
        have h2b4 : 2 * b = 4 :=
          (sq_eq_sq₀ (by nlinarith : (0 : ℤ) ≤ 2 * b)
            (by norm_num : (0 : ℤ) ≤ 4)).mp (by
              norm_num
              exact h2bSq)
        have hb2 : b = 2 := by nlinarith
        rw [hb2] at hfirst
        norm_num at hfirst
      by_cases hsN : s < N
      · exact ⟨r, s, 2 * b, hr, hs, hrscop, hminus, hneq, hrN, hsN⟩
      · have hsEq : s = N := by
          have hbr_ge_one : 1 ≤ b * r := by
            have := mul_pos hb hr
            omega
          have hsle : s ≤ N := by
            rw [hNbrs]
            exact le_mul_of_one_le_left hs.le hbr_ge_one
          omega
        have hbr : b * r = 1 := by
          have hzero : (b * r - 1) * s = 0 := by
            rw [hsEq] at hNbrs
            nlinarith
          exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hs))
        have hb1 : b = 1 := by nlinarith
        have hr1 : r = 1 := by nlinarith
        simp only [Q14MinusQuartic] at hminus
        rw [hb1, hr1] at hminus
        norm_num at hminus
        have hs2 : 1 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
        have hs4 : 1 ≤ s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 1)]
        nlinarith
  · have hdual0 : Q14DualQuartic a b M :=
      Q14_odd_midpoint_split_to_dual_right hNab hfirst.1 hfirst.2.1
    have hdual : Q14DualQuartic a b |M| := by
      simp only [Q14DualQuartic] at hdual0 ⊢
      rw [sq_abs]
      exact hdual0
    rcases Int.emod_two_eq_zero_or_one b with hbeven | hbodd
    · obtain ⟨r, s, hr, hs, hrscop, hbrs, hsplit⟩ :=
        Q14_dual_odd_even_second_split
          (x := a) (y := b) (Z := |M|)
          hfirst.2.2 hbeven hb hMabspos habcop hdual
      have hreturn := Q14_second_split_from_dual_even_y hbrs hsplit
      have hminus : Q14MinusQuartic r s a := by
        rcases hreturn with hminus | himpossible
        · exact hminus
        · exact False.elim <| Q14_quartic_d_neg_one_no_solution
            (M := r) (N := s) (Y := a) hs hrscop himpossible
      have hsN : s < N := by
        have hfactor : 1 < 2 * r * a := by
          have hra := mul_pos hr ha
          nlinarith
        calc
          s < s * (2 * r * a) := lt_mul_of_one_lt_right hs hfactor
          _ = N := by rw [hNab, hbrs]; ring
      have hrN : r < N := by
        have hfactor : 1 < 2 * s * a := by
          have hsa := mul_pos hs ha
          nlinarith
        calc
          r < r * (2 * s * a) := lt_mul_of_one_lt_right hr hfactor
          _ = N := by rw [hNab, hbrs]; ring
      have hneq : r ^ 2 ≠ s ^ 2 := by
        intro heq
        have haSq := Q14MinusQuartic_T_sq_eq_sixteen_of_sq_eq
          hr hs hrscop hminus heq
        have ha4 : a = 4 := (sq_eq_sq₀ ha.le (by norm_num : (0 : ℤ) ≤ 4)).mp (by
          norm_num
          exact haSq)
        rw [ha4] at hfirst
        norm_num at hfirst
      exact ⟨r, s, a, hr, hs, hrscop, hminus, hneq, hrN, hsN⟩
    · obtain ⟨r, s, hr, hs, hrscop, hbrs, hsplit⟩ :=
        Q14_dual_y_odd_second_split
          (x := a) (y := b) (Z := |M|)
          hbodd hb hMabspos habcop hdual
      have hreturn := Q14_second_split_from_dual hbrs hsplit
      have hminus : Q14MinusQuartic r s (2 * a) := by
        rcases hreturn with hminus | himpossible
        · exact hminus
        · exact False.elim <| Q14_quartic_d_neg_one_no_solution
            (M := r) (N := s) (Y := 2 * a) hs hrscop himpossible
      have hNars : N = (a * r) * s := by
        rw [hNab, hbrs]
        ring
      have hrN : r < N := by
        by_contra hnot
        have has_ge_one : 1 ≤ a * s := by
          have := mul_pos ha hs
          omega
        have hrle : r ≤ N := by
          rw [hNars]
          have : r ≤ (a * s) * r := le_mul_of_one_le_left hr.le has_ge_one
          nlinarith
        have hrEq : r = N := by omega
        have has : a * s = 1 := by
          have hzero : (a * s - 1) * r = 0 := by
            rw [hrEq] at hNars
            nlinarith
          exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hr))
        have ha1 : a = 1 := by nlinarith
        have hs1 : s = 1 := by nlinarith
        simp only [Q14MinusQuartic] at hminus
        rw [ha1, hs1] at hminus
        norm_num at hminus
        have hq : (r ^ 2 - 3) * (7 * r ^ 2 - 1) = 0 := by
          calc
            (r ^ 2 - 3) * (7 * r ^ 2 - 1) =
                7 * r ^ 4 - 22 * r ^ 2 + 3 := by ring
            _ = 0 := by nlinarith
        rcases mul_eq_zero.mp hq with hq | hq
        · have hr2 : r ^ 2 = 3 := sub_eq_zero.mp hq
          rcases Int.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
          · rw [hk] at hr2
            ring_nf at hr2
            omega
          · rw [hk] at hr2
            ring_nf at hr2
            omega
        · omega
      have hneq : r ^ 2 ≠ s ^ 2 := by
        intro heq
        have h2aSq := Q14MinusQuartic_T_sq_eq_sixteen_of_sq_eq
          hr hs hrscop hminus heq
        have h2a4 : 2 * a = 4 :=
          (sq_eq_sq₀ (by nlinarith : (0 : ℤ) ≤ 2 * a)
            (by norm_num : (0 : ℤ) ≤ 4)).mp (by
              norm_num
              exact h2aSq)
        have ha2 : a = 2 := by nlinarith
        rw [ha2] at hfirst
        norm_num at hfirst
      by_cases hsN : s < N
      · exact ⟨r, s, 2 * a, hr, hs, hrscop, hminus, hneq, hrN, hsN⟩
      · have hsEq : s = N := by
          have har_ge_one : 1 ≤ a * r := by
            have := mul_pos ha hr
            omega
          have hsle : s ≤ N := by
            rw [hNars]
            exact le_mul_of_one_le_left hs.le har_ge_one
          omega
        have har : a * r = 1 := by
          have hzero : (a * r - 1) * s = 0 := by
            rw [hsEq] at hNars
            nlinarith
          exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hs))
        have ha1 : a = 1 := by nlinarith
        have hr1 : r = 1 := by nlinarith
        simp only [Q14MinusQuartic] at hminus
        rw [ha1, hr1] at hminus
        norm_num at hminus
        have hs2 : 1 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
        have hs4 : 1 ≤ s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 1)]
        nlinarith

set_option maxHeartbeats 2400000 in
/-- Uniform one-step descent for every primitive `d=1` quartic solution. -/
theorem Q14_plus_strict_descent
    {M N Y : ℤ}
    (hNpos : 0 < N) (hcopMN : IsCoprime M N)
    (hplus : Q14PlusQuartic M N Y) :
    M ^ 2 = N ^ 2 ∨
      ∃ r s T : ℤ, 0 < r ∧ 0 < s ∧ IsCoprime r s ∧
        Q14MinusQuartic r s T ∧ r ^ 2 ≠ s ^ 2 ∧ r < N ∧ s < N := by
  rcases Int.emod_two_eq_zero_or_one M with hMeven | hModd <;>
    rcases Int.emod_two_eq_zero_or_one N with hNeven | hNodd
  · have h2M : (2 : ℤ) ∣ M := ⟨M / 2, by omega⟩
    have h2N : (2 : ℤ) ∣ N := ⟨N / 2, by omega⟩
    exact False.elim (not_both_even_of_coprime hcopMN ⟨h2M, h2N⟩)
  · have hAodd : (M ^ 2 + 11 * N ^ 2) % 2 = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, M = 2 * m := ⟨M / 2, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, N = 2 * n + 1 := ⟨N / 2, by omega⟩
      rw [hm, hn]
      ring_nf
      omega
    exact Or.inr (Q14_plus_odd_midpoint_strict_descent hAodd hNpos hcopMN hplus)
  · have hAodd : (M ^ 2 + 11 * N ^ 2) % 2 = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, M = 2 * m + 1 := ⟨M / 2, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, N = 2 * n := ⟨N / 2, by omega⟩
      rw [hm, hn]
      ring_nf
      omega
    exact Or.inr (Q14_plus_odd_midpoint_strict_descent hAodd hNpos hcopMN hplus)
  · exact Q14_plus_both_odd_strict_descent hModd hNodd hNpos hcopMN hplus

private theorem Q14_minus_descent_aux :
    ∀ n : ℕ, ∀ M N Y : ℤ,
      max M.natAbs N.natAbs ≤ n →
      0 < N → IsCoprime M N → Q14MinusQuartic M N Y →
      M = 0 ∨ M ^ 2 = N ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro M N Y hheight hNpos hcopMN hminus
      by_cases hM0 : M = 0
      · exact Or.inl hM0
      have hMabspos : 0 < |M| := abs_pos.mpr hM0
      have hplus0 : Q14PlusQuartic N M Y :=
        (Q14MinusQuartic_iff_swapped_plus M N Y).mp hminus
      have hMabs2 : |M| ^ 2 = M ^ 2 := sq_abs M
      have hMabs4 : |M| ^ 4 = M ^ 4 := by nlinarith [hMabs2]
      have hplus : Q14PlusQuartic N |M| Y := by
        simp only [Q14PlusQuartic] at hplus0 ⊢
        rw [hMabs2, hMabs4]
        exact hplus0
      have hcopplus : IsCoprime N |M| := hcopMN.symm.abs_right
      rcases Q14_plus_strict_descent hMabspos hcopplus hplus with hbase | hdesc
      · right
        nlinarith [hbase, sq_abs M]
      · obtain ⟨r, s, T, hr, hs, hrscop, hminus', hneq, hrM, hsM⟩ := hdesc
        have hrNat : r.natAbs < M.natAbs := by
          have hrZ : (r.natAbs : ℤ) < (M.natAbs : ℤ) := by
            rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_pos hr]
            exact hrM
          exact_mod_cast hrZ
        have hsNat : s.natAbs < M.natAbs := by
          have hsZ : (s.natAbs : ℤ) < (M.natAbs : ℤ) := by
            rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_pos hs]
            exact hsM
          exact_mod_cast hsZ
        have hMle : M.natAbs ≤ n :=
          le_trans (Nat.le_max_left M.natAbs N.natAbs) hheight
        have hnew : max r.natAbs s.natAbs < n := by omega
        have hclass := ih (max r.natAbs s.natAbs) hnew
          r s T le_rfl hs hrscop hminus'
        rcases hclass with hr0 | heq
        · exact False.elim (ne_of_gt hr hr0)
        · exact False.elim (hneq heq)

/-- The complete `d=-7` primitive quartic tail. -/
theorem Q14_quartic_d_neg_seven_descent_tail
    {M N Y : ℤ}
    (hNpos : 0 < N) (hcopMN : IsCoprime M N)
    (hminus : Q14MinusQuartic M N Y) :
    M = 0 ∨ M ^ 2 = N ^ 2 := by
  exact Q14_minus_descent_aux (max M.natAbs N.natAbs)
    M N Y le_rfl hNpos hcopMN hminus

/-- The complete `d=1` primitive quartic tail. -/
theorem Q14_quartic_d_one_descent_tail
    {M N Y : ℤ}
    (hNpos : 0 < N) (hcopMN : IsCoprime M N)
    (hplus : Q14PlusQuartic M N Y) :
    M ^ 2 = N ^ 2 := by
  rcases Q14_plus_strict_descent hNpos hcopMN hplus with hbase | hdesc
  · exact hbase
  · obtain ⟨r, s, T, hr, hs, hrscop, hminus, hneq, _hrN, _hsN⟩ := hdesc
    rcases Q14_quartic_d_neg_seven_descent_tail hs hrscop hminus with hr0 | heq
    · exact False.elim (ne_of_gt hr hr0)
    · exact False.elim (hneq heq)

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
  rw [mem_Q14_target_rat]
  rcases hd with hd | hd
  · subst d
    have hplus : Q14PlusQuartic M N Y := by
      simp only [Q14PlusQuartic]
      norm_num at _hdesc ⊢
      nlinarith
    have hsq := Q14_quartic_d_one_descent_tail _hN _hcop hplus
    have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt _hN)
    have hsqQ : (M : ℚ) ^ 2 = (N : ℚ) ^ 2 := by exact_mod_cast hsq
    have hratio : ((M : ℚ) / (N : ℚ)) ^ 2 = 1 := by
      rw [div_pow, hsqQ]
      exact div_self (pow_ne_zero 2 hNQ)
    have hv1 : v = 1 := by
      rw [hv, hratio]
      norm_num
    exact Or.inr (Or.inr hv1)
  · subst d
    have hminus : Q14MinusQuartic M N Y := by
      simp only [Q14MinusQuartic]
      norm_num at _hdesc ⊢
      nlinarith
    rcases Q14_quartic_d_neg_seven_descent_tail _hN _hcop hminus with hM0 | hsq
    · have hv0 : v = 0 := by rw [hv, hM0]; norm_num
      exact Or.inr (Or.inl hv0)
    · have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt _hN)
      have hsqQ : (M : ℚ) ^ 2 = (N : ℚ) ^ 2 := by exact_mod_cast hsq
      have hratio : ((M : ℚ) / (N : ℚ)) ^ 2 = 1 := by
        rw [div_pow, hsqQ]
        exact div_self (pow_ne_zero 2 hNQ)
      have hvm7 : v = -7 := by
        rw [hv, hratio]
        norm_num
      exact Or.inl hvm7

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
