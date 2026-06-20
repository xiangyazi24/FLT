import scratch.SquareStep014
import scratch.FourSquaresAP

set_option maxHeartbeats 2000000

namespace ObstructionN12

private lemma isSquare_of_isSquare_cube (q : ℕ) (h : IsSquare (q ^ 3)) :
    IsSquare q := by
  rcases h with ⟨d, hd⟩
  have hpow : q ^ 3 = d ^ 2 := by
    simpa [pow_two] using hd
  obtain ⟨c, hcq, _hcd⟩ :=
    Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
      (a := q) (b := d) (m := 3) (n := 2)
      (by decide : Nat.Coprime 3 2)
      hpow
  exact ⟨c, by simpa [pow_two] using hcq⟩

private lemma int_gcd_eq_one_of_nat_coprime {a b : ℤ}
    (h : Nat.Coprime a.natAbs b.natAbs) :
    Int.gcd a b = 1 := by
  simpa [Int.gcd_def, Nat.Coprime] using h

private lemma nat_coprime_of_int_gcd_eq_one {a b : ℤ}
    (h : Int.gcd a b = 1) :
    Nat.Coprime a.natAbs b.natAbs := by
  simpa [Int.gcd_def, Nat.Coprime] using h

private lemma n12_factor_coprime_den
    (p q : ℤ) (hpq : Nat.Coprime p.natAbs q.natAbs) :
    Nat.Coprime
      (((p - q) * (p - 2 * q) * (p + 2 * q)).natAbs)
      q.natAbs := by
  have hpqI : IsCoprime p q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact int_gcd_eq_one_of_nat_coprime hpq
  have h1 : IsCoprime (p - q) q := by
    have h := hpqI.add_mul_right_left (-1)
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h
  have h2 : IsCoprime (p - 2 * q) q := by
    have h := hpqI.add_mul_right_left (-2)
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h
  have h3 : IsCoprime (p + 2 * q) q := by
    have h := hpqI.add_mul_right_left 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hprod : IsCoprime ((p - q) * (p - 2 * q) * (p + 2 * q)) q :=
    (h1.mul_left h2).mul_left h3
  rw [Int.isCoprime_iff_gcd_eq_one] at hprod
  exact nat_coprime_of_int_gcd_eq_one hprod

private lemma rat_n12_rhs_num_den (u : ℚ) :
    let p : ℤ := u.num
    let q : ℤ := u.den
    let M : ℤ := (p - q) * (p - 2 * q) * (p + 2 * q)
    (u ^ 3 - u ^ 2 - 4 * u + 4).num = M ∧
      (u ^ 3 - u ^ 2 - 4 * u + 4).den = u.den ^ 3 := by
  classical
  let p : ℤ := u.num
  let qN : ℕ := u.den
  let q : ℤ := qN
  let M : ℤ := (p - q) * (p - 2 * q) * (p + 2 * q)
  have hqposN : 0 < qN := u.pos
  have hqpos : 0 < q := by
    dsimp [q]
    exact Int.natCast_pos.mpr hqposN
  have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hu : u = (p : ℚ) / (q : ℚ) := by
    dsimp [p, q, qN]
    exact (Rat.num_div_den u).symm
  have hrhs :
      u ^ 3 - u ^ 2 - 4 * u + 4 =
        ((M : ℤ) : ℚ) / ((q ^ 3 : ℤ) : ℚ) := by
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
    exact n12_factor_coprime_den p q hpq
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

private theorem n12_clear_denominators (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    ∃ A N C : ℤ, 0 < N ∧ Int.gcd A N = 1 ∧
      u = (A : ℚ) / ((N ^ 2 : ℤ) : ℚ) ∧
      C ^ 2 = (A - N ^ 2) * (A - 2 * N ^ 2) * (A + 2 * N ^ 2) := by
  classical
  let A : ℤ := u.num
  let qN : ℕ := u.den
  let q : ℤ := qN
  let M : ℤ := (A - q) * (A - 2 * q) * (A + 2 * q)
  have hnumden := rat_n12_rhs_num_den u
  have hnumR : (u ^ 3 - u ^ 2 - 4 * u + 4).num = M := by
    simpa [A, q, qN, M] using hnumden.1
  have hdenR : (u ^ 3 - u ^ 2 - 4 * u + 4).den = qN ^ 3 := by
    simpa [A, q, qN, M] using hnumden.2
  have hsR : IsSquare (u ^ 3 - u ^ 2 - 4 * u + 4) :=
    ⟨w, by simpa [pow_two] using h.symm⟩
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
    have hqpos : 0 < qN := u.pos
    have hN0pos : 0 < N0 := by
      by_contra hle
      have hN0zero : N0 = 0 := by omega
      rw [hN0zero] at hqN
      norm_num at hqN
      omega
    dsimp [N]
    exact_mod_cast hN0pos
  obtain ⟨C, hC⟩ := hsM
  have hpq : Nat.Coprime A.natAbs q.natAbs := by
    dsimp [A, q, qN]
    simpa [Int.natAbs_natCast] using u.reduced
  have hpqI : IsCoprime A q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact int_gcd_eq_one_of_nat_coprime hpq
  have hpN : IsCoprime A N := by
    have hpN2 : IsCoprime A (N ^ 2) := by
      simpa [hq] using hpqI
    exact (IsCoprime.pow_right_iff (x := A) (y := N) (m := 2) (by norm_num)).mp hpN2
  refine ⟨A, N, C, hNpos, Int.isCoprime_iff_gcd_eq_one.mp hpN, ?_, ?_⟩
  · have hu : u = (A : ℚ) / (q : ℚ) := by
      dsimp [A, q, qN]
      exact (Rat.num_div_den u).symm
    rw [hu, hq]
  · have hM : M = C ^ 2 := by
      simpa [pow_two] using hC
    rw [← hM]
    dsimp [M]
    rw [hq]

private lemma n12_case_111
    (A N X Y Z : ℤ) (hN : N ≠ 0)
    (h1 : A - N ^ 2 = X ^ 2)
    (h2 : A - 2 * N ^ 2 = Y ^ 2)
    (h3 : A + 2 * N ^ 2 = Z ^ 2) :
    A = 2 * N ^ 2 := by
  have hX : X ^ 2 = Y ^ 2 + N ^ 2 := by nlinarith
  have hZ : Z ^ 2 = Y ^ 2 + 4 * N ^ 2 := by nlinarith
  have hYN : Y * N = 0 := no_sq_at_0_1_4 Y X Z N hX hZ
  have hY0 : Y = 0 := by
    rcases mul_eq_zero.mp hYN with hY | hN0
    · exact hY
    · exact False.elim (hN hN0)
  nlinarith

private lemma n12_case_326
    (A N X Y Z : ℤ)
    (h1 : A - N ^ 2 = 3 * X ^ 2)
    (h2 : A - 2 * N ^ 2 = 2 * Y ^ 2)
    (h3 : A + 2 * N ^ 2 = 6 * Z ^ 2) :
    A = 4 * N ^ 2 := by
  let Δ : ℤ := Z ^ 2 - N ^ 2
  have hz : Z ^ 2 = N ^ 2 + Δ := by dsimp [Δ]; ring
  have hx : X ^ 2 = N ^ 2 + 2 * Δ := by
    dsimp [Δ]
    nlinarith
  have hy : Y ^ 2 = N ^ 2 + 3 * Δ := by
    dsimp [Δ]
    nlinarith
  have hΔ : Δ = 0 := FourSquaresAP.no_four_sq_AP N Z X Y Δ hz hx hy
  have hZeq : Z ^ 2 = N ^ 2 := by
    dsimp [Δ] at hΔ
    nlinarith
  nlinarith

private lemma n12_case_m1m22
    (A N X Y Z : ℤ)
    (h1 : A - N ^ 2 = -(X ^ 2))
    (h2 : A - 2 * N ^ 2 = -(2 * Y ^ 2))
    (h3 : A + 2 * N ^ 2 = 2 * Z ^ 2) :
    A = 0 := by
  let Δ : ℤ := Y ^ 2 - N ^ 2
  have hsum : Z ^ 2 + Y ^ 2 = 2 * N ^ 2 := by nlinarith
  have hXeq : X ^ 2 = 2 * Y ^ 2 - N ^ 2 := by nlinarith
  have hN : N ^ 2 = Z ^ 2 + Δ := by
    dsimp [Δ]
    nlinarith
  have hY : Y ^ 2 = Z ^ 2 + 2 * Δ := by
    dsimp [Δ]
    nlinarith
  have hX : X ^ 2 = Z ^ 2 + 3 * Δ := by
    dsimp [Δ]
    nlinarith
  have hΔ : Δ = 0 := FourSquaresAP.no_four_sq_AP Z N Y X Δ hN hY hX
  have hYN : Y ^ 2 = N ^ 2 := by
    dsimp [Δ] at hΔ
    nlinarith
  nlinarith

private lemma n12_case_m3m13
    (A N X Y Z : ℤ)
    (h1 : A - N ^ 2 = -(3 * X ^ 2))
    (h2 : A - 2 * N ^ 2 = -(Y ^ 2))
    (h3 : A + 2 * N ^ 2 = 3 * Z ^ 2) :
    A = N ^ 2 ∨ A = -2 * N ^ 2 := by
  have hN : N ^ 2 = Z ^ 2 + X ^ 2 := by nlinarith
  have hY : Y ^ 2 = Z ^ 2 + 4 * X ^ 2 := by nlinarith
  have hZX : Z * X = 0 := no_sq_at_0_1_4 Z N Y X hN hY
  rcases mul_eq_zero.mp hZX with hZ0 | hX0
  · right
    nlinarith
  · left
    nlinarith

private lemma int_mod_three_cases (z : ℤ) :
    (∃ q : ℤ, z = 3 * q) ∨
      (∃ q : ℤ, z = 3 * q + 1) ∨
        (∃ q : ℤ, z = 3 * q - 1) := by
  have hm : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases hm with h | h | h
  · left; exact ⟨z / 3, by omega⟩
  · right; left; exact ⟨z / 3, by omega⟩
  · right; right; exact ⟨z / 3 + 1, by omega⟩

private lemma n12_case_122_false
    (X Y Z N : ℤ) (hcopYN : Int.gcd Y N = 1)
    (hA : X ^ 2 - 2 * Y ^ 2 = N ^ 2)
    (hB : 2 * Z ^ 2 - X ^ 2 = 3 * N ^ 2) : False := by
  rcases Int.even_or_odd X with ⟨x, hx⟩ | ⟨x, hx⟩ <;>
    rcases Int.even_or_odd Y with ⟨y, hy⟩ | ⟨y, hy⟩ <;>
      rcases Int.even_or_odd Z with ⟨z, hz⟩ | ⟨z, hz⟩ <;>
        rcases Int.even_or_odd N with ⟨n, hn⟩ | ⟨n, hn⟩
  all_goals
    subst X; subst Y; subst Z; subst N
    ring_nf at hA hB
    first
    | omega
    | have h2Y : (2 : ℤ) ∣ y + y := ⟨y, by ring⟩
      have h2N : (2 : ℤ) ∣ n + n := ⟨n, by ring⟩
      have h2gcd : (2 : ℤ) ∣ (Int.gcd (y + y) (n + n) : ℤ) :=
        Int.dvd_coe_gcd h2Y h2N
      rw [hcopYN] at h2gcd
      norm_num at h2gcd

private lemma n12_case_313_false
    (X Y N : ℤ) (hcopYN : Int.gcd Y N = 1)
    (h : 3 * X ^ 2 - Y ^ 2 = N ^ 2) : False := by
  rcases int_mod_three_cases Y with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩ <;>
    rcases int_mod_three_cases N with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  · have h3Y : (3 : ℤ) ∣ Y := ⟨y, hy⟩
    have h3N : (3 : ℤ) ∣ N := ⟨n, hn⟩
    have h3gcd : (3 : ℤ) ∣ (Int.gcd Y N : ℤ) := Int.dvd_coe_gcd h3Y h3N
    rw [hcopYN] at h3gcd
    norm_num at h3gcd
  all_goals
    rw [hy, hn] at h
    ring_nf at h
    omega

private lemma n12_case_m1m11_false
    (X Z N : ℤ) (hcopXN : Int.gcd X N = 1)
    (h : Z ^ 2 + X ^ 2 = 3 * N ^ 2) : False := by
  rcases int_mod_three_cases X with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩ <;>
    rcases int_mod_three_cases Z with ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ <;>
      rcases int_mod_three_cases N with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  · have h3X : (3 : ℤ) ∣ X := ⟨x, hx⟩
    have h3N : (3 : ℤ) ∣ N := ⟨n, hn⟩
    have h3gcd : (3 : ℤ) ∣ (Int.gcd X N : ℤ) := Int.dvd_coe_gcd h3X h3N
    rw [hcopXN] at h3gcd
    norm_num at h3gcd
  all_goals
    rw [hx, hz, hn] at h
    ring_nf at h
    omega

private lemma n12_case_m3m26_false
    (X Y N : ℤ) (hcopYN : Int.gcd Y N = 1)
    (h : -(3 * X ^ 2) + 2 * Y ^ 2 = N ^ 2) : False := by
  rcases int_mod_three_cases Y with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩ <;>
    rcases int_mod_three_cases N with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  · have h3Y : (3 : ℤ) ∣ Y := ⟨y, hy⟩
    have h3N : (3 : ℤ) ∣ N := ⟨n, hn⟩
    have h3gcd : (3 : ℤ) ∣ (Int.gcd Y N : ℤ) := Int.dvd_coe_gcd h3Y h3N
    rw [hcopYN] at h3gcd
    norm_num at h3gcd
  all_goals
    rw [hy, hn] at h
    ring_nf at h
    omega

private lemma n12_factor_coprime_N
    (A N k : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A + k * N ^ 2) N := by
  have h := hcop.add_mul_right_left (k * N)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h

private lemma n12_F1_coprime_N (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A - N ^ 2) N := by
  simpa [sub_eq_add_neg] using n12_factor_coprime_N A N (-1) hcop

private lemma n12_F2_coprime_N (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A - 2 * N ^ 2) N := by
  simpa [sub_eq_add_neg, mul_assoc] using n12_factor_coprime_N A N (-2) hcop

private lemma n12_F3_coprime_N (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A + 2 * N ^ 2) N := by
  simpa [mul_assoc] using n12_factor_coprime_N A N 2 hcop

private lemma n12_F1_F2_coprime (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A - N ^ 2) (A - 2 * N ^ 2) := by
  have hF2N : IsCoprime (A - 2 * N ^ 2) N := n12_F2_coprime_N A N hcop
  have hF2N2 : IsCoprime (N ^ 2) (A - 2 * N ^ 2) := hF2N.symm.pow_left
  have h := hF2N2.add_mul_right_left 1
  have hrewrite : N ^ 2 + 1 * (A - 2 * N ^ 2) = A - N ^ 2 := by ring
  rwa [hrewrite] at h

private lemma n12_gcd_F1_F3_dvd_three
    (A N : ℤ) (hcop : IsCoprime A N) :
    (Int.gcd (A - N ^ 2) (A + 2 * N ^ 2) : ℤ) ∣ (3 : ℤ) := by
  let g : ℤ := Int.gcd (A - N ^ 2) (A + 2 * N ^ 2)
  have hgF1 : g ∣ A - N ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_left _ _
  have hgF3 : g ∣ A + 2 * N ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_right _ _
  have hg3N2 : g ∣ 3 * N ^ 2 := by
    have hsub : g ∣ (A + 2 * N ^ 2) - (A - N ^ 2) := dvd_sub hgF3 hgF1
    convert hsub using 1
    ring
  have hF1N : IsCoprime (A - N ^ 2) N := n12_F1_coprime_N A N hcop
  have hgN : IsCoprime g N := by
    rcases hF1N with ⟨r, s, hrs⟩
    rcases hgF1 with ⟨t, ht⟩
    refine ⟨r * t, s, ?_⟩
    rw [ht] at hrs
    nlinarith
  have hgN2 : IsCoprime g (N ^ 2) := hgN.pow_right
  exact hgN2.dvd_of_dvd_mul_right hg3N2

private lemma n12_gcd_F2_F3_dvd_four
    (A N : ℤ) (hcop : IsCoprime A N) :
    (Int.gcd (A - 2 * N ^ 2) (A + 2 * N ^ 2) : ℤ) ∣ (4 : ℤ) := by
  let g : ℤ := Int.gcd (A - 2 * N ^ 2) (A + 2 * N ^ 2)
  have hgF2 : g ∣ A - 2 * N ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_left _ _
  have hgF3 : g ∣ A + 2 * N ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_right _ _
  have hg4N2 : g ∣ 4 * N ^ 2 := by
    have hsub : g ∣ (A + 2 * N ^ 2) - (A - 2 * N ^ 2) := dvd_sub hgF3 hgF2
    convert hsub using 1
    ring
  have hF2N : IsCoprime (A - 2 * N ^ 2) N := n12_F2_coprime_N A N hcop
  have hgN : IsCoprime g N := by
    rcases hF2N with ⟨r, s, hrs⟩
    rcases hgF2 with ⟨t, ht⟩
    refine ⟨r * t, s, ?_⟩
    rw [ht] at hrs
    nlinarith
  have hgN2 : IsCoprime g (N ^ 2) := hgN.pow_right
  exact hgN2.dvd_of_dvd_mul_right hg4N2

private lemma three_pos_pairwise_square
    (U V W C : ℤ)
    (hUpos : 0 < U) (hVpos : 0 < V) (hWpos : 0 < W)
    (hUV : IsCoprime U V) (hUW : IsCoprime U W) (hVW : IsCoprime V W)
    (hprod : C ^ 2 = U * V * W) :
    ∃ X Y Z : ℤ, U = X ^ 2 ∧ V = Y ^ 2 ∧ W = Z ^ 2 := by
  have hU_VW : IsCoprime U (V * W) := hUV.mul_right hUW
  have hfactU : U * (V * W) = C ^ 2 := by nlinarith
  obtain ⟨X, hX | hX⟩ := Int.sq_of_isCoprime hU_VW hfactU
  · have hfactVW : (V * W) * U = C ^ 2 := by nlinarith
    obtain ⟨T, hT | hT⟩ := Int.sq_of_isCoprime hU_VW.symm hfactVW
    · obtain ⟨Y, hY | hY⟩ := Int.sq_of_isCoprime hVW hT
      · have hfactW : W * V = T ^ 2 := by nlinarith
        obtain ⟨Z, hZ | hZ⟩ := Int.sq_of_isCoprime hVW.symm hfactW
        · exact ⟨X, Y, Z, hX, hY, hZ⟩
        · nlinarith [sq_nonneg Z]
      · nlinarith [sq_nonneg Y]
    · nlinarith [sq_nonneg T, mul_pos hVpos hWpos]
  · nlinarith [sq_nonneg X]

private lemma n12_gcd_pos_of_left_ne_zero (a b : ℤ) (ha : a ≠ 0) :
    0 < (Int.gcd a b : ℤ) := by
  have hg : Int.gcd a b ≠ 0 := by
    intro hg0
    have hd : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
    rw [hg0] at hd
    exact ha (by simpa using hd)
  exact_mod_cast Nat.pos_of_ne_zero hg

private lemma n12_gcd_dvd_three_cases (a b : ℤ) (ha : a ≠ 0)
    (h : (Int.gcd a b : ℤ) ∣ (3 : ℤ)) :
    Int.gcd a b = 1 ∨ Int.gcd a b = 3 := by
  let g : ℕ := Int.gcd a b
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using n12_gcd_pos_of_left_ne_zero a b ha
  rcases h with ⟨k, hk⟩
  have hk' : (g : ℤ) * k = 3 := by simpa [g, mul_comm] using hk.symm
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 3 := by nlinarith
  interval_cases k
  · right
    omega
  · omega
  · left
    omega

private lemma n12_gcd_dvd_four_cases (a b : ℤ) (ha : a ≠ 0)
    (h : (Int.gcd a b : ℤ) ∣ (4 : ℤ)) :
    Int.gcd a b = 1 ∨ Int.gcd a b = 2 ∨ Int.gcd a b = 4 := by
  let g : ℕ := Int.gcd a b
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using n12_gcd_pos_of_left_ne_zero a b ha
  rcases h with ⟨k, hk⟩
  have hk' : (g : ℤ) * k = 4 := by simpa [g, mul_comm] using hk.symm
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 4 := by nlinarith
  interval_cases k
  · right
    right
    omega
  · right
    left
    omega
  · omega
  · left
    omega

private lemma n12_coprime_stripped_of_gcd_eq
    (d : ℕ) (hdpos : 0 < d)
    {U W F G : ℤ} (hU : U ≠ 0)
    (hF : F = (d : ℤ) * U) (hG : G = (d : ℤ) * W)
    (hgcd : Int.gcd F G = d) :
    IsCoprime U W := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  let g : ℕ := Int.gcd U W
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using n12_gcd_pos_of_left_ne_zero U W hU
  have hdgF : (d : ℤ) * (g : ℤ) ∣ F := by
    rw [hF]
    exact mul_dvd_mul_left (d : ℤ) (by dsimp [g]; exact Int.gcd_dvd_left U W)
  have hdgG : (d : ℤ) * (g : ℤ) ∣ G := by
    rw [hG]
    exact mul_dvd_mul_left (d : ℤ) (by dsimp [g]; exact Int.gcd_dvd_right U W)
  have hdggcd : (d : ℤ) * (g : ℤ) ∣ (Int.gcd F G : ℤ) :=
    Int.dvd_coe_gcd hdgF hdgG
  rw [hgcd] at hdggcd
  rcases hdggcd with ⟨k, hk⟩
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
  have hcancel : (g : ℤ) * k = 1 := by
    apply mul_left_cancel₀ hdne
    calc
      (d : ℤ) * ((g : ℤ) * k) = ((d : ℤ) * (g : ℤ)) * k := by ring
      _ = (d : ℤ) := hk.symm
      _ = (d : ℤ) * 1 := by ring
  have hg_dvd_one : (g : ℤ) ∣ (1 : ℤ) := ⟨k, hcancel.symm⟩
  have hg_nat_dvd_one : g ∣ 1 := by exact_mod_cast hg_dvd_one
  have hg_one : g = 1 := Nat.dvd_one.mp hg_nat_dvd_one
  simpa [g] using hg_one

private lemma n12_three_square_from_factors_pos
    (U V W F1 F2 F3 C : ℤ) (d13 d23 : ℕ)
    (hd13pos : 0 < d13) (hd23pos : 0 < d23)
    (hUpos : 0 < U) (hVpos : 0 < V) (hWpos : 0 < W)
    (hF1 : F1 = (d13 : ℤ) * U)
    (hF2 : F2 = (d23 : ℤ) * V)
    (hF3 : F3 = (d13 : ℤ) * (d23 : ℤ) * W)
    (h12 : IsCoprime F1 F2)
    (hg13 : Int.gcd F1 F3 = d13)
    (hg23 : Int.gcd F2 F3 = d23)
    (hprod : C ^ 2 = F1 * F2 * F3) :
    ∃ X Y Z : ℤ, U = X ^ 2 ∧ V = Y ^ 2 ∧ W = Z ^ 2 := by
  have hUdvdF1 : U ∣ F1 := by
    rw [hF1]
    exact dvd_mul_left U (d13 : ℤ)
  have hVdvdF2 : V ∣ F2 := by
    rw [hF2]
    exact dvd_mul_left V (d23 : ℤ)
  have hUV : IsCoprime U V :=
    (h12.of_isCoprime_of_dvd_left hUdvdF1).of_isCoprime_of_dvd_right hVdvdF2
  have hF3_d13 : F3 = (d13 : ℤ) * ((d23 : ℤ) * W) := by
    rw [hF3]
    ring
  have hU_d23W : IsCoprime U ((d23 : ℤ) * W) :=
    n12_coprime_stripped_of_gcd_eq d13 hd13pos (ne_of_gt hUpos) hF1 hF3_d13 hg13
  have hUW : IsCoprime U W := hU_d23W.of_mul_right_right
  have hF3_d23 : F3 = (d23 : ℤ) * ((d13 : ℤ) * W) := by
    rw [hF3]
    ring
  have hV_d13W : IsCoprime V ((d13 : ℤ) * W) :=
    n12_coprime_stripped_of_gcd_eq d23 hd23pos (ne_of_gt hVpos) hF2 hF3_d23 hg23
  have hVW : IsCoprime V W := hV_d13W.of_mul_right_right
  let D : ℤ := (d13 : ℤ) * (d23 : ℤ)
  have hnorm : C ^ 2 = D ^ 2 * (U * V * W) := by
    rw [hprod, hF1, hF2, hF3]
    dsimp [D]
    ring
  have hDsq_dvd : D ^ 2 ∣ C ^ 2 := by
    rw [hnorm]
    exact dvd_mul_right (D ^ 2) (U * V * W)
  have hD_dvd_C : D ∣ C :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hDsq_dvd
  rcases hD_dvd_C with ⟨C0, hC⟩
  have hDne : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero
      (by exact_mod_cast ne_of_gt hd13pos)
      (by exact_mod_cast ne_of_gt hd23pos)
  have hDsqne : D ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  rw [hC] at hnorm
  have hC0 : C0 ^ 2 = U * V * W := by
    have hcancel : D ^ 2 * C0 ^ 2 = D ^ 2 * (U * V * W) := by
      calc
        D ^ 2 * C0 ^ 2 = (D * C0) ^ 2 := by ring
        _ = D ^ 2 * (U * V * W) := hnorm
    exact mul_left_cancel₀ hDsqne hcancel
  exact three_pos_pairwise_square U V W C0 hUpos hVpos hWpos hUV hUW hVW hC0

private lemma n12_three_square_from_factors_neg
    (U V W F1 F2 F3 C : ℤ) (d13 d23 : ℕ)
    (hd13pos : 0 < d13) (hd23pos : 0 < d23)
    (hUpos : 0 < U) (hVpos : 0 < V) (hWpos : 0 < W)
    (hF1 : F1 = -((d13 : ℤ) * U))
    (hF2 : F2 = -((d23 : ℤ) * V))
    (hF3 : F3 = (d13 : ℤ) * (d23 : ℤ) * W)
    (h12 : IsCoprime F1 F2)
    (hg13 : Int.gcd F1 F3 = d13)
    (hg23 : Int.gcd F2 F3 = d23)
    (hprod : C ^ 2 = F1 * F2 * F3) :
    ∃ X Y Z : ℤ, U = X ^ 2 ∧ V = Y ^ 2 ∧ W = Z ^ 2 := by
  have hUdvdF1 : U ∣ F1 := by
    rw [hF1]
    exact ⟨-(d13 : ℤ), by ring⟩
  have hVdvdF2 : V ∣ F2 := by
    rw [hF2]
    exact ⟨-(d23 : ℤ), by ring⟩
  have hUV : IsCoprime U V :=
    (h12.of_isCoprime_of_dvd_left hUdvdF1).of_isCoprime_of_dvd_right hVdvdF2
  have hF1_d13 : F1 = (d13 : ℤ) * (-U) := by
    rw [hF1]
    ring
  have hF3_d13 : F3 = (d13 : ℤ) * ((d23 : ℤ) * W) := by
    rw [hF3]
    ring
  have hnegU_d23W : IsCoprime (-U) ((d23 : ℤ) * W) :=
    n12_coprime_stripped_of_gcd_eq d13 hd13pos
      (neg_ne_zero.mpr (ne_of_gt hUpos)) hF1_d13 hF3_d13 hg13
  have hU_d23W : IsCoprime U ((d23 : ℤ) * W) :=
    (IsCoprime.neg_left_iff U ((d23 : ℤ) * W)).mp hnegU_d23W
  have hUW : IsCoprime U W := hU_d23W.of_mul_right_right
  have hF2_d23 : F2 = (d23 : ℤ) * (-V) := by
    rw [hF2]
    ring
  have hF3_d23 : F3 = (d23 : ℤ) * ((d13 : ℤ) * W) := by
    rw [hF3]
    ring
  have hnegV_d13W : IsCoprime (-V) ((d13 : ℤ) * W) :=
    n12_coprime_stripped_of_gcd_eq d23 hd23pos
      (neg_ne_zero.mpr (ne_of_gt hVpos)) hF2_d23 hF3_d23 hg23
  have hV_d13W : IsCoprime V ((d13 : ℤ) * W) :=
    (IsCoprime.neg_left_iff V ((d13 : ℤ) * W)).mp hnegV_d13W
  have hVW : IsCoprime V W := hV_d13W.of_mul_right_right
  let D : ℤ := (d13 : ℤ) * (d23 : ℤ)
  have hnorm : C ^ 2 = D ^ 2 * (U * V * W) := by
    rw [hprod, hF1, hF2, hF3]
    dsimp [D]
    ring
  have hDsq_dvd : D ^ 2 ∣ C ^ 2 := by
    rw [hnorm]
    exact dvd_mul_right (D ^ 2) (U * V * W)
  have hD_dvd_C : D ∣ C :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hDsq_dvd
  rcases hD_dvd_C with ⟨C0, hC⟩
  have hDne : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero
      (by exact_mod_cast ne_of_gt hd13pos)
      (by exact_mod_cast ne_of_gt hd23pos)
  have hDsqne : D ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  rw [hC] at hnorm
  have hC0 : C0 ^ 2 = U * V * W := by
    have hcancel : D ^ 2 * C0 ^ 2 = D ^ 2 * (U * V * W) := by
      calc
        D ^ 2 * C0 ^ 2 = (D * C0) ^ 2 := by ring
        _ = D ^ 2 * (U * V * W) := hnorm
    exact mul_left_cancel₀ hDsqne hcancel
  exact three_pos_pairwise_square U V W C0 hUpos hVpos hWpos hUV hUW hVW hC0

private lemma n12_pos_squareclass_from_gcd
    (F1 F2 F3 C : ℤ) (d13 d23 : ℕ)
    (hd13pos : 0 < d13) (hd23pos : 0 < d23)
    (hcopd : IsCoprime (d13 : ℤ) (d23 : ℤ))
    (hF1pos : 0 < F1) (hF2pos : 0 < F2) (hF3pos : 0 < F3)
    (h12 : IsCoprime F1 F2)
    (hg13 : Int.gcd F1 F3 = d13)
    (hg23 : Int.gcd F2 F3 = d23)
    (hprod : C ^ 2 = F1 * F2 * F3) :
    ∃ X Y Z : ℤ,
      F1 = (d13 : ℤ) * X ^ 2 ∧
      F2 = (d23 : ℤ) * Y ^ 2 ∧
      F3 = (d13 : ℤ) * (d23 : ℤ) * Z ^ 2 := by
  have hd13F1 : (d13 : ℤ) ∣ F1 := by
    have hd := Int.gcd_dvd_left F1 F3
    rw [hg13] at hd
    simpa using hd
  have hd23F2 : (d23 : ℤ) ∣ F2 := by
    have hd := Int.gcd_dvd_left F2 F3
    rw [hg23] at hd
    simpa using hd
  have hd13F3 : (d13 : ℤ) ∣ F3 := by
    have hd := Int.gcd_dvd_right F1 F3
    rw [hg13] at hd
    simpa using hd
  have hd23F3 : (d23 : ℤ) ∣ F3 := by
    have hd := Int.gcd_dvd_right F2 F3
    rw [hg23] at hd
    simpa using hd
  rcases hd13F1 with ⟨U, hF1U⟩
  rcases hd23F2 with ⟨V, hF2V⟩
  have hDvdF3 : (d13 : ℤ) * (d23 : ℤ) ∣ F3 :=
    hcopd.mul_dvd hd13F3 hd23F3
  rcases hDvdF3 with ⟨W, hF3W⟩
  have hUpos : 0 < U := by
    have hd13posZ : 0 < (d13 : ℤ) := by exact_mod_cast hd13pos
    nlinarith
  have hVpos : 0 < V := by
    have hd23posZ : 0 < (d23 : ℤ) := by exact_mod_cast hd23pos
    nlinarith
  have hWpos : 0 < W := by
    have hd13posZ : 0 < (d13 : ℤ) := by exact_mod_cast hd13pos
    have hd23posZ : 0 < (d23 : ℤ) := by exact_mod_cast hd23pos
    have hDpos : 0 < (d13 : ℤ) * (d23 : ℤ) := mul_pos hd13posZ hd23posZ
    nlinarith
  have hF3W' : F3 = (d13 : ℤ) * (d23 : ℤ) * W := by
    simpa [mul_assoc] using hF3W
  obtain ⟨X, Y, Z, hX, hY, hZ⟩ :=
    n12_three_square_from_factors_pos U V W F1 F2 F3 C d13 d23
      hd13pos hd23pos hUpos hVpos hWpos hF1U hF2V hF3W' h12 hg13 hg23 hprod
  refine ⟨X, Y, Z, ?_, ?_, ?_⟩
  · rw [hF1U, hX]
  · rw [hF2V, hY]
  · rw [hF3W', hZ]

private lemma n12_neg_squareclass_from_gcd
    (F1 F2 F3 C : ℤ) (d13 d23 : ℕ)
    (hd13pos : 0 < d13) (hd23pos : 0 < d23)
    (hcopd : IsCoprime (d13 : ℤ) (d23 : ℤ))
    (hF1neg : F1 < 0) (hF2neg : F2 < 0) (hF3pos : 0 < F3)
    (h12 : IsCoprime F1 F2)
    (hg13 : Int.gcd F1 F3 = d13)
    (hg23 : Int.gcd F2 F3 = d23)
    (hprod : C ^ 2 = F1 * F2 * F3) :
    ∃ X Y Z : ℤ,
      F1 = -((d13 : ℤ) * X ^ 2) ∧
      F2 = -((d23 : ℤ) * Y ^ 2) ∧
      F3 = (d13 : ℤ) * (d23 : ℤ) * Z ^ 2 := by
  have hd13F1 : (d13 : ℤ) ∣ F1 := by
    have hd := Int.gcd_dvd_left F1 F3
    rw [hg13] at hd
    simpa using hd
  have hd23F2 : (d23 : ℤ) ∣ F2 := by
    have hd := Int.gcd_dvd_left F2 F3
    rw [hg23] at hd
    simpa using hd
  have hd13F3 : (d13 : ℤ) ∣ F3 := by
    have hd := Int.gcd_dvd_right F1 F3
    rw [hg13] at hd
    simpa using hd
  have hd23F3 : (d23 : ℤ) ∣ F3 := by
    have hd := Int.gcd_dvd_right F2 F3
    rw [hg23] at hd
    simpa using hd
  have hd13negF1 : (d13 : ℤ) ∣ -F1 := dvd_neg.mpr hd13F1
  have hd23negF2 : (d23 : ℤ) ∣ -F2 := dvd_neg.mpr hd23F2
  rcases hd13negF1 with ⟨U, hnegF1U⟩
  rcases hd23negF2 with ⟨V, hnegF2V⟩
  have hDvdF3 : (d13 : ℤ) * (d23 : ℤ) ∣ F3 :=
    hcopd.mul_dvd hd13F3 hd23F3
  rcases hDvdF3 with ⟨W, hF3W⟩
  have hF1U : F1 = -((d13 : ℤ) * U) := by
    rw [← hnegF1U]
    ring
  have hF2V : F2 = -((d23 : ℤ) * V) := by
    rw [← hnegF2V]
    ring
  have hUpos : 0 < U := by
    have hd13posZ : 0 < (d13 : ℤ) := by exact_mod_cast hd13pos
    nlinarith
  have hVpos : 0 < V := by
    have hd23posZ : 0 < (d23 : ℤ) := by exact_mod_cast hd23pos
    nlinarith
  have hWpos : 0 < W := by
    have hd13posZ : 0 < (d13 : ℤ) := by exact_mod_cast hd13pos
    have hd23posZ : 0 < (d23 : ℤ) := by exact_mod_cast hd23pos
    have hDpos : 0 < (d13 : ℤ) * (d23 : ℤ) := mul_pos hd13posZ hd23posZ
    nlinarith
  have hF3W' : F3 = (d13 : ℤ) * (d23 : ℤ) * W := by
    simpa [mul_assoc] using hF3W
  obtain ⟨X, Y, Z, hX, hY, hZ⟩ :=
    n12_three_square_from_factors_neg U V W F1 F2 F3 C d13 d23
      hd13pos hd23pos hUpos hVpos hWpos hF1U hF2V hF3W' h12 hg13 hg23 hprod
  refine ⟨X, Y, Z, ?_, ?_, ?_⟩
  · rw [hF1U, hX]
  · rw [hF2V, hY]
  · rw [hF3W', hZ]

private lemma n12_u_eq_int
    (u : ℚ) {A N c : ℤ} (hN : N ≠ 0)
    (hu : u = (A : ℚ) / ((N ^ 2 : ℤ) : ℚ))
    (hA : A = c * N ^ 2) :
    u = (c : ℚ) := by
  rw [hu, hA]
  have hNsq : ((N ^ 2 : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 hN)
  field_simp [hNsq]
  push_cast
  ring

end ObstructionN12

open ObstructionN12

theorem obstruction_N12 (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4 := by
  rcases n12_clear_denominators u w h with ⟨A, N, C, hNpos, hAN, hu, hprod0⟩
  have hNne : N ≠ 0 := ne_of_gt hNpos
  let F1 : ℤ := A - N ^ 2
  let F2 : ℤ := A - 2 * N ^ 2
  let F3 : ℤ := A + 2 * N ^ 2
  have hprod : C ^ 2 = F1 * F2 * F3 := by
    simpa [F1, F2, F3] using hprod0
  have finishA :
      A = -2 * N ^ 2 ∨ A = 0 ∨ A = N ^ 2 ∨ A = 2 * N ^ 2 ∨ A = 4 * N ^ 2 →
        u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4 := by
    intro hAvals
    rcases hAvals with hA | hA | hA | hA | hA
    · left
      exact by
        have hu' := n12_u_eq_int u hNne hu (c := -2) (by simpa using hA)
        simpa using hu'
    · right
      left
      have hAc : A = (0 : ℤ) * N ^ 2 := by
        rw [hA]
        ring
      have hu' := n12_u_eq_int u hNne hu (c := 0) hAc
      simpa using hu'
    · right
      right
      left
      have hAc : A = (1 : ℤ) * N ^ 2 := by
        rw [hA]
        ring
      have hu' := n12_u_eq_int u hNne hu (c := 1) hAc
      simpa using hu'
    · right
      right
      right
      left
      have hu' := n12_u_eq_int u hNne hu (c := 2) (by simpa using hA)
      simpa using hu'
    · right
      right
      right
      right
      have hu' := n12_u_eq_int u hNne hu (c := 4) (by simpa using hA)
      simpa using hu'
  by_cases hF1zero : F1 = 0
  · apply finishA
    right
    right
    left
    dsimp [F1] at hF1zero
    nlinarith
  by_cases hF2zero : F2 = 0
  · apply finishA
    right
    right
    right
    left
    dsimp [F2] at hF2zero
    nlinarith
  by_cases hF3zero : F3 = 0
  · apply finishA
    left
    dsimp [F3] at hF3zero
    nlinarith
  have hF1nz : F1 ≠ 0 := hF1zero
  have hF2nz : F2 ≠ 0 := hF2zero
  have hF3nz : F3 ≠ 0 := hF3zero
  have hcopAN : IsCoprime A N := Int.isCoprime_iff_gcd_eq_one.mpr hAN
  have h12 : IsCoprime F1 F2 := by
    simpa [F1, F2] using n12_F1_F2_coprime A N hcopAN
  have h13dvd : (Int.gcd F1 F3 : ℤ) ∣ (3 : ℤ) := by
    simpa [F1, F3] using n12_gcd_F1_F3_dvd_three A N hcopAN
  have h23dvd : (Int.gcd F2 F3 : ℤ) ∣ (4 : ℤ) := by
    simpa [F2, F3] using n12_gcd_F2_F3_dvd_four A N hcopAN
  have hF1N : IsCoprime F1 N := by
    simpa [F1] using n12_F1_coprime_N A N hcopAN
  have hF2N : IsCoprime F2 N := by
    simpa [F2] using n12_F2_coprime_N A N hcopAN
  have gcd_of_dvd {T F : ℤ} (hFN : IsCoprime F N) (hTF : T ∣ F) :
      Int.gcd T N = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (hFN.of_isCoprime_of_dvd_left hTF)
  have hN2pos : 0 < N ^ 2 := sq_pos_of_ne_zero hNne
  have hF2ltF1 : F2 < F1 := by
    dsimp [F1, F2]
    nlinarith
  have hF1ltF3 : F1 < F3 := by
    dsimp [F1, F3]
    nlinarith
  have hF2ltF3 : F2 < F3 := by
    dsimp [F2, F3]
    nlinarith
  have hprod_nonneg : 0 ≤ F1 * F2 * F3 := by
    rw [← hprod]
    exact sq_nonneg C
  have hsign :
      (0 < F1 ∧ 0 < F2 ∧ 0 < F3) ∨ (F1 < 0 ∧ F2 < 0 ∧ 0 < F3) := by
    by_cases hF2pos : 0 < F2
    · left
      constructor
      · nlinarith
      · constructor
        · exact hF2pos
        · nlinarith
    · have hF2neg : F2 < 0 := lt_of_le_of_ne (not_lt.mp hF2pos) hF2nz
      by_cases hF1pos : 0 < F1
      · have hF3pos : 0 < F3 := by nlinarith
        have hp13 : 0 < F1 * F3 := mul_pos hF1pos hF3pos
        have hnegprod : F1 * F2 * F3 < 0 := by
          nlinarith [mul_neg_of_pos_of_neg hp13 hF2neg]
        nlinarith
      · have hF1neg : F1 < 0 := lt_of_le_of_ne (not_lt.mp hF1pos) hF1nz
        by_cases hF3pos : 0 < F3
        · right
          exact ⟨hF1neg, hF2neg, hF3pos⟩
        · have hF3neg : F3 < 0 := lt_of_le_of_ne (not_lt.mp hF3pos) hF3nz
          have hp12 : 0 < F1 * F2 := mul_pos_of_neg_of_neg hF1neg hF2neg
          have hnegprod : F1 * F2 * F3 < 0 := by
            nlinarith [mul_neg_of_pos_of_neg hp12 hF3neg]
          nlinarith
  have h13cases := n12_gcd_dvd_three_cases F1 F3 hF1nz h13dvd
  have h23cases := n12_gcd_dvd_four_cases F2 F3 hF2nz h23dvd
  rcases hsign with ⟨hF1pos, hF2pos, hF3pos⟩ | ⟨hF1neg, hF2neg, hF3pos⟩
  · rcases h13cases with hg13 | hg13
    · rcases h23cases with hg23 | hg23 | hg23
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n12_pos_squareclass_from_gcd F1 F2 F3 C 1 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        have hc1 : A - N ^ 2 = X ^ 2 := by simpa [F1] using h1
        have hc2 : A - 2 * N ^ 2 = Y ^ 2 := by simpa [F2] using h2
        have hc3 : A + 2 * N ^ 2 = Z ^ 2 := by simpa [F3] using h3
        apply finishA
        right; right; right; left
        exact n12_case_111 A N X Y Z hNne hc1 hc2 hc3
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n12_pos_squareclass_from_gcd F1 F2 F3 C 1 2
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        exfalso
        have hYdvdF2 : Y ∣ F2 := by
          rw [h2]
          exact ⟨2 * Y, by ring⟩
        have hcopYN : Int.gcd Y N = 1 := gcd_of_dvd hF2N hYdvdF2
        have hAeq : X ^ 2 - 2 * Y ^ 2 = N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        have hBeq : 2 * Z ^ 2 - X ^ 2 = 3 * N ^ 2 := by
          dsimp [F1, F3] at h1 h3
          nlinarith
        exact n12_case_122_false X Y Z N hcopYN hAeq hBeq
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n12_pos_squareclass_from_gcd F1 F2 F3 C 1 4
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        have hc1 : A - N ^ 2 = X ^ 2 := by simpa [F1] using h1
        have hc2 : A - 2 * N ^ 2 = (2 * Y) ^ 2 := by
          dsimp [F2] at h2
          rw [h2]
          ring
        have hc3 : A + 2 * N ^ 2 = (2 * Z) ^ 2 := by
          dsimp [F3] at h3
          rw [h3]
          ring
        apply finishA
        right; right; right; left
        exact n12_case_111 A N X (2 * Y) (2 * Z) hNne hc1 hc2 hc3
    · rcases h23cases with hg23 | hg23 | hg23
      · obtain ⟨X, Y, Z, h1, h2, _h3⟩ :=
          n12_pos_squareclass_from_gcd F1 F2 F3 C 3 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        exfalso
        have hYdvdF2 : Y ∣ F2 := by
          rw [h2]
          exact ⟨Y, by ring⟩
        have hcopYN : Int.gcd Y N = 1 := gcd_of_dvd hF2N hYdvdF2
        have heq : 3 * X ^ 2 - Y ^ 2 = N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        exact n12_case_313_false X Y N hcopYN heq
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n12_pos_squareclass_from_gcd F1 F2 F3 C 3 2
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        have hc1 : A - N ^ 2 = 3 * X ^ 2 := by simpa [F1] using h1
        have hc2 : A - 2 * N ^ 2 = 2 * Y ^ 2 := by simpa [F2] using h2
        have hc3 : A + 2 * N ^ 2 = 6 * Z ^ 2 := by
          dsimp [F3] at h3
          rw [h3]
        apply finishA
        right; right; right; right
        exact n12_case_326 A N X Y Z hc1 hc2 hc3
      · obtain ⟨X, Y, Z, h1, h2, _h3⟩ :=
          n12_pos_squareclass_from_gcd F1 F2 F3 C 3 4
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        exfalso
        have h2YdvdF2 : (2 * Y) ∣ F2 := by
          rw [h2]
          exact ⟨2 * Y, by ring⟩
        have hcopYN : Int.gcd (2 * Y) N = 1 := gcd_of_dvd hF2N h2YdvdF2
        have heq : 3 * X ^ 2 - (2 * Y) ^ 2 = N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        exact n12_case_313_false X (2 * Y) N hcopYN heq
  · rcases h13cases with hg13 | hg13
    · rcases h23cases with hg23 | hg23 | hg23
      · obtain ⟨X, _Y, Z, h1, _h2, h3⟩ :=
          n12_neg_squareclass_from_gcd F1 F2 F3 C 1 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        exfalso
        have hXdvdF1 : X ∣ F1 := by
          rw [h1]
          exact ⟨-X, by ring⟩
        have hcopXN : Int.gcd X N = 1 := gcd_of_dvd hF1N hXdvdF1
        have heq : Z ^ 2 + X ^ 2 = 3 * N ^ 2 := by
          dsimp [F1, F3] at h1 h3
          nlinarith
        exact n12_case_m1m11_false X Z N hcopXN heq
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n12_neg_squareclass_from_gcd F1 F2 F3 C 1 2
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        have hc1 : A - N ^ 2 = -(X ^ 2) := by
          dsimp [F1] at h1
          simpa using h1
        have hc2 : A - 2 * N ^ 2 = -(2 * Y ^ 2) := by
          simpa [F2] using h2
        have hc3 : A + 2 * N ^ 2 = 2 * Z ^ 2 := by
          simpa [F3] using h3
        apply finishA
        right; left
        exact n12_case_m1m22 A N X Y Z hc1 hc2 hc3
      · obtain ⟨X, _Y, Z, h1, _h2, h3⟩ :=
          n12_neg_squareclass_from_gcd F1 F2 F3 C 1 4
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        exfalso
        have hXdvdF1 : X ∣ F1 := by
          rw [h1]
          exact ⟨-X, by ring⟩
        have hcopXN : Int.gcd X N = 1 := gcd_of_dvd hF1N hXdvdF1
        have heq : (2 * Z) ^ 2 + X ^ 2 = 3 * N ^ 2 := by
          dsimp [F1, F3] at h1 h3
          nlinarith
        exact n12_case_m1m11_false X (2 * Z) N hcopXN heq
    · rcases h23cases with hg23 | hg23 | hg23
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n12_neg_squareclass_from_gcd F1 F2 F3 C 3 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        have hc1 : A - N ^ 2 = -(3 * X ^ 2) := by
          simpa [F1] using h1
        have hc2 : A - 2 * N ^ 2 = -(Y ^ 2) := by
          dsimp [F2] at h2
          simpa using h2
        have hc3 : A + 2 * N ^ 2 = 3 * Z ^ 2 := by
          dsimp [F3] at h3
          rw [h3]
        rcases n12_case_m3m13 A N X Y Z hc1 hc2 hc3 with hA | hA
        · apply finishA
          right; right; left
          exact hA
        · apply finishA
          left
          exact hA
      · obtain ⟨X, Y, _Z, h1, h2, _h3⟩ :=
          n12_neg_squareclass_from_gcd F1 F2 F3 C 3 2
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        exfalso
        have hYdvdF2 : Y ∣ F2 := by
          rw [h2]
          exact ⟨-(2 * Y), by ring⟩
        have hcopYN : Int.gcd Y N = 1 := gcd_of_dvd hF2N hYdvdF2
        have heq : -(3 * X ^ 2) + 2 * Y ^ 2 = N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        exact n12_case_m3m26_false X Y N hcopYN heq
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n12_neg_squareclass_from_gcd F1 F2 F3 C 3 4
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        have hc1 : A - N ^ 2 = -(3 * X ^ 2) := by
          simpa [F1] using h1
        have hc2 : A - 2 * N ^ 2 = -((2 * Y) ^ 2) := by
          dsimp [F2] at h2
          rw [h2]
          ring
        have hc3 : A + 2 * N ^ 2 = 3 * (2 * Z) ^ 2 := by
          dsimp [F3] at h3
          rw [h3]
          ring
        rcases n12_case_m3m13 A N X (2 * Y) (2 * Z) hc1 hc2 hc3 with hA | hA
        · apply finishA
          right; right; left
          exact hA
        · apply finishA
          left
          exact hA
