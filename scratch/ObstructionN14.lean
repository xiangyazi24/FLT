import scratch.SquareStep014
import scratch.FourSquaresAP

set_option maxHeartbeats 2000000

namespace ObstructionN14

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

private lemma n14_factor_coprime_den
    (p q : ℤ) (hpq : Nat.Coprime p.natAbs q.natAbs) :
    Nat.Coprime
      ((p * (p + 2 * q) * (p - q)).natAbs)
      q.natAbs := by
  have hpqI : IsCoprime p q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact int_gcd_eq_one_of_nat_coprime hpq
  have h1 : IsCoprime p q := hpqI
  have h2 : IsCoprime (p + 2 * q) q := by
    have h := hpqI.add_mul_right_left 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h3 : IsCoprime (p - q) q := by
    have h := hpqI.add_mul_right_left (-1)
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h
  have hprod : IsCoprime (p * (p + 2 * q) * (p - q)) q :=
    (h1.mul_left h2).mul_left h3
  rw [Int.isCoprime_iff_gcd_eq_one] at hprod
  exact nat_coprime_of_int_gcd_eq_one hprod

private lemma rat_n14_rhs_num_den (u : ℚ) :
    let p : ℤ := u.num
    let q : ℤ := u.den
    let M : ℤ := p * (p + 2 * q) * (p - q)
    (u ^ 3 + u ^ 2 - 2 * u).num = M ∧
      (u ^ 3 + u ^ 2 - 2 * u).den = u.den ^ 3 := by
  classical
  let p : ℤ := u.num
  let qN : ℕ := u.den
  let q : ℤ := qN
  let M : ℤ := p * (p + 2 * q) * (p - q)
  have hqposN : 0 < qN := u.pos
  have hqpos : 0 < q := by
    dsimp [q]
    exact Int.natCast_pos.mpr hqposN
  have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hu : u = (p : ℚ) / (q : ℚ) := by
    dsimp [p, q, qN]
    exact (Rat.num_div_den u).symm
  have hrhs :
      u ^ 3 + u ^ 2 - 2 * u =
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
    exact n14_factor_coprime_den p q hpq
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

private theorem n14_clear_denominators (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - 2 * u) :
    ∃ A N C : ℤ, 0 < N ∧ Int.gcd A N = 1 ∧
      u = (A : ℚ) / ((N ^ 2 : ℤ) : ℚ) ∧
      C ^ 2 = A * (A + 2 * N ^ 2) * (A - N ^ 2) := by
  classical
  let A : ℤ := u.num
  let qN : ℕ := u.den
  let q : ℤ := qN
  let M : ℤ := A * (A + 2 * q) * (A - q)
  have hnumden := rat_n14_rhs_num_den u
  have hnumR : (u ^ 3 + u ^ 2 - 2 * u).num = M := by
    simpa [A, q, qN, M] using hnumden.1
  have hdenR : (u ^ 3 + u ^ 2 - 2 * u).den = qN ^ 3 := by
    simpa [A, q, qN, M] using hnumden.2
  have hsR : IsSquare (u ^ 3 + u ^ 2 - 2 * u) :=
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

private lemma n14_case_111
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

private lemma n14_case_326
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

private lemma n14_case_m1m22
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

private lemma n14_case_m3m13
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

private lemma n14_case_122_false
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

private lemma n14_case_313_false
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

private lemma n14_case_m1m11_false
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

private lemma n14_case_m3m26_false
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

private lemma core013_gcd_LR_dvd_three
    (β γ : ℤ) (hcop : IsCoprime β γ) :
    (Int.gcd (γ ^ 2 - β ^ 2) (γ ^ 2 + 2 * β ^ 2) : ℤ) ∣ (3 : ℤ) := by
  let g : ℤ := Int.gcd (γ ^ 2 - β ^ 2) (γ ^ 2 + 2 * β ^ 2)
  have hgL : g ∣ γ ^ 2 - β ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_left _ _
  have hgR : g ∣ γ ^ 2 + 2 * β ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_right _ _
  have hg3β2 : g ∣ 3 * β ^ 2 := by
    have hsub : g ∣ (γ ^ 2 + 2 * β ^ 2) - (γ ^ 2 - β ^ 2) := dvd_sub hgR hgL
    convert hsub using 1
    ring
  have hLβ : IsCoprime (γ ^ 2 - β ^ 2) β := by
    have hγ2β : IsCoprime (γ ^ 2) β := hcop.symm.pow_left
    have h := hγ2β.add_mul_right_left (-β)
    simpa [sub_eq_add_neg, pow_two, mul_assoc, mul_comm, mul_left_comm] using h
  have hgβ : IsCoprime g β :=
    hLβ.of_isCoprime_of_dvd_left hgL
  have hgβ2 : IsCoprime g (β ^ 2) := hgβ.pow_right
  exact hgβ2.dvd_of_dvd_mul_right hg3β2

private lemma core013_eq_of_pos_dvd_dvd {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) (hba : b ∣ a) :
    a = b := by
  rcases hab with ⟨m, hm⟩
  rcases hba with ⟨n, hn⟩
  have hmpos : 0 < m := by
    by_contra hmle
    have hmnonpos : m ≤ 0 := le_of_not_gt hmle
    rw [hm] at hb
    nlinarith
  have hnpos : 0 < n := by
    by_contra hnle
    have hnnonpos : n ≤ 0 := le_of_not_gt hnle
    rw [hn] at ha
    nlinarith
  have hmn : m * n = 1 := by
    rw [hm] at hn
    have ha0 : a ≠ 0 := ne_of_gt ha
    nlinarith
  have hm1 : m = 1 := by nlinarith
  rw [hm, hm1]
  ring

private lemma core013_square_system_coprime
    (α δ L R : ℤ)
    (hαpos : 0 < α) (hδpos : 0 < δ)
    (hLpos : 0 < L) (hRpos : 0 < R)
    (hαδ : IsCoprime α δ) (hLR : IsCoprime L R)
    (h : α ^ 2 * L = δ ^ 2 * R) :
    L = δ ^ 2 ∧ R = α ^ 2 := by
  have hR_dvd_α2L : R ∣ α ^ 2 * L := by
    refine ⟨δ ^ 2, ?_⟩
    nlinarith
  have hR_dvd_α2 : R ∣ α ^ 2 :=
    hLR.symm.dvd_of_dvd_mul_right hR_dvd_α2L
  have hα2_dvd_δ2R : α ^ 2 ∣ δ ^ 2 * R := by
    refine ⟨L, ?_⟩
    nlinarith
  have hα2δ2 : IsCoprime (α ^ 2) (δ ^ 2) := by
    simpa using (hαδ.pow_left (m := 2)).pow_right (n := 2)
  have hα2_dvd_R : α ^ 2 ∣ R :=
    hα2δ2.dvd_of_dvd_mul_right (by simpa [mul_comm] using hα2_dvd_δ2R)
  have hα2pos : 0 < α ^ 2 := sq_pos_of_pos hαpos
  have hReq : R = α ^ 2 :=
    core013_eq_of_pos_dvd_dvd hRpos hα2pos hR_dvd_α2 hα2_dvd_R
  have hL_dvd_δ2 : L ∣ δ ^ 2 := by
    have hL_dvd_δ2R : L ∣ δ ^ 2 * R := by
      refine ⟨α ^ 2, ?_⟩
      nlinarith
    exact hLR.dvd_of_dvd_mul_right hL_dvd_δ2R
  have hδ2_dvd_α2L : δ ^ 2 ∣ α ^ 2 * L := by
    refine ⟨R, ?_⟩
    nlinarith
  have hδ2α2 : IsCoprime (δ ^ 2) (α ^ 2) := hα2δ2.symm
  have hδ2_dvd_L : δ ^ 2 ∣ L :=
    hδ2α2.dvd_of_dvd_mul_right (by simpa [mul_comm] using hδ2_dvd_α2L)
  have hδ2pos : 0 < δ ^ 2 := sq_pos_of_pos hδpos
  have hLeq : L = δ ^ 2 :=
    core013_eq_of_pos_dvd_dvd hLpos hδ2pos hL_dvd_δ2 hδ2_dvd_L
  exact ⟨hLeq, hReq⟩

private lemma core013_gcd_pos_of_left_ne_zero (a b : ℤ) (ha : a ≠ 0) :
    0 < (Int.gcd a b : ℤ) := by
  have hg : Int.gcd a b ≠ 0 := by
    intro hg0
    have hd : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
    rw [hg0] at hd
    exact ha (by simpa using hd)
  exact_mod_cast Nat.pos_of_ne_zero hg

private lemma core013_gcd_dvd_three_cases (a b : ℤ) (ha : a ≠ 0)
    (h : (Int.gcd a b : ℤ) ∣ (3 : ℤ)) :
    Int.gcd a b = 1 ∨ Int.gcd a b = 3 := by
  let g : ℕ := Int.gcd a b
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using core013_gcd_pos_of_left_ne_zero a b ha
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

private lemma core013_nat_matrix_factor
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

private lemma core013_half_factors_coprime
    (m n z R S : ℤ)
    (hRpos : 0 < R)
    (hmn : IsCoprime m n)
    (hXodd : Odd (m ^ 2 + n ^ 2))
    (hR : z + (m ^ 2 + n ^ 2) = 2 * R)
    (hS : z - (m ^ 2 + n ^ 2) = 2 * S)
    (hzX : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 + 2 * (2 * m * n) ^ 2) :
    IsCoprime R S := by
  let X : ℤ := m ^ 2 + n ^ 2
  let g : ℤ := Int.gcd R S
  have hgR : g ∣ R := by
    dsimp [g]
    exact Int.gcd_dvd_left _ _
  have hgS : g ∣ S := by
    dsimp [g]
    exact Int.gcd_dvd_right _ _
  have hsum : R + S = z := by
    nlinarith
  have hdiff : R - S = X := by
    dsimp [X] at *
    nlinarith
  have hgz : g ∣ z := by
    rw [← hsum]
    exact dvd_add hgR hgS
  have hgX : g ∣ X := by
    rw [← hdiff]
    exact dvd_sub hgR hgS
  have hgY : g ∣ 2 * (2 * m * n) ^ 2 := by
    have hgz2 : g ∣ z ^ 2 := dvd_pow hgz (by norm_num : (2 : ℕ) ≠ 0)
    have hgX2 : g ∣ X ^ 2 := dvd_pow hgX (by norm_num : (2 : ℕ) ≠ 0)
    have hsqdiff : g ∣ z ^ 2 - X ^ 2 := dvd_sub hgz2 hgX2
    convert hsqdiff using 1
    dsimp [X] at *
    nlinarith
  have hcopXmn : IsCoprime X (m * n) := by
    dsimp [X]
    exact Int.isCoprime_of_sq_sum' hmn
  have hcopX2 : IsCoprime X (2 : ℤ) := by
    dsimp [X]
    simpa [isCoprime_comm] using (show IsCoprime (2 : ℤ) (m ^ 2 + n ^ 2) from by
      simpa using hXodd)
  have hcopX2mn : IsCoprime X (2 * (m * n)) := by
    simpa [mul_assoc] using hcopX2.mul_right hcopXmn
  have hcopg2mn : IsCoprime g (2 * (m * n)) :=
    hcopX2mn.of_isCoprime_of_dvd_left hgX
  have hcopgY : IsCoprime g ((2 * (m * n)) ^ 2) := hcopg2mn.pow_right
  have hgY' : g ∣ 2 * ((2 * (m * n)) ^ 2) := by
    simpa [mul_assoc] using hgY
  have hg2 : g ∣ (2 : ℤ) :=
    hcopgY.dvd_of_dvd_mul_right hgY'
  have hcopg2 : IsCoprime g (2 : ℤ) :=
    hcopX2.of_isCoprime_of_dvd_left hgX
  have hg1 : g ∣ (1 : ℤ) := by
    rcases hcopg2 with ⟨a, b, hab⟩
    rcases hg2 with ⟨k, hk⟩
    refine ⟨a + b * k, ?_⟩
    rw [hk] at hab
    nlinarith
  have hgpos : 0 < g := by
    dsimp [g]
    exact core013_gcd_pos_of_left_ne_zero R S (ne_of_gt hRpos)
  rcases hg1 with ⟨k, hk⟩
  have hkpos : 0 < k := by nlinarith
  have hg_eq : Int.gcd R S = 1 := by
    have hg_le : g ≤ 1 := by nlinarith
    have hg_ge : (1 : ℤ) ≤ g := by omega
    have hgZ : g = 1 := by omega
    dsimp [g] at hgZ
    exact_mod_cast hgZ
  exact Int.isCoprime_iff_gcd_eq_one.mpr hg_eq

private lemma core013_half_square_split
    (R S M : ℤ)
    (hRpos : 0 < R) (hSpos : 0 < S) (hMpos : 0 < M)
    (hcop : IsCoprime R S)
    (hprod : R * S = 2 * M ^ 2) :
    (∃ a b : ℤ, 0 < a ∧ 0 < b ∧ R = a ^ 2 ∧ S = 2 * b ^ 2 ∧ a * b = M) ∨
    (∃ a b : ℤ, 0 < a ∧ 0 < b ∧ R = 2 * a ^ 2 ∧ S = b ^ 2 ∧ a * b = M) := by
  by_cases h2R : (2 : ℤ) ∣ R
  · right
    rcases h2R with ⟨R1, hR⟩
    have hR1pos : 0 < R1 := by
      rw [hR] at hRpos
      nlinarith
    have hR1S : R1 * S = M ^ 2 := by
      rw [hR] at hprod
      nlinarith
    have hcopR1S : IsCoprime R1 S := by
      rcases hcop with ⟨u, v, huv⟩
      refine ⟨2 * u, v, ?_⟩
      rw [hR] at huv
      nlinarith
    obtain ⟨a0, ha0 | ha0⟩ := Int.sq_of_isCoprime hcopR1S hR1S
    · obtain ⟨b0, hb0 | hb0⟩ :=
        Int.sq_of_isCoprime hcopR1S.symm (show S * R1 = M ^ 2 by nlinarith)
      · let a : ℤ := |a0|
        let b : ℤ := |b0|
        have ha : R1 = a ^ 2 := by
          dsimp [a]
          rw [sq_abs]
          exact ha0
        have hb : S = b ^ 2 := by
          dsimp [b]
          rw [sq_abs]
          exact hb0
        have hapos : 0 < a := by
          dsimp [a]
          exact abs_pos.mpr (by intro h0; rw [h0] at ha0; nlinarith)
        have hbpos : 0 < b := by
          dsimp [b]
          exact abs_pos.mpr (by intro h0; rw [h0] at hb0; nlinarith)
        have habsq : (a * b) ^ 2 = M ^ 2 := by
          rw [← hR1S, ha, hb]
          ring
        have hab : a * b = M := by
          have habnonneg : 0 ≤ a * b := mul_nonneg hapos.le hbpos.le
          exact (sq_eq_sq₀ habnonneg hMpos.le).mp habsq
        refine ⟨a, b, hapos, hbpos, ?_, hb, hab⟩
        rw [hR, ha]
      · nlinarith [sq_nonneg b0]
    · nlinarith [sq_nonneg a0]
  · left
    have h2S : (2 : ℤ) ∣ S := by
      have h2prod : (2 : ℤ) ∣ R * S := by
        rw [hprod]
        exact dvd_mul_right 2 (M ^ 2)
      rcases (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (2 : ℤ)).dvd_or_dvd h2prod with h | h
      · exact False.elim (h2R h)
      · exact h
    rcases h2S with ⟨S1, hS⟩
    have hS1pos : 0 < S1 := by
      rw [hS] at hSpos
      nlinarith
    have hRS1 : R * S1 = M ^ 2 := by
      rw [hS] at hprod
      nlinarith
    have hcopRS1 : IsCoprime R S1 := by
      rcases hcop with ⟨u, v, huv⟩
      refine ⟨u, 2 * v, ?_⟩
      rw [hS] at huv
      nlinarith
    obtain ⟨a0, ha0 | ha0⟩ := Int.sq_of_isCoprime hcopRS1 hRS1
    · obtain ⟨b0, hb0 | hb0⟩ :=
        Int.sq_of_isCoprime hcopRS1.symm (show S1 * R = M ^ 2 by nlinarith)
      · let a : ℤ := |a0|
        let b : ℤ := |b0|
        have ha : R = a ^ 2 := by
          dsimp [a]
          rw [sq_abs]
          exact ha0
        have hb : S1 = b ^ 2 := by
          dsimp [b]
          rw [sq_abs]
          exact hb0
        have hapos : 0 < a := by
          dsimp [a]
          exact abs_pos.mpr (by intro h0; rw [h0] at ha0; nlinarith)
        have hbpos : 0 < b := by
          dsimp [b]
          exact abs_pos.mpr (by intro h0; rw [h0] at hb0; nlinarith)
        have habsq : (a * b) ^ 2 = M ^ 2 := by
          rw [← hRS1, ha, hb]
          ring
        have hab : a * b = M := by
          have habnonneg : 0 ≤ a * b := mul_nonneg hapos.le hbpos.le
          exact (sq_eq_sq₀ habnonneg hMpos.le).mp habsq
        refine ⟨a, b, hapos, hbpos, ha, ?_, hab⟩
        rw [hS, hb]
      · nlinarith [sq_nonneg b0]
    · nlinarith [sq_nonneg a0]

private lemma core013_bad_half_branch_false
    (m n a b : ℤ)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (hX : m ^ 2 + n ^ 2 = 2 * a ^ 2 - b ^ 2)
    (hab : a * b = m * n) : False := by
  rcases Int.even_or_odd m with ⟨m0, hm0⟩ | ⟨m0, hm0⟩ <;>
    rcases Int.even_or_odd n with ⟨n0, hn0⟩ | ⟨n0, hn0⟩ <;>
      rcases Int.even_or_odd a with ⟨a0, ha0⟩ | ⟨a0, ha0⟩ <;>
        rcases Int.even_or_odd b with ⟨b0, hb0⟩ | ⟨b0, hb0⟩
  all_goals
    rw [hm0, hn0] at hpar
    rw [hm0, hn0, ha0, hb0] at hX hab
    ring_nf at hX hab hpar
    omega

private lemma core013_sqsum_odd_of_parity (m n : ℤ)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Odd (m ^ 2 + n ^ 2) := by
  rcases Int.even_or_odd m with ⟨m0, hm0⟩ | ⟨m0, hm0⟩ <;>
    rcases Int.even_or_odd n with ⟨n0, hn0⟩ | ⟨n0, hn0⟩
  all_goals
    rw [Int.odd_iff]
    rw [hm0, hn0] at hpar ⊢
    ring_nf at hpar ⊢
    omega

private lemma core013_gcd_scaled_three (a b : ℤ) :
    Int.gcd (3 * a) (3 * b) = 3 * Int.gcd a b := by
  rw [Int.gcd_def, Int.gcd_def]
  rw [Int.natAbs_mul, Int.natAbs_mul]
  norm_num
  rw [Nat.gcd_mul_left]

set_option maxHeartbeats 200000 in
private theorem core013_k10_descent
    (m n z : ℤ)
    (hmpos : 0 < m) (hnpos : 0 < n) (hzpos : 0 < z)
    (hmn_gcd : Int.gcd m n = 1)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (hK : z ^ 2 = m ^ 4 + 10 * m ^ 2 * n ^ 2 + n ^ 4) :
    ∃ A' B' C' D' : ℤ,
      0 < A' ∧ 0 < D' ∧
      B' ^ 2 = A' ^ 2 + D' ^ 2 ∧
      C' ^ 2 = A' ^ 2 + 3 * D' ^ 2 ∧
      D'.natAbs < (2 * m * n).natAbs := by
  let X : ℤ := m ^ 2 + n ^ 2
  have hXpos : 0 < X := by
    dsimp [X]
    nlinarith [sq_pos_of_pos hmpos]
  have hMpos : 0 < m * n := mul_pos hmpos hnpos
  have hzX : z ^ 2 = X ^ 2 + 2 * (2 * m * n) ^ 2 := by
    dsimp [X]
    rw [hK]
    ring
  have hXodd : Odd X := by
    dsimp [X]
    exact core013_sqsum_odd_of_parity m n hpar
  have hzodd : Odd z := by
    rcases Int.even_or_odd z with ⟨k, hk⟩ | hzodd
    · exfalso
      rcases hXodd with ⟨x, hx⟩
      rw [hk, hx] at hzX
      ring_nf at hzX
      omega
    · exact hzodd
  have hzgtX : X < z := by
    by_contra hnot
    have hzle : z ≤ X := le_of_not_gt hnot
    have hlt_sq : X ^ 2 < z ^ 2 := by
      rw [hzX]
      nlinarith [sq_pos_of_pos hMpos]
    nlinarith
  have h2plus : (2 : ℤ) ∣ z + X := by
    rcases hzodd with ⟨r, hr⟩
    rcases hXodd with ⟨s, hs⟩
    refine ⟨r + s + 1, ?_⟩
    rw [hr, hs]
    ring
  have h2minus : (2 : ℤ) ∣ z - X := by
    rcases hzodd with ⟨r, hr⟩
    rcases hXodd with ⟨s, hs⟩
    refine ⟨r - s, ?_⟩
    rw [hr, hs]
    ring
  rcases h2plus with ⟨R, hR⟩
  rcases h2minus with ⟨S, hS⟩
  have hRpos : 0 < R := by nlinarith
  have hSpos : 0 < S := by nlinarith
  have hsum : R + S = z := by nlinarith
  have hdiff : R - S = X := by nlinarith
  have hprod : R * S = 2 * (m * n) ^ 2 := by
    have hfac : (z + X) * (z - X) = 8 * (m * n) ^ 2 := by
      rw [show (z + X) * (z - X) = z ^ 2 - X ^ 2 by ring]
      rw [hzX]
      ring
    rw [hR, hS] at hfac
    nlinarith
  have hmnI : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
  have hcopRS : IsCoprime R S :=
    core013_half_factors_coprime m n z R S hRpos hmnI hXodd hR hS hzX
  rcases core013_half_square_split R S (m * n) hRpos hSpos hMpos hcopRS hprod with
    ⟨a, b, hapos, hbpos, hRa, hSb, hab⟩ | ⟨a, b, hapos, hbpos, hRa, hSb, hab⟩
  · have hmain : m ^ 2 + n ^ 2 = a ^ 2 - 2 * b ^ 2 := by
      dsimp [X] at hdiff
      rw [hRa, hSb] at hdiff
      exact hdiff.symm
    have hadivR : a ∣ R := by
      rw [hRa]
      exact ⟨a, by ring⟩
    have hbdivS : b ∣ S := by
      rw [hSb]
      exact ⟨2 * b, by ring⟩
    have hcop_aS : IsCoprime a S :=
      hcopRS.of_isCoprime_of_dvd_left hadivR
    have hcopab : IsCoprime a b :=
      hcop_aS.of_isCoprime_of_dvd_right hbdivS
    let P : ℕ := m.natAbs
    let Q : ℕ := n.natAbs
    let U : ℕ := a.natAbs
    let V : ℕ := b.natAbs
    have hPz : (P : ℤ) = m := by
      dsimp [P]
      exact Int.ofNat_natAbs_of_nonneg hmpos.le
    have hQz : (Q : ℤ) = n := by
      dsimp [Q]
      exact Int.ofNat_natAbs_of_nonneg hnpos.le
    have hUz : (U : ℤ) = a := by
      dsimp [U]
      exact Int.ofNat_natAbs_of_nonneg hapos.le
    have hVz : (V : ℤ) = b := by
      dsimp [V]
      exact Int.ofNat_natAbs_of_nonneg hbpos.le
    have hPpos : 0 < P := by dsimp [P]; exact Int.natAbs_pos.mpr (ne_of_gt hmpos)
    have hQpos : 0 < Q := by dsimp [Q]; exact Int.natAbs_pos.mpr (ne_of_gt hnpos)
    have hUpos : 0 < U := by dsimp [U]; exact Int.natAbs_pos.mpr (ne_of_gt hapos)
    have hVpos : 0 < V := by dsimp [V]; exact Int.natAbs_pos.mpr (ne_of_gt hbpos)
    have hPQ : P.Coprime Q := by
      dsimp [P, Q]
      exact nat_coprime_of_int_gcd_eq_one hmn_gcd
    have hUV : U.Coprime V := by
      dsimp [U, V]
      exact nat_coprime_of_int_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hcopab)
    have hPQUV : P * Q = U * V := by
      apply Int.ofNat_inj.mp
      rw [Nat.cast_mul, Nat.cast_mul, hPz, hQz, hUz, hVz]
      exact hab.symm
    let α : ℕ := P.gcd U
    let β : ℕ := P.gcd V
    let γ : ℕ := Q.gcd U
    let δ : ℕ := Q.gcd V
    obtain ⟨hPfac, hQfac, hUfac, hVfac⟩ :=
      core013_nat_matrix_factor hPQ hUV hPQUV
    have hαpos : 0 < α := by dsimp [α]; exact Nat.gcd_pos_of_pos_left U hPpos
    have hβpos : 0 < β := by dsimp [β]; exact Nat.gcd_pos_of_pos_left V hPpos
    have hγpos : 0 < γ := by dsimp [γ]; exact Nat.gcd_pos_of_pos_left U hQpos
    have hδpos : 0 < δ := by dsimp [δ]; exact Nat.gcd_pos_of_pos_left V hQpos
    have hαδN : α.Coprime δ := by
      have hαU : α ∣ U := by dsimp [α]; exact Nat.gcd_dvd_right P U
      have hδV : δ ∣ V := by dsimp [δ]; exact Nat.gcd_dvd_right Q V
      exact Nat.Coprime.coprime_dvd_right hδV
        (Nat.Coprime.coprime_dvd_left hαU hUV)
    have hβγN : β.Coprime γ := by
      have hβV : β ∣ V := by dsimp [β]; exact Nat.gcd_dvd_right P V
      have hγU : γ ∣ U := by dsimp [γ]; exact Nat.gcd_dvd_right Q U
      exact Nat.Coprime.coprime_dvd_right hγU
        (Nat.Coprime.coprime_dvd_left hβV hUV.symm)
    let αz : ℤ := α
    let βz : ℤ := β
    let γz : ℤ := γ
    let δz : ℤ := δ
    have hαzpos : 0 < αz := by dsimp [αz]; exact_mod_cast hαpos
    have hβzpos : 0 < βz := by dsimp [βz]; exact_mod_cast hβpos
    have hγzpos : 0 < γz := by dsimp [γz]; exact_mod_cast hγpos
    have hδzpos : 0 < δz := by dsimp [δz]; exact_mod_cast hδpos
    have hmf : m = αz * βz := by
      rw [← hPz, hPfac]
      rfl
    have hnf : n = γz * δz := by
      rw [← hQz, hQfac]
      rfl
    have haf : a = αz * γz := by
      rw [← hUz, hUfac]
      rfl
    have hbf : b = βz * δz := by
      rw [← hVz, hVfac]
      rfl
    have hcoeff :
        αz ^ 2 * (γz ^ 2 - βz ^ 2) =
          δz ^ 2 * (γz ^ 2 + 2 * βz ^ 2) := by
      have hmain' :
          (αz * βz) ^ 2 + (γz * δz) ^ 2 =
            (αz * γz) ^ 2 - 2 * (βz * δz) ^ 2 := by
        simpa [hmf, hnf, haf, hbf] using hmain
      have hid :
          αz ^ 2 * (γz ^ 2 - βz ^ 2) -
              δz ^ 2 * (γz ^ 2 + 2 * βz ^ 2)
            =
          (αz * γz) ^ 2 - 2 * (βz * δz) ^ 2 -
              ((αz * βz) ^ 2 + (γz * δz) ^ 2) := by
        ring
      apply sub_eq_zero.mp
      rw [hid, hmain']
      ring
    let L : ℤ := γz ^ 2 - βz ^ 2
    let W : ℤ := γz ^ 2 + 2 * βz ^ 2
    have hWpos : 0 < W := by dsimp [W]; positivity
    have hLpos : 0 < L := by
      have hright : 0 < δz ^ 2 * W := mul_pos (sq_pos_of_pos hδzpos) hWpos
      rw [← hcoeff] at hright
      have hright' : 0 < L * αz ^ 2 := by
        simpa [L, mul_comm] using hright
      exact pos_of_mul_pos_left hright' (sq_nonneg αz)
    have hαδI : IsCoprime αz δz := by
      rw [Int.isCoprime_iff_nat_coprime]
      simpa [αz, δz] using hαδN
    have hβγI : IsCoprime βz γz := by
      rw [Int.isCoprime_iff_nat_coprime]
      simpa [βz, γz] using hβγN
    have hgdvd : (Int.gcd L W : ℤ) ∣ (3 : ℤ) := by
      dsimp [L, W]
      exact core013_gcd_LR_dvd_three βz γz hβγI
    rcases core013_gcd_dvd_three_cases L W (ne_of_gt hLpos) hgdvd with hg | hg
    · have hLW : IsCoprime L W := Int.isCoprime_iff_gcd_eq_one.mpr hg
      obtain ⟨hLeq, hWeq⟩ :=
        core013_square_system_coprime αz δz L W hαzpos hδzpos hLpos hWpos hαδI hLW
          (by simpa [L, W] using hcoeff)
      refine ⟨δz, γz, αz, βz, hδzpos, hβzpos, ?_, ?_, ?_⟩
      · dsimp [L] at hLeq
        linarith
      · dsimp [L, W] at hLeq hWeq
        linarith
      · have hdropNat : β < 2 * (α * β * γ * δ) := by
          have hfactor : 1 < 2 * (α * γ * δ) := by
            have hprodpos : 0 < α * γ * δ := by positivity
            omega
          calc
            β < β * (2 * (α * γ * δ)) := lt_mul_of_one_lt_right hβpos hfactor
            _ = 2 * (α * β * γ * δ) := by ring
        have htarget : (2 * m * n).natAbs = 2 * (α * β * γ * δ) := by
          rw [hmf, hnf]
          dsimp [αz, βz, γz, δz]
          simp [Int.natAbs_mul]
          ring
        dsimp [βz]
        rw [htarget]
        exact hdropNat
    · have h3L : (3 : ℤ) ∣ L := by
        have hd := Int.gcd_dvd_left L W
        rw [hg] at hd
        exact_mod_cast hd
      have h3W : (3 : ℤ) ∣ W := by
        have hd := Int.gcd_dvd_right L W
        rw [hg] at hd
        exact_mod_cast hd
      rcases h3L with ⟨L1, hL1⟩
      rcases h3W with ⟨W1, hW1⟩
      have hL1pos : 0 < L1 := by rw [hL1] at hLpos; linarith
      have hW1pos : 0 < W1 := by rw [hW1] at hWpos; linarith
      have hcopL1W1 : IsCoprime L1 W1 := by
        have hscale : Int.gcd (3 * L1) (3 * W1) = 3 * Int.gcd L1 W1 :=
          core013_gcd_scaled_three L1 W1
        rw [← hL1, ← hW1, hg] at hscale
        have hg1 : Int.gcd L1 W1 = 1 := by omega
        exact Int.isCoprime_iff_gcd_eq_one.mpr hg1
      have hcoeff1 : αz ^ 2 * L1 = δz ^ 2 * W1 := by
        have hcoeffLW : αz ^ 2 * L = δz ^ 2 * W := by
          simpa [L, W] using hcoeff
        rw [hL1, hW1] at hcoeffLW
        have h3 : (3 : ℤ) * (αz ^ 2 * L1) = 3 * (δz ^ 2 * W1) := by
          calc
            (3 : ℤ) * (αz ^ 2 * L1) = αz ^ 2 * (3 * L1) := by ring
            _ = δz ^ 2 * (3 * W1) := hcoeffLW
            _ = 3 * (δz ^ 2 * W1) := by ring
        exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) h3
      obtain ⟨hL1eq, hW1eq⟩ :=
        core013_square_system_coprime αz δz L1 W1 hαzpos hδzpos hL1pos hW1pos
          hαδI hcopL1W1 hcoeff1
      refine ⟨βz, αz, γz, δz, hβzpos, hδzpos, ?_, ?_, ?_⟩
      · have hgamma : γz ^ 2 = βz ^ 2 + 3 * δz ^ 2 := by
          dsimp [L] at hL1
          rw [hL1eq] at hL1
          linarith
        dsimp [W] at hW1
        rw [hW1eq] at hW1
        linarith
      · dsimp [L] at hL1
        rw [hL1eq] at hL1
        linarith
      · have hdropNat : δ < 2 * (α * β * γ * δ) := by
          have hfactor : 1 < 2 * (α * β * γ) := by
            have hprodpos : 0 < α * β * γ := by positivity
            omega
          calc
            δ < δ * (2 * (α * β * γ)) := lt_mul_of_one_lt_right hδpos hfactor
            _ = 2 * (α * β * γ * δ) := by ring
        have htarget : (2 * m * n).natAbs = 2 * (α * β * γ * δ) := by
          rw [hmf, hnf]
          dsimp [αz, βz, γz, δz]
          simp [Int.natAbs_mul]
          ring
        dsimp [δz]
        rw [htarget]
        exact hdropNat
  · have hmain : m ^ 2 + n ^ 2 = 2 * a ^ 2 - b ^ 2 := by
      dsimp [X] at hdiff
      rw [hRa, hSb] at hdiff
      nlinarith
    exact False.elim (core013_bad_half_branch_false m n a b hpar hmain hab)

private lemma core013_primitive_parity
    (A B C D : ℤ)
    (hcop : Int.gcd A D = 1)
    (h1 : B ^ 2 = A ^ 2 + D ^ 2)
    (h2 : C ^ 2 = A ^ 2 + 3 * D ^ 2) :
    A % 2 = 1 ∧ D % 2 = 0 := by
  rcases Int.even_or_odd A with ⟨a, hA⟩ | ⟨a, hA⟩ <;>
    rcases Int.even_or_odd D with ⟨d, hD⟩ | ⟨d, hD⟩
  · subst A
    subst D
    have h2A : (2 : ℤ) ∣ a + a := ⟨a, by ring⟩
    have h2D : (2 : ℤ) ∣ d + d := ⟨d, by ring⟩
    have h2gcd : (2 : ℤ) ∣ (Int.gcd (a + a) (d + d) : ℤ) :=
      Int.dvd_coe_gcd h2A h2D
    rw [hcop] at h2gcd
    norm_num at h2gcd
  · subst A
    subst D
    rcases Int.even_or_odd C with ⟨c, hC⟩ | ⟨c, hC⟩
    · subst C
      ring_nf at h2
      omega
    · subst C
      ring_nf at h2
      omega
  · subst A
    subst D
    constructor <;> omega
  · subst A
    subst D
    rcases Int.even_or_odd B with ⟨b, hB⟩ | ⟨b, hB⟩
    · subst B
      ring_nf at h1
      omega
    · subst B
      ring_nf at h1
      omega

private lemma core013_reduce_gcd_step
    (A B C D : ℤ)
    (hApos : 0 < A) (hDpos : 0 < D)
    (h1 : B ^ 2 = A ^ 2 + D ^ 2)
    (h2 : C ^ 2 = A ^ 2 + 3 * D ^ 2)
    (hg_ne_one : Int.gcd A D ≠ 1) :
    ∃ A' B' C' D' : ℤ,
      0 < A' ∧ 0 < D' ∧
      B' ^ 2 = A' ^ 2 + D' ^ 2 ∧
      C' ^ 2 = A' ^ 2 + 3 * D' ^ 2 ∧
      D'.natAbs < D.natAbs := by
  let g : ℤ := Int.gcd A D
  have hgpos : 0 < g := by
    dsimp [g]
    exact core013_gcd_pos_of_left_ne_zero A D (ne_of_gt hApos)
  have hgne : g ≠ 0 := ne_of_gt hgpos
  have hg_gt_one : 1 < g := by
    by_contra hle
    have hg_le_one : g ≤ 1 := le_of_not_gt hle
    have hg_ge_one : (1 : ℤ) ≤ g := by omega
    have hg_one : g = 1 := by omega
    exact hg_ne_one (by simpa [g] using hg_one)
  have hgA : g ∣ A := by
    dsimp [g]
    exact Int.gcd_dvd_left A D
  have hgD : g ∣ D := by
    dsimp [g]
    exact Int.gcd_dvd_right A D
  have hg2A2 : g ^ 2 ∣ A ^ 2 := pow_dvd_pow_of_dvd hgA 2
  have hg2D2 : g ^ 2 ∣ D ^ 2 := pow_dvd_pow_of_dvd hgD 2
  rcases hgA with ⟨A', hAfac⟩
  rcases hgD with ⟨D', hDfac⟩
  have hA'pos : 0 < A' := by
    rw [hAfac] at hApos
    nlinarith
  have hD'pos : 0 < D' := by
    rw [hDfac] at hDpos
    nlinarith
  have hg2B2 : g ^ 2 ∣ B ^ 2 := by
    rw [h1]
    exact dvd_add hg2A2 hg2D2
  have hg2C2 : g ^ 2 ∣ C ^ 2 := by
    rw [h2]
    exact dvd_add hg2A2 (dvd_mul_of_dvd_right hg2D2 3)
  have hgB : g ∣ B :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hg2B2
  have hgC : g ∣ C :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hg2C2
  rcases hgB with ⟨B', hBfac⟩
  rcases hgC with ⟨C', hCfac⟩
  have hg2ne : g ^ 2 ≠ 0 := pow_ne_zero 2 hgne
  have h1' : B' ^ 2 = A' ^ 2 + D' ^ 2 := by
    rw [hAfac, hDfac, hBfac] at h1
    have hscaled : g ^ 2 * B' ^ 2 = g ^ 2 * (A' ^ 2 + D' ^ 2) := by
      nlinarith
    exact mul_left_cancel₀ hg2ne hscaled
  have h2' : C' ^ 2 = A' ^ 2 + 3 * D' ^ 2 := by
    rw [hAfac, hDfac, hCfac] at h2
    have hscaled : g ^ 2 * C' ^ 2 = g ^ 2 * (A' ^ 2 + 3 * D' ^ 2) := by
      nlinarith
    exact mul_left_cancel₀ hg2ne hscaled
  have hdrop : D'.natAbs < D.natAbs := by
    have hdropZ : (D'.natAbs : ℤ) < (D.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs]
      rw [abs_of_nonneg hD'pos.le]
      rw [hDfac, abs_of_nonneg (mul_nonneg hgpos.le hD'pos.le)]
      nlinarith
    exact_mod_cast hdropZ
  exact ⟨A', B', C', D', hA'pos, hD'pos, h1', h2', hdrop⟩

private theorem no_sq_at_0_1_3_pos_aux :
    ∀ n : ℕ, ∀ A B C D : ℤ,
      D.natAbs ≤ n →
      0 < A → 0 < D →
      B ^ 2 = A ^ 2 + D ^ 2 →
      C ^ 2 = A ^ 2 + 3 * D ^ 2 →
      False := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro A B C D hDn hApos hDpos h1 h2
      by_cases hcop : Int.gcd A D = 1
      · have hparAD := core013_primitive_parity A B C D hcop h1 h2
        have hBne : B ≠ 0 := by
          intro hB0
          rw [hB0] at h1
          nlinarith [sq_pos_of_pos hApos, sq_nonneg D]
        have hBpos : 0 < |B| := abs_pos.mpr hBne
        have htrip : PythagoreanTriple A D |B| := by
          unfold PythagoreanTriple
          nlinarith [h1, sq_abs B]
        obtain ⟨m, n0, hAeq, hDeq, _hBeq, hmngcd, hmnpar, hmnonneg⟩ :=
          htrip.coprime_classification' hcop hparAD.1 hBpos
        have hmpos : 0 < m := by
          have hmne : m ≠ 0 := by
            intro hm0
            rw [hm0] at hDeq
            nlinarith
          omega
        have hmnpos : 0 < m * n0 := by
          nlinarith
        have hmnpos' : 0 < n0 * m := by
          nlinarith
        have hnpos : 0 < n0 :=
          pos_of_mul_pos_left hmnpos' hmpos.le
        have hCne : C ≠ 0 := by
          intro hC0
          rw [hC0] at h2
          nlinarith [sq_pos_of_pos hApos, sq_pos_of_pos hDpos]
        have hCpos : 0 < |C| := abs_pos.mpr hCne
        have hK : |C| ^ 2 = m ^ 4 + 10 * m ^ 2 * n0 ^ 2 + n0 ^ 4 := by
          rw [sq_abs, h2, hAeq, hDeq]
          ring
        obtain ⟨A', B', C', D', hA'pos, hD'pos, h1', h2', hdrop⟩ :=
          core013_k10_descent m n0 |C| hmpos hnpos hCpos hmngcd hmnpar hK
        have hdropD : D'.natAbs < D.natAbs := by
          rw [hDeq]
          exact hdrop
        exact ih D'.natAbs (by omega) A' B' C' D' le_rfl hA'pos hD'pos h1' h2'
      · obtain ⟨A', B', C', D', hA'pos, hD'pos, h1', h2', hdrop⟩ :=
          core013_reduce_gcd_step A B C D hApos hDpos h1 h2 hcop
        exact ih D'.natAbs (by omega) A' B' C' D' le_rfl hA'pos hD'pos h1' h2'

private theorem no_sq_at_0_1_3 (A B C D : ℤ)
    (h1 : B ^ 2 = A ^ 2 + D ^ 2)
    (h2 : C ^ 2 = A ^ 2 + 3 * D ^ 2) :
    A * D = 0 := by
  by_contra hAD
  have hAne : A ≠ 0 := by
    intro hA0
    apply hAD
    rw [hA0]
    ring
  have hDne : D ≠ 0 := by
    intro hD0
    apply hAD
    rw [hD0]
    ring
  let A0 : ℤ := |A|
  let B0 : ℤ := |B|
  let C0 : ℤ := |C|
  let D0 : ℤ := |D|
  have hA0pos : 0 < A0 := by
    dsimp [A0]
    exact abs_pos.mpr hAne
  have hD0pos : 0 < D0 := by
    dsimp [D0]
    exact abs_pos.mpr hDne
  have h1abs : B0 ^ 2 = A0 ^ 2 + D0 ^ 2 := by
    dsimp [A0, B0, D0]
    rw [sq_abs, sq_abs, sq_abs]
    exact h1
  have h2abs : C0 ^ 2 = A0 ^ 2 + 3 * D0 ^ 2 := by
    dsimp [A0, C0, D0]
    rw [sq_abs, sq_abs, sq_abs]
    exact h2
  exact no_sq_at_0_1_3_pos_aux D0.natAbs A0 B0 C0 D0 le_rfl
    hA0pos hD0pos h1abs h2abs

private lemma n14_core_013_false
    (A B C D : ℤ) (hA : A ≠ 0) (hD : D ≠ 0)
    (h1 : B ^ 2 = A ^ 2 + D ^ 2)
    (h2 : C ^ 2 = A ^ 2 + 3 * D ^ 2) : False := by
  have hAD : A * D = 0 := no_sq_at_0_1_3 A B C D h1 h2
  rcases mul_eq_zero.mp hAD with hA0 | hD0
  · exact hA hA0
  · exact hD hD0

private lemma n14_pos_21_false
    (X Y Z N : ℤ) (hcopXN : Int.gcd X N = 1)
    (hA : 2 * X ^ 2 - Y ^ 2 = N ^ 2)
    (hB : Z ^ 2 - X ^ 2 = N ^ 2) : False := by
  rcases int_mod_three_cases X with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩ <;>
    rcases int_mod_three_cases Y with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩ <;>
      rcases int_mod_three_cases Z with ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ <;>
        rcases int_mod_three_cases N with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  · have h3X : (3 : ℤ) ∣ X := ⟨x, hx⟩
    have h3N : (3 : ℤ) ∣ N := ⟨n, hn⟩
    have h3gcd : (3 : ℤ) ∣ (Int.gcd X N : ℤ) := Int.dvd_coe_gcd h3X h3N
    rw [hcopXN] at h3gcd
    norm_num at h3gcd
  all_goals
    subst X; subst Y; subst Z; subst N
    ring_nf at hA hB
    omega

private lemma n14_neg_11_false
    (X Y Z N : ℤ) (hcopXN : Int.gcd X N = 1)
    (hA : Y ^ 2 - X ^ 2 = N ^ 2)
    (hB : Z ^ 2 + X ^ 2 = 2 * N ^ 2) : False := by
  rcases int_mod_three_cases X with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩ <;>
    rcases int_mod_three_cases Y with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩ <;>
      rcases int_mod_three_cases Z with ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ <;>
        rcases int_mod_three_cases N with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  · have h3X : (3 : ℤ) ∣ X := ⟨x, hx⟩
    have h3N : (3 : ℤ) ∣ N := ⟨n, hn⟩
    have h3gcd : (3 : ℤ) ∣ (Int.gcd X N : ℤ) := Int.dvd_coe_gcd h3X h3N
    rw [hcopXN] at h3gcd
    norm_num at h3gcd
  all_goals
    subst X; subst Y; subst Z; subst N
    ring_nf at hA hB
    omega

private lemma n14_pos_23_false
    (X Y N : ℤ) (hcop2XN : Int.gcd (2 * X) N = 1)
    (h : 2 * X ^ 2 - 3 * Y ^ 2 = N ^ 2) : False := by
  rcases Int.even_or_odd X with ⟨x, hx⟩ | ⟨x, hx⟩ <;>
    rcases Int.even_or_odd Y with ⟨y, hy⟩ | ⟨y, hy⟩ <;>
      rcases Int.even_or_odd N with ⟨n, hn⟩ | ⟨n, hn⟩
  · have h2X : (2 : ℤ) ∣ 2 * (x + x) := ⟨x + x, by ring⟩
    have h2N : (2 : ℤ) ∣ n + n := ⟨n, by ring⟩
    have h2gcd : (2 : ℤ) ∣ (Int.gcd (2 * (x + x)) (n + n) : ℤ) :=
      Int.dvd_coe_gcd h2X h2N
    rw [← hx, ← hn, hcop2XN] at h2gcd
    norm_num at h2gcd
  · subst X; subst Y; subst N
    rcases Int.even_or_odd y with ⟨y0, hy0⟩ | ⟨y0, hy0⟩ <;>
      rcases Int.even_or_odd n with ⟨n0, hn0⟩ | ⟨n0, hn0⟩
    all_goals
      rw [hy0, hn0] at h
      ring_nf at h
      omega
  · have h2X : (2 : ℤ) ∣ 2 * (x + x) := ⟨x + x, by ring⟩
    have h2N : (2 : ℤ) ∣ n + n := ⟨n, by ring⟩
    have h2gcd : (2 : ℤ) ∣ (Int.gcd (2 * (x + x)) (n + n) : ℤ) :=
      Int.dvd_coe_gcd h2X h2N
    rw [← hx, ← hn, hcop2XN] at h2gcd
    norm_num at h2gcd
  · subst X; subst Y; subst N
    rcases Int.even_or_odd y with ⟨y0, hy0⟩ | ⟨y0, hy0⟩ <;>
      rcases Int.even_or_odd n with ⟨n0, hn0⟩ | ⟨n0, hn0⟩
    all_goals
      rw [hy0, hn0] at h
      ring_nf at h
      omega
  · have h2X : (2 : ℤ) ∣ 2 * (2 * x + 1) := ⟨2 * x + 1, by ring⟩
    have h2N : (2 : ℤ) ∣ n + n := ⟨n, by ring⟩
    have h2gcd : (2 : ℤ) ∣ (Int.gcd (2 * (2 * x + 1)) (n + n) : ℤ) :=
      Int.dvd_coe_gcd h2X h2N
    rw [← hx, ← hn, hcop2XN] at h2gcd
    norm_num at h2gcd
  · subst X; subst Y; subst N
    ring_nf at h
    omega
  · have h2X : (2 : ℤ) ∣ 2 * (2 * x + 1) := ⟨2 * x + 1, by ring⟩
    have h2N : (2 : ℤ) ∣ n + n := ⟨n, by ring⟩
    have h2gcd : (2 : ℤ) ∣ (Int.gcd (2 * (2 * x + 1)) (n + n) : ℤ) :=
      Int.dvd_coe_gcd h2X h2N
    rw [← hx, ← hn, hcop2XN] at h2gcd
    norm_num at h2gcd
  · subst X; subst Y; subst N
    ring_nf at h
    omega

private lemma n14_neg_13_false
    (X Y N : ℤ) (hcopXN : Int.gcd X N = 1)
    (h : 3 * Y ^ 2 = X ^ 2 + N ^ 2) : False := by
  rcases Int.even_or_odd X with ⟨x, hx⟩ | ⟨x, hx⟩ <;>
    rcases Int.even_or_odd Y with ⟨y, hy⟩ | ⟨y, hy⟩ <;>
      rcases Int.even_or_odd N with ⟨n, hn⟩ | ⟨n, hn⟩
  · have h2X : (2 : ℤ) ∣ x + x := ⟨x, by ring⟩
    have h2N : (2 : ℤ) ∣ n + n := ⟨n, by ring⟩
    have h2gcd : (2 : ℤ) ∣ (Int.gcd (x + x) (n + n) : ℤ) :=
      Int.dvd_coe_gcd h2X h2N
    rw [← hx, ← hn, hcopXN] at h2gcd
    norm_num at h2gcd
  all_goals
    subst X; subst Y; subst N
    ring_nf at h
    omega

private lemma n14_factor_coprime_N
    (A N k : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A + k * N ^ 2) N := by
  have h := hcop.add_mul_right_left (k * N)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h

private lemma n14_F1_coprime_N (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime A N := hcop

private lemma n14_F2_coprime_N (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A - N ^ 2) N := by
  simpa [sub_eq_add_neg] using n14_factor_coprime_N A N (-1) hcop

private lemma n14_F3_coprime_N (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime (A + 2 * N ^ 2) N := by
  simpa [mul_assoc] using n14_factor_coprime_N A N 2 hcop

private lemma n14_F1_F2_coprime (A N : ℤ) (hcop : IsCoprime A N) :
    IsCoprime A (A - N ^ 2) := by
  have hF2N : IsCoprime (A - N ^ 2) N := n14_F2_coprime_N A N hcop
  have hF2N2 : IsCoprime (N ^ 2) (A - N ^ 2) := hF2N.symm.pow_left
  have h := hF2N2.add_mul_right_left 1
  have hrewrite : N ^ 2 + 1 * (A - N ^ 2) = A := by ring
  rwa [hrewrite] at h

private lemma n14_gcd_F1_F3_dvd_two
    (A N : ℤ) (hcop : IsCoprime A N) :
    (Int.gcd A (A + 2 * N ^ 2) : ℤ) ∣ (2 : ℤ) := by
  let g : ℤ := Int.gcd A (A + 2 * N ^ 2)
  have hgF1 : g ∣ A := by
    dsimp [g]
    exact Int.gcd_dvd_left _ _
  have hgF3 : g ∣ A + 2 * N ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_right _ _
  have hg2N2 : g ∣ 2 * N ^ 2 := by
    have hsub : g ∣ (A + 2 * N ^ 2) - A := dvd_sub hgF3 hgF1
    convert hsub using 1
    ring
  have hF1N : IsCoprime A N := n14_F1_coprime_N A N hcop
  have hgN : IsCoprime g N := by
    rcases hF1N with ⟨r, s, hrs⟩
    rcases hgF1 with ⟨t, ht⟩
    refine ⟨r * t, s, ?_⟩
    rw [ht] at hrs
    nlinarith
  have hgN2 : IsCoprime g (N ^ 2) := hgN.pow_right
  exact hgN2.dvd_of_dvd_mul_right hg2N2

private lemma n14_gcd_F2_F3_dvd_three
    (A N : ℤ) (hcop : IsCoprime A N) :
    (Int.gcd (A - N ^ 2) (A + 2 * N ^ 2) : ℤ) ∣ (3 : ℤ) := by
  let g : ℤ := Int.gcd (A - N ^ 2) (A + 2 * N ^ 2)
  have hgF2 : g ∣ A - N ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_left _ _
  have hgF3 : g ∣ A + 2 * N ^ 2 := by
    dsimp [g]
    exact Int.gcd_dvd_right _ _
  have hg3N2 : g ∣ 3 * N ^ 2 := by
    have hsub : g ∣ (A + 2 * N ^ 2) - (A - N ^ 2) := dvd_sub hgF3 hgF2
    convert hsub using 1
    ring
  have hF2N : IsCoprime (A - N ^ 2) N := n14_F2_coprime_N A N hcop
  have hgN : IsCoprime g N := by
    rcases hF2N with ⟨r, s, hrs⟩
    rcases hgF2 with ⟨t, ht⟩
    refine ⟨r * t, s, ?_⟩
    rw [ht] at hrs
    nlinarith
  have hgN2 : IsCoprime g (N ^ 2) := hgN.pow_right
  exact hgN2.dvd_of_dvd_mul_right hg3N2

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

private lemma n14_gcd_pos_of_left_ne_zero (a b : ℤ) (ha : a ≠ 0) :
    0 < (Int.gcd a b : ℤ) := by
  have hg : Int.gcd a b ≠ 0 := by
    intro hg0
    have hd : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
    rw [hg0] at hd
    exact ha (by simpa using hd)
  exact_mod_cast Nat.pos_of_ne_zero hg

private lemma n14_gcd_dvd_three_cases (a b : ℤ) (ha : a ≠ 0)
    (h : (Int.gcd a b : ℤ) ∣ (3 : ℤ)) :
    Int.gcd a b = 1 ∨ Int.gcd a b = 3 := by
  let g : ℕ := Int.gcd a b
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using n14_gcd_pos_of_left_ne_zero a b ha
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

private lemma n14_gcd_dvd_two_cases (a b : ℤ) (ha : a ≠ 0)
    (h : (Int.gcd a b : ℤ) ∣ (2 : ℤ)) :
    Int.gcd a b = 1 ∨ Int.gcd a b = 2 := by
  let g : ℕ := Int.gcd a b
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using n14_gcd_pos_of_left_ne_zero a b ha
  rcases h with ⟨k, hk⟩
  have hk' : (g : ℤ) * k = 2 := by simpa [g, mul_comm] using hk.symm
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 2 := by nlinarith
  interval_cases k
  · right
    omega
  · left
    omega

private lemma n14_gcd_dvd_four_cases (a b : ℤ) (ha : a ≠ 0)
    (h : (Int.gcd a b : ℤ) ∣ (4 : ℤ)) :
    Int.gcd a b = 1 ∨ Int.gcd a b = 2 ∨ Int.gcd a b = 4 := by
  let g : ℕ := Int.gcd a b
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using n14_gcd_pos_of_left_ne_zero a b ha
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

private lemma n14_coprime_stripped_of_gcd_eq
    (d : ℕ) (hdpos : 0 < d)
    {U W F G : ℤ} (hU : U ≠ 0)
    (hF : F = (d : ℤ) * U) (hG : G = (d : ℤ) * W)
    (hgcd : Int.gcd F G = d) :
    IsCoprime U W := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  let g : ℕ := Int.gcd U W
  have hgpos : 0 < (g : ℤ) := by
    simpa [g] using n14_gcd_pos_of_left_ne_zero U W hU
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

private lemma n14_three_square_from_factors_pos
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
    n14_coprime_stripped_of_gcd_eq d13 hd13pos (ne_of_gt hUpos) hF1 hF3_d13 hg13
  have hUW : IsCoprime U W := hU_d23W.of_mul_right_right
  have hF3_d23 : F3 = (d23 : ℤ) * ((d13 : ℤ) * W) := by
    rw [hF3]
    ring
  have hV_d13W : IsCoprime V ((d13 : ℤ) * W) :=
    n14_coprime_stripped_of_gcd_eq d23 hd23pos (ne_of_gt hVpos) hF2 hF3_d23 hg23
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

private lemma n14_three_square_from_factors_neg
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
    n14_coprime_stripped_of_gcd_eq d13 hd13pos
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
    n14_coprime_stripped_of_gcd_eq d23 hd23pos
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

private lemma n14_pos_squareclass_from_gcd
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
    n14_three_square_from_factors_pos U V W F1 F2 F3 C d13 d23
      hd13pos hd23pos hUpos hVpos hWpos hF1U hF2V hF3W' h12 hg13 hg23 hprod
  refine ⟨X, Y, Z, ?_, ?_, ?_⟩
  · rw [hF1U, hX]
  · rw [hF2V, hY]
  · rw [hF3W', hZ]

private lemma n14_neg_squareclass_from_gcd
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
    n14_three_square_from_factors_neg U V W F1 F2 F3 C d13 d23
      hd13pos hd23pos hUpos hVpos hWpos hF1U hF2V hF3W' h12 hg13 hg23 hprod
  refine ⟨X, Y, Z, ?_, ?_, ?_⟩
  · rw [hF1U, hX]
  · rw [hF2V, hY]
  · rw [hF3W', hZ]

private lemma n14_u_eq_int
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

end ObstructionN14

open ObstructionN14

theorem obstruction_N14 (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - 2 * u) :
    u = -2 ∨ u = 0 ∨ u = 1 := by
  rcases n14_clear_denominators u w h with ⟨A, N, C, hNpos, hAN, hu, hprod0⟩
  have hNne : N ≠ 0 := ne_of_gt hNpos
  let F1 : ℤ := A
  let F2 : ℤ := A - N ^ 2
  let F3 : ℤ := A + 2 * N ^ 2
  have hprod : C ^ 2 = F1 * F2 * F3 := by
    rw [hprod0]
    dsimp [F1, F2, F3]
    ring
  have finishA :
      A = -2 * N ^ 2 ∨ A = 0 ∨ A = N ^ 2 →
        u = -2 ∨ u = 0 ∨ u = 1 := by
    intro hAvals
    rcases hAvals with hA | hA | hA
    · left
      have hu' := n14_u_eq_int u hNne hu (c := -2) (by simpa using hA)
      simpa using hu'
    · right; left
      have hAc : A = (0 : ℤ) * N ^ 2 := by
        rw [hA]
        ring
      have hu' := n14_u_eq_int u hNne hu (c := 0) hAc
      simpa using hu'
    · right; right
      have hAc : A = (1 : ℤ) * N ^ 2 := by
        rw [hA]
        ring
      have hu' := n14_u_eq_int u hNne hu (c := 1) hAc
      simpa using hu'
  by_cases hF1zero : F1 = 0
  · apply finishA
    right; left
    dsimp [F1] at hF1zero
    nlinarith
  by_cases hF2zero : F2 = 0
  · apply finishA
    right; right
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
    simpa [F1, F2] using n14_F1_F2_coprime A N hcopAN
  have h13dvd : (Int.gcd F1 F3 : ℤ) ∣ (2 : ℤ) := by
    simpa [F1, F3] using n14_gcd_F1_F3_dvd_two A N hcopAN
  have h23dvd : (Int.gcd F2 F3 : ℤ) ∣ (3 : ℤ) := by
    simpa [F2, F3] using n14_gcd_F2_F3_dvd_three A N hcopAN
  have hF1N : IsCoprime F1 N := by
    simpa [F1] using n14_F1_coprime_N A N hcopAN
  have hF2N : IsCoprime F2 N := by
    simpa [F2] using n14_F2_coprime_N A N hcopAN
  have gcd_of_dvd {T F : ℤ} (hFN : IsCoprime F N) (hTF : T ∣ F) :
      Int.gcd T N = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (hFN.of_isCoprime_of_dvd_left hTF)
  have hF2ltF1 : F2 < F1 := by
    dsimp [F1, F2]
    nlinarith [sq_pos_of_ne_zero hNne]
  have hF1ltF3 : F1 < F3 := by
    dsimp [F1, F3]
    nlinarith [sq_pos_of_ne_zero hNne]
  have hF2ltF3 : F2 < F3 := by
    dsimp [F2, F3]
    nlinarith [sq_pos_of_ne_zero hNne]
  have hprod_nonneg : 0 ≤ F1 * F2 * F3 := by
    rw [← hprod]
    exact sq_nonneg C
  have hsign :
      (0 < F1 ∧ 0 < F2 ∧ 0 < F3) ∨ (F1 < 0 ∧ F2 < 0 ∧ 0 < F3) := by
    by_cases hF1pos : 0 < F1
    · by_cases hF2pos : 0 < F2
      · left
        exact ⟨hF1pos, hF2pos, by nlinarith⟩
      · have hF2neg : F2 < 0 := lt_of_le_of_ne (not_lt.mp hF2pos) hF2nz
        have hp13 : 0 < F1 * F3 := mul_pos hF1pos (by nlinarith)
        have hnegprod : F1 * F2 * F3 < 0 := by
          nlinarith [mul_neg_of_pos_of_neg hp13 hF2neg]
        nlinarith
    · have hF1neg : F1 < 0 := lt_of_le_of_ne (not_lt.mp hF1pos) hF1nz
      have hF2neg : F2 < 0 := by nlinarith
      by_cases hF3pos : 0 < F3
      · right
        exact ⟨hF1neg, hF2neg, hF3pos⟩
      · have hF3neg : F3 < 0 := lt_of_le_of_ne (not_lt.mp hF3pos) hF3nz
        have hp12 : 0 < F1 * F2 := mul_pos_of_neg_of_neg hF1neg hF2neg
        have hnegprod : F1 * F2 * F3 < 0 := by
          nlinarith [mul_neg_of_pos_of_neg hp12 hF3neg]
        nlinarith
  have h13cases := n14_gcd_dvd_two_cases F1 F3 hF1nz h13dvd
  have h23cases := n14_gcd_dvd_three_cases F2 F3 hF2nz h23dvd
  rcases hsign with ⟨hF1pos, hF2pos, hF3pos⟩ | ⟨hF1neg, hF2neg, hF3pos⟩
  · rcases h13cases with hg13 | hg13
    · rcases h23cases with hg23 | hg23
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_pos_squareclass_from_gcd F1 F2 F3 C 1 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        exfalso
        have hYne : Y ≠ 0 := by
          intro hY0
          apply hF2nz
          rw [h2, hY0]
          ring
        have hB : X ^ 2 = Y ^ 2 + N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        have hC : Z ^ 2 = Y ^ 2 + 3 * N ^ 2 := by
          dsimp [F2, F3] at h2 h3
          nlinarith
        exact n14_core_013_false Y X Z N hYne hNne hB hC
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_pos_squareclass_from_gcd F1 F2 F3 C 1 3
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        exfalso
        have hYne : Y ≠ 0 := by
          intro hY0
          apply hF2nz
          rw [h2, hY0]
          ring
        have hB : Z ^ 2 = N ^ 2 + Y ^ 2 := by
          dsimp [F2, F3] at h2 h3
          nlinarith
        have hC : X ^ 2 = N ^ 2 + 3 * Y ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        exact n14_core_013_false N Z X Y hNne hYne hB hC
    · rcases h23cases with hg23 | hg23
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_pos_squareclass_from_gcd F1 F2 F3 C 2 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        exfalso
        have hXdvdF1 : X ∣ F1 := by
          rw [h1]
          exact ⟨2 * X, by ring⟩
        have hcopXN : Int.gcd X N = 1 := gcd_of_dvd hF1N hXdvdF1
        have hAeq : 2 * X ^ 2 - Y ^ 2 = N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        have hBeq : Z ^ 2 - X ^ 2 = N ^ 2 := by
          dsimp [F1, F3] at h1 h3
          nlinarith
        exact n14_pos_21_false X Y Z N hcopXN hAeq hBeq
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_pos_squareclass_from_gcd F1 F2 F3 C 2 3
            (by norm_num) (by norm_num) (by norm_num)
            hF1pos hF2pos hF3pos h12 hg13 hg23 hprod
        exfalso
        have h2XdvdF1 : (2 * X) ∣ F1 := by
          rw [h1]
          exact ⟨X, by ring⟩
        have hcop2XN : Int.gcd (2 * X) N = 1 := gcd_of_dvd hF1N h2XdvdF1
        have heq : 2 * X ^ 2 - 3 * Y ^ 2 = N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        exact n14_pos_23_false X Y N hcop2XN heq
  · rcases h13cases with hg13 | hg13
    · rcases h23cases with hg23 | hg23
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_neg_squareclass_from_gcd F1 F2 F3 C 1 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        exfalso
        have hXdvdF1 : X ∣ F1 := by
          rw [h1]
          exact ⟨-X, by ring⟩
        have hcopXN : Int.gcd X N = 1 := gcd_of_dvd hF1N hXdvdF1
        have hAeq : Y ^ 2 - X ^ 2 = N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        have hBeq : Z ^ 2 + X ^ 2 = 2 * N ^ 2 := by
          dsimp [F1, F3] at h1 h3
          nlinarith
        exact n14_neg_11_false X Y Z N hcopXN hAeq hBeq
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_neg_squareclass_from_gcd F1 F2 F3 C 1 3
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        exfalso
        have hXdvdF1 : X ∣ F1 := by
          rw [h1]
          exact ⟨-X, by ring⟩
        have hcopXN : Int.gcd X N = 1 := gcd_of_dvd hF1N hXdvdF1
        have heq : 3 * Y ^ 2 = X ^ 2 + N ^ 2 := by
          dsimp [F1, F2] at h1 h2
          nlinarith
        exact n14_neg_13_false X Y N hcopXN heq
    · rcases h23cases with hg23 | hg23
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_neg_squareclass_from_gcd F1 F2 F3 C 2 1
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        exfalso
        have hXne : X ≠ 0 := by
          intro hX0
          apply hF1nz
          rw [h1, hX0]
          ring
        have hZne : Z ≠ 0 := by
          intro hZ0
          apply hF3nz
          rw [h3, hZ0]
          ring
        have hB : N ^ 2 = Z ^ 2 + X ^ 2 := by
          dsimp [F1, F3] at h1 h3
          nlinarith
        have hC : Y ^ 2 = Z ^ 2 + 3 * X ^ 2 := by
          dsimp [F1, F2, F3] at h1 h2 h3
          nlinarith
        exact n14_core_013_false Z N Y X hZne hXne hB hC
      · obtain ⟨X, Y, Z, h1, h2, h3⟩ :=
          n14_neg_squareclass_from_gcd F1 F2 F3 C 2 3
            (by norm_num) (by norm_num) (by norm_num)
            hF1neg hF2neg hF3pos h12 hg13 hg23 hprod
        exfalso
        have hXne : X ≠ 0 := by
          intro hX0
          apply hF1nz
          rw [h1, hX0]
          ring
        have hZne : Z ≠ 0 := by
          intro hZ0
          apply hF3nz
          rw [h3, hZ0]
          ring
        have hB : Y ^ 2 = X ^ 2 + Z ^ 2 := by
          dsimp [F1, F2, F3] at h1 h2 h3
          nlinarith
        have hC : N ^ 2 = X ^ 2 + 3 * Z ^ 2 := by
          dsimp [F1, F3] at h1 h3
          nlinarith
        exact n14_core_013_false X Y N Z hXne hZne hB hC
