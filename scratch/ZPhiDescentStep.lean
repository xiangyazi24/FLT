import Mathlib

set_option maxHeartbeats 1200000

/-!
# Structured proof skeleton for `zphi_descent_step`

This file matches the signature in `scratch/DenominatorQuartic.lean`.
The final wrapper is complete once the two core descent lemmas are supplied.
-/

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

/-- `q.natAbs` is nonzero under the denominator hypothesis. -/
private lemma zphi_q_natAbs_pos {q : ℤ} (hq : 2 ≤ q) : 0 < q.natAbs := by
  have hqpos : 0 < q := by omega
  exact Int.natAbs_pos.mpr (by omega)

/-- Odd `q` core.

Mathematical content intended here:
* from `h` and `Int.gcd p q = 1`, prove `Int.gcd t q = 1`;
* prove the Pellian factors `A,B` are positive and coprime;
* split coprime positive factors of `5*q^4` as `{5*m^4,n^4}` with `m*n=q`;
* compare coefficients to obtain `p^2 = m^4 + ((n^2-m^2)/2)^2`;
* parametrize the primitive Pythagorean triple;
* produce a new denominator `q'` with `2 ≤ q'` and `q'.natAbs < q.natAbs`.

This is the hard algebraic-number-theory/Pythagorean descent package, not a
routine linear-arithmetic lemma. -/

private lemma int_mod_four_cases (z : ℤ) :
    (∃ q : ℤ, z = 4 * q) ∨
      (∃ q : ℤ, z = 4 * q + 1) ∨
        (∃ q : ℤ, z = 4 * q + 2) ∨
          (∃ q : ℤ, z = 4 * q - 1) := by
  have hm : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
  rcases hm with h | h | h | h
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
    (∃ q : ℤ, z = 4 * q + 1) ∨ (∃ q : ℤ, z = 4 * q - 1) := by
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

private lemma square_not_sixteen_mul_add_five (t K : ℤ)
    (h : t ^ 2 = 16 * K + 5) : False := by
  rcases int_mod_four_cases t with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have : 16 * c ^ 2 = 16 * K + 5 := by nlinarith
    omega
  · have : 16 * c ^ 2 + 8 * c + 1 = 16 * K + 5 := by nlinarith
    omega
  · have : 16 * c ^ 2 + 16 * c + 4 = 16 * K + 5 := by nlinarith
    omega
  · have : 16 * c ^ 2 - 8 * c + 1 = 16 * K + 5 := by nlinarith
    omega

private lemma q_two_times_odd_half_contra (p s t : ℤ)
    (hpodd : Odd p) (hsodd : Odd s)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * (2 * s) ^ 2 - (2 * s) ^ 4) : False := by
  rcases int_odd_mod_four_cases p hpodd with ⟨a, hp⟩ | ⟨a, hp⟩
  · rcases int_odd_mod_four_cases s hsodd with ⟨b, hs⟩ | ⟨b, hs⟩
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-1 - 14 * b + 3 * a - 92 * b ^ 2 + 16 * a * b + 10 * a ^ 2 -
            256 * b ^ 3 + 32 * a * b ^ 2 + 32 * a ^ 2 * b + 16 * a ^ 3 -
            256 * b ^ 4 + 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 5 := by
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_five t _ hmod
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-1 + 14 * b + 3 * a - 92 * b ^ 2 - 16 * a * b + 10 * a ^ 2 +
            256 * b ^ 3 + 32 * a * b ^ 2 - 32 * a ^ 2 * b + 16 * a ^ 3 -
            256 * b ^ 4 + 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 5 := by
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_five t _ hmod
  · rcases int_odd_mod_four_cases s hsodd with ⟨b, hs⟩ | ⟨b, hs⟩
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-1 - 14 * b - 3 * a - 92 * b ^ 2 - 16 * a * b + 10 * a ^ 2 -
            256 * b ^ 3 - 32 * a * b ^ 2 + 32 * a ^ 2 * b - 16 * a ^ 3 -
            256 * b ^ 4 + 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 5 := by
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_five t _ hmod
    · rw [hp, hs] at h
      have hmod : t ^ 2 = 16 *
          (-1 + 14 * b - 3 * a - 92 * b ^ 2 + 16 * a * b + 10 * a ^ 2 +
            256 * b ^ 3 - 32 * a * b ^ 2 - 32 * a ^ 2 * b - 16 * a ^ 3 -
            256 * b ^ 4 + 64 * a ^ 2 * b ^ 2 + 16 * a ^ 4) + 5 := by
        ring_nf at h ⊢
        exact h
      exact square_not_sixteen_mul_add_five t _ hmod

private theorem coprime_product_eq_fourth_power
    (X Y q : ℤ)
    (hXpos : 0 < X)
    (hYpos : 0 < Y)
    (hqpos : 0 < q)
    (hcop : IsCoprime X Y)
    (hXY : X * Y = q ^ 4) :
    ∃ m n : ℤ,
      X = m ^ 4 ∧
      Y = n ^ 4 ∧
      m * n = q ∧
      0 < m ∧
      0 < n := by
  obtain ⟨m0, hm0assoc⟩ :=
    exists_associated_pow_of_mul_eq_pow' (R := ℤ) (a := X) (b := Y) (c := q)
      hcop (k := 4) hXY
  obtain ⟨n0, hn0assoc⟩ :=
    exists_associated_pow_of_mul_eq_pow' (R := ℤ) (a := Y) (b := X) (c := q)
      hcop.symm (k := 4) (by simpa [mul_comm] using hXY)
  let m : ℤ := m0.natAbs
  let n : ℤ := n0.natAbs
  have hmAbs : (m0 ^ 4).natAbs = X.natAbs :=
    Int.natAbs_eq_iff_associated.mpr hm0assoc
  have hnAbs : (n0 ^ 4).natAbs = Y.natAbs :=
    Int.natAbs_eq_iff_associated.mpr hn0assoc
  have hmX : X = m ^ 4 := by
    calc
      X = (X.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_nonneg hXpos.le]
      _ = ((m0 ^ 4).natAbs : ℤ) := by rw [hmAbs]
      _ = m ^ 4 := by
        dsimp [m]
        rw [Int.natAbs_pow]
        norm_num
  have hnY : Y = n ^ 4 := by
    calc
      Y = (Y.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_nonneg hYpos.le]
      _ = ((n0 ^ 4).natAbs : ℤ) := by rw [hnAbs]
      _ = n ^ 4 := by
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
  have hmn_pow : (m * n) ^ 4 = q ^ 4 := by
    calc
      (m * n) ^ 4 = m ^ 4 * n ^ 4 := by ring
      _ = X * Y := by rw [← hmX, ← hnY]
      _ = q ^ 4 := hXY
  have hmn_nonneg : 0 ≤ m * n := by nlinarith
  have hmn : m * n = q := by
    have hsq : (m * n) ^ 2 = q ^ 2 := by
      apply (sq_eq_sq₀ (sq_nonneg (m * n)) (sq_nonneg q)).mp
      nlinarith [hmn_pow]
    have hmn_abs : (m * n).natAbs = q.natAbs :=
      Int.natAbs_eq_iff_sq_eq.mpr hsq
    exact (Int.natAbs_inj_of_nonneg_of_nonneg hmn_nonneg hqpos.le).mp hmn_abs
  exact ⟨m, n, hmX, hnY, hmn, hmpos, hnpos⟩

private theorem coprime_fourth_power_factor
    (A B q : ℤ)
    (hAB : A * B = 5 * q ^ 4)
    (hcop : IsCoprime A B)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hqpos : 0 < q)
    (h5A : (5 : ℤ) ∣ A) :
    ∃ m n : ℤ,
      A = 5 * m ^ 4 ∧
      B = n ^ 4 ∧
      m * n = q ∧
      0 < m ∧
      0 < n := by
  rcases h5A with ⟨X, hAX⟩
  have hXpos : 0 < X := by
    rw [hAX] at hApos
    nlinarith
  have hXY : X * B = q ^ 4 := by
    rw [hAX] at hAB
    nlinarith
  have hcopXB : IsCoprime X B := by
    rcases hcop with ⟨r, s, hbez⟩
    refine ⟨5 * r, s, ?_⟩
    rw [hAX] at hbez
    nlinarith
  obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
    coprime_product_eq_fourth_power X B q hXpos hBpos hqpos hcopXB hXY
  refine ⟨m, n, ?_, hn, hmn, hmpos, hnpos⟩
  rw [hAX, hm]

private lemma zphi_pellian_factors_pos (p q t : ℤ)
    (hq : 2 ≤ q)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    0 < zphiA p q t ∧ 0 < zphiB p q t := by
  have hprod := zphi_AB_eq_5q4 p q t h
  have hsum := zphi_A_add_B p q t
  have hsum_pos : 0 < zphiA p q t + zphiB p q t := by
    rw [hsum]
    nlinarith [sq_nonneg p, sq_nonneg q]
  have hprod_pos : 0 < zphiA p q t * zphiB p q t := by
    rw [hprod]
    positivity
  by_cases hA : 0 < zphiA p q t
  · by_cases hB : 0 < zphiB p q t
    · exact ⟨hA, hB⟩
    · have hBle : zphiB p q t ≤ 0 := by omega
      have hnonpos : zphiA p q t * zphiB p q t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA) hBle
      nlinarith
  · have hAle : zphiA p q t ≤ 0 := by omega
    by_cases hB : 0 < zphiB p q t
    · have hnonpos : zphiA p q t * zphiB p q t ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hAle (le_of_lt hB)
      nlinarith
    · have hBle : zphiB p q t ≤ 0 := by omega
      have hsum_nonpos : zphiA p q t + zphiB p q t ≤ 0 := by omega
      nlinarith

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

private lemma zphi_descent_step_odd_core
    (p q t : ℤ)
    (hq : 2 ≤ q)
    (hqodd : ¬ (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  -- Pellian setup available to the descent core:
  have hAB : zphiA p q t * zphiB p q t = 5 * q ^ 4 :=
    zphi_AB_eq_5q4 p q t h
  have hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2) :=
    zphi_A_add_B p q t
  have hdiff : zphiB p q t - zphiA p q t = 4 * t :=
    zphi_B_sub_A p q t
  have hpos : 0 < zphiA p q t ∧ 0 < zphiB p q t :=
    zphi_pellian_factors_pos p q t hq h
  have hqpos : 0 < q := by omega
  have hq_odd : Odd q := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    exact hqodd
  have hA_odd : Odd (zphiA p q t) := by
    have h2p_even : Even (2 * p ^ 2) := ⟨p ^ 2, by ring⟩
    have h2t_even : Even (2 * t) := ⟨t, by ring⟩
    have hq2_odd : Odd (q ^ 2) := hq_odd.pow
    have hsum_odd : Odd (q ^ 2 + 2 * p ^ 2) := hq2_odd.add_even h2p_even
    have hsum_odd' : Odd (2 * p ^ 2 + q ^ 2) := by
      simpa [add_comm] using hsum_odd
    simpa [zphiA] using hsum_odd'.sub_even h2t_even
  have hcopAB_gcd : Int.gcd (zphiA p q t) (zphiB p q t) = 1 := by
    by_contra H
    obtain ⟨ℓ, hℓprime, hℓA, hℓB⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
    rw [← Int.natCast_dvd] at hℓA hℓB
    have hℓ_ne_two : ℓ ≠ 2 := by
      intro hℓ2eq
      have h2A : (2 : ℤ) ∣ zphiA p q t := by
        simpa [hℓ2eq] using hℓA
      exact (show ¬ (2 : ℤ) ∣ zphiA p q t from by
        simpa [← even_iff_two_dvd, Int.not_even_iff_odd] using hA_odd) h2A
    have hℓq : (ℓ : ℤ) ∣ q := by
      by_cases hℓeq5 : ℓ = 5
      · have h25AB : (25 : ℤ) ∣ zphiA p q t * zphiB p q t := by
          have hmul := mul_dvd_mul hℓA hℓB
          simpa [hℓeq5] using hmul
        have h25rhs : (25 : ℤ) ∣ 5 * q ^ 4 := by
          simpa [hAB] using h25AB
        have h5q4 : (5 : ℤ) ∣ q ^ 4 := by
          rcases h25rhs with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          nlinarith
        simpa [hℓeq5] using
          (Int.Prime.dvd_pow' (p := 5) (k := 4) Nat.prime_five h5q4)
      · have hℓprod : (ℓ : ℤ) ∣ 5 * q ^ 4 := by
          rw [← hAB]
          exact dvd_mul_of_dvd_left hℓA (zphiB p q t)
        rcases Int.Prime.dvd_mul' (p := ℓ) hℓprime hℓprod with hℓ5 | hℓq4
        · have hℓ5nat : ℓ ∣ 5 := Int.natCast_dvd.mp hℓ5
          have hle : ℓ ≤ 5 := Nat.le_of_dvd (by norm_num) hℓ5nat
          have hℓeq5' : ℓ = 5 := by
            have hposℓ : 0 < ℓ := hℓprime.pos
            interval_cases ℓ
            · norm_num at hℓprime
            · norm_num at hℓ5nat
            · norm_num at hℓ5nat
            · norm_num at hℓprime
            · rfl
          exact False.elim (hℓeq5 hℓeq5')
        · exact Int.Prime.dvd_pow' (p := ℓ) (k := 4) hℓprime hℓq4
    have hℓsum : (ℓ : ℤ) ∣ zphiA p q t + zphiB p q t := dvd_add hℓA hℓB
    have hℓsum' : (ℓ : ℤ) ∣ 2 * (2 * p ^ 2 + q ^ 2) := by
      simpa [hsum] using hℓsum
    have hℓinner : (ℓ : ℤ) ∣ 2 * p ^ 2 + q ^ 2 := by
      rcases Int.Prime.dvd_mul' (p := ℓ) hℓprime hℓsum' with hℓ2 | hℓinner
      · have hℓ2nat : ℓ ∣ 2 := Int.natCast_dvd.mp hℓ2
        have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓ2nat
        exact False.elim (hℓ_ne_two (le_antisymm hle hℓprime.two_le))
      · exact hℓinner
    have hℓq2 : (ℓ : ℤ) ∣ q ^ 2 := dvd_pow hℓq (by norm_num : (2 : ℕ) ≠ 0)
    have hℓ2p2 : (ℓ : ℤ) ∣ 2 * p ^ 2 := by
      have htmp : (ℓ : ℤ) ∣ (2 * p ^ 2 + q ^ 2) - q ^ 2 := dvd_sub hℓinner hℓq2
      convert htmp using 1
      ring
    have hℓp2 : (ℓ : ℤ) ∣ p ^ 2 := by
      rcases Int.Prime.dvd_mul' (p := ℓ) hℓprime hℓ2p2 with hℓ2 | hℓp2
      · have hℓ2nat : ℓ ∣ 2 := Int.natCast_dvd.mp hℓ2
        have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓ2nat
        exact False.elim (hℓ_ne_two (le_antisymm hle hℓprime.two_le))
      · exact hℓp2
    have hℓp : (ℓ : ℤ) ∣ p :=
      Int.Prime.dvd_pow' (p := ℓ) (k := 2) hℓprime hℓp2
    apply hℓprime.not_dvd_one
    rw [← hcop, Int.gcd_def]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp hℓp) (Int.natCast_dvd.mp hℓq)
  have hcopAB : IsCoprime (zphiA p q t) (zphiB p q t) :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcopAB_gcd
  have h5prod : (5 : ℤ) ∣ zphiA p q t * zphiB p q t := by
    rw [hAB]
    exact dvd_mul_of_dvd_left (dvd_refl (5 : ℤ)) (q ^ 4)
  rcases Int.Prime.dvd_mul' (p := 5) Nat.prime_five h5prod with h5A | h5B
  · obtain ⟨m, n, hA5, hB4, hmn, hmpos, hnpos⟩ :=
      coprime_fourth_power_factor (zphiA p q t) (zphiB p q t) q hAB
        hcopAB hpos.1 hpos.2 hqpos h5A
    have hqmn : q = m * n := hmn.symm
    have hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4 :=
      coeff_identity_left5 p q t m n hsum hqmn hA5 hB4
    exact pythagorean_square_leg_self_descent_left5 p q t m n hq hcop
      (by omega) (by omega) hqmn hcoeff
  · obtain ⟨u, v, hB5, hA4, huv, hupos, hvpos⟩ :=
      coprime_fourth_power_factor (zphiB p q t) (zphiA p q t) q
        (by simpa [mul_comm] using hAB) hcopAB.symm hpos.2 hpos.1 hqpos h5B
    have hqvu : q = v * u := by
      rw [← huv]
      ring
    have hcoeff : 4 * p ^ 2 = (v ^ 2 - u ^ 2) ^ 2 + 4 * u ^ 4 :=
      coeff_identity_right5 p q t v u hsum hqvu hA4 hB5
    exact pythagorean_square_leg_self_descent_right5 p q t v u hq hcop
      (by omega) (by omega) hqvu hcoeff

private theorem even_square_leg_descent_core
    (p q _t m n : ℤ)
    (_hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = 2 * (m * n))
    (hcoeff : p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
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
  let r : ℤ := n ^ 2 - m ^ 2
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
    coprime_product_eq_fourth_power X Y m hXpos hYpos hm_pos hcopXY hXY
  have hpc : P - r = 2 * c ^ 4 := by rw [hXdef, hXc]
  have hpd : P + r = 2 * d ^ 4 := by rw [hYdef, hYd]
  have hn_sq_from_split : n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 := by
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
    · have hm_eq_one : m = 1 := by
        rw [← hcd, hc_eq_one, hd_eq_one]
        norm_num
      have hn_sq_eq_one : n ^ 2 = 1 := by
        simpa [hc_eq_one, hd_eq_one] using hn_sq_from_split
      have hn_eq_one : n = 1 := by
        have hn_nonneg : 0 ≤ n := by omega
        nlinarith [sq_nonneg (n - 1), sq_nonneg (n + 1)]
      have hp2sq : (2 : ℤ) ∣ p ^ 2 := by
        rw [hm_eq_one, hn_eq_one] at hcoeff
        use 2
        nlinarith
      have hp2 : (2 : ℤ) ∣ p :=
        Int.Prime.dvd_pow' (p := 2) (k := 2) Nat.prime_two hp2sq
      have hq2 : (2 : ℤ) ∣ q := by
        rw [hqmn]
        exact ⟨m * n, by ring⟩
      have h2gcd : (2 : ℤ) ∣ (Int.gcd p q : ℤ) := Int.dvd_coe_gcd hp2 hq2
      rw [hcop] at h2gcd
      norm_num at h2gcd
    · have hd_ge_two : 2 ≤ d := by omega
      have hn_sq_expr : n ^ 2 = d ^ 4 + d ^ 2 - 1 := by
        rw [hc_eq_one] at hn_sq_from_split
        norm_num at hn_sq_from_split
        exact hn_sq_from_split
      have hd2_gt_one : 1 < d ^ 2 := by nlinarith [hd_ge_two, sq_nonneg (d - 2)]
      have hlow : d ^ 4 < n ^ 2 := by nlinarith [hn_sq_expr, hd2_gt_one]
      have hhigh : n ^ 2 < (d ^ 2 + 1) ^ 2 := by nlinarith [hn_sq_expr, sq_nonneg d]
      have h_abs_gt : d ^ 2 < |n| := by
        have hs : (d ^ 2) ^ 2 < |n| ^ 2 := by
          rw [sq_abs]
          nlinarith
        exact (sq_lt_sq₀ (sq_nonneg d) (abs_nonneg n)).mp hs
      have h_abs_lt : |n| < d ^ 2 + 1 := by
        have hnonneg : 0 ≤ d ^ 2 + 1 := by nlinarith [sq_nonneg d]
        have hs : |n| ^ 2 < (d ^ 2 + 1) ^ 2 := by
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
  · exact hn_sq_from_split
  · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) hc_lt_q

/-- Even `q` core.

Mathematical content intended here:
extract the exact 2-adic content of the equation, divide to a primitive odd
case or construct a smaller denominator directly. -/
theorem zphi_descent_step_even_core
    (p q t : ℤ)
    (hq : 2 ≤ q)
    (hqeven : (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
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
    have hrhs_odd : Odd (p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :=
      (hp4_odd.add_even hp2q2_even).sub_even hq4_even
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
  · have hAB : zphiA p q t * zphiB p q t = 5 * q ^ 4 :=
      zphi_AB_eq_5q4 p q t h
    have hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2) :=
      zphi_A_add_B p q t
    have hdiff : zphiB p q t - zphiA p q t = 4 * t :=
      zphi_B_sub_A p q t
    have hpos : 0 < zphiA p q t ∧ 0 < zphiB p q t :=
      zphi_pellian_factors_pos p q t hq h
    have hspos : 0 < s := by omega
    have hp2_odd : Odd (p ^ 2) := hp_odd.pow
    have h2s2_even : Even (2 * s ^ 2) := ⟨s ^ 2, by ring⟩
    have hinnerA_even : Even (p ^ 2 + 2 * s ^ 2 - t) := by
      have hpt : Even (p ^ 2 - t) := hp2_odd.sub_odd ht_odd
      rcases hpt with ⟨u, hu⟩
      rcases h2s2_even with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      nlinarith
    have hinnerB_even : Even (p ^ 2 + 2 * s ^ 2 + t) := by
      have hpt : Even (p ^ 2 + t) := hp2_odd.add_odd ht_odd
      rcases hpt with ⟨u, hu⟩
      rcases h2s2_even with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      nlinarith
    rcases hinnerA_even with ⟨A1, hAinner⟩
    rcases hinnerB_even with ⟨B1, hBinner⟩
    have hAeq : zphiA p q t = 4 * A1 := by
      dsimp [zphiA]
      rw [hqeq']
      nlinarith
    have hBeq : zphiB p q t = 4 * B1 := by
      dsimp [zphiB]
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
    have hA1sum : A1 + B1 = p ^ 2 + 2 * s ^ 2 := by
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
      have hℓsum' : (ℓ : ℤ) ∣ p ^ 2 + 2 * s ^ 2 := by
        rwa [hA1sum] at hℓsum
      have hℓs2 : (ℓ : ℤ) ∣ s ^ 2 := dvd_pow hℓs (by norm_num : (2 : ℕ) ≠ 0)
      have hℓ2s2 : (ℓ : ℤ) ∣ 2 * s ^ 2 := dvd_mul_of_dvd_right hℓs2 2
      have hℓp2 : (ℓ : ℤ) ∣ p ^ 2 := by
        have htmp : (ℓ : ℤ) ∣ (p ^ 2 + 2 * s ^ 2) - 2 * s ^ 2 :=
          dvd_sub hℓsum' hℓ2s2
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
        coprime_fourth_power_factor A1 B1 s hA1B1 hcopA1B1 hA1pos hB1pos hspos h5A
      have hcoeff : p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4 := by
        have hsum' : 5 * m ^ 4 + n ^ 4 = p ^ 2 + 2 * (m * n) ^ 2 := by
          calc
            5 * m ^ 4 + n ^ 4 = A1 + B1 := by rw [hA5, hB4]
            _ = p ^ 2 + 2 * s ^ 2 := hA1sum
            _ = p ^ 2 + 2 * (m * n) ^ 2 := by rw [← hmn]
        nlinarith
      have hqmn : q = 2 * (m * n) := by
        rw [hqeq', ← hmn]
      exact even_square_leg_descent_core p q t m n hq hcop (by omega) (by omega) hqmn hcoeff
    · obtain ⟨m, n, hB5, hA4, hmn, hmpos, hnpos⟩ :=
        coprime_fourth_power_factor B1 A1 s (by simpa [mul_comm] using hA1B1)
          hcopA1B1.symm hB1pos hA1pos hspos h5B
      have hcoeff : p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4 := by
        have hsum' : n ^ 4 + 5 * m ^ 4 = p ^ 2 + 2 * (m * n) ^ 2 := by
          calc
            n ^ 4 + 5 * m ^ 4 = A1 + B1 := by rw [hA4, hB5]
            _ = p ^ 2 + 2 * s ^ 2 := hA1sum
            _ = p ^ 2 + 2 * (m * n) ^ 2 := by rw [← hmn]
        nlinarith
      have hqmn : q = 2 * (m * n) := by
        rw [hqeq', ← hmn]
      exact even_square_leg_descent_core p q t m n hq hcop (by omega) (by omega) hqmn hcoeff
  · have hs_odd : Odd s := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      exact hs_even
    have h2s : t ^ 2 = p ^ 4 + p ^ 2 * (2 * s) ^ 2 - (2 * s) ^ 4 := by
      simpa [hqeq'] using h
    exact False.elim (q_two_times_odd_half_contra p s t hp_odd hs_odd h2s)

/-- The hard descent step used by `scratch/DenominatorQuartic.lean`. -/
theorem zphi_descent_step (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  by_cases hqodd : ¬ (2 : ℤ) ∣ q
  · exact zphi_descent_step_odd_core p q t hq hqodd hcop h
  · have hqeven : (2 : ℤ) ∣ q := by
      exact Classical.not_not.mp hqodd
    exact zphi_descent_step_even_core p q t hq hqeven hcop h
