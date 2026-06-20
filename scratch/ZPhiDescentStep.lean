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
  -- The remaining proof is the actual odd-denominator descent described above.
  -- It should consume `hAB`, `hsum`, `hdiff`, `hqodd`, and `hcop`.
  sorry

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
