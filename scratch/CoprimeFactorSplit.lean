import Mathlib

/-!
# Coprime factors of `5*q^4`

The only non-elementary input is the UFD/factorization fact that coprime
positive factors of a fourth power are themselves fourth powers.
-/

namespace Scratch.ChatGPTDropDM1

/--
UFD / prime-factorization input over `ℤ`.

If two positive coprime integers multiply to a positive fourth power, then each
factor is a fourth power, with compatible positive roots.
-/
theorem coprime_product_eq_fourth_power
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

/--
If `A` and `B` are coprime positive integers, `5 ∣ A`, and
`A * B = 5 * q^4` with `q > 0`, then `A = 5*m^4`, `B = n^4`, and `m*n=q`.
-/
theorem coprime_fourth_power_factor
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

end Scratch.ChatGPTDropDM1
