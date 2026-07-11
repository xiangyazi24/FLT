import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.Lemmas

/-!
# Auxiliary square-factor balance for the N=12 descent

This file contains the coprime square-factor balance lemma used by the
Euler-style descent route for the N=12 auxiliary obstruction.
-/

namespace MazurProof.RationalPointsN12

/-- If coprime square factors balance against coprime cofactors, the cofactors
are exactly the opposite squares. -/
theorem nat_square_factor_balance
    {b c M N : ℕ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : Nat.Coprime b c)
    (hMN : Nat.Coprime M N)
    (h : b ^ 2 * M = c ^ 2 * N) :
    M = c ^ 2 ∧ N = b ^ 2 := by
  have hcb_sq : Nat.Coprime (c ^ 2) (b ^ 2) := by
    exact (hbc.symm.pow_left 2).pow_right 2
  have hc2_dvd_M : c ^ 2 ∣ M := by
    exact (hcb_sq.dvd_mul_left).mp (by
      rw [h]
      exact dvd_mul_right (c ^ 2) N)
  have hb2_dvd_N : b ^ 2 ∣ N := by
    exact (hcb_sq.symm.dvd_mul_left).mp (by
      rw [← h]
      exact dvd_mul_right (b ^ 2) M)
  rcases hc2_dvd_M with ⟨k, rfl⟩
  rcases hb2_dvd_N with ⟨l, rfl⟩
  have hkl : k = l := by
    have h' : (b ^ 2 * c ^ 2) * k = (b ^ 2 * c ^ 2) * l := by
      calc
        (b ^ 2 * c ^ 2) * k = b ^ 2 * (c ^ 2 * k) := by
          rw [Nat.mul_assoc]
        _ = c ^ 2 * (b ^ 2 * l) := h
        _ = (b ^ 2 * c ^ 2) * l := by
          ac_rfl
    have hbc2_ne : b ^ 2 * c ^ 2 ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hc)
    exact mul_left_cancel₀ hbc2_ne h'
  subst l
  have hk_one : k = 1 := by
    exact Nat.eq_one_of_dvd_coprimes hMN
      (dvd_mul_left k (c ^ 2))
      (dvd_mul_left k (b ^ 2))
  subst k
  simp

/-- Convert integer coprimality to the natural coprimality of absolute values. -/
theorem nat_coprime_natAbs_of_isCoprime_int {a b : ℤ}
    (h : IsCoprime a b) :
    Nat.Coprime a.natAbs b.natAbs :=
  Int.isCoprime_iff_nat_coprime.mp h

/-- A positive integer has nonzero absolute value. -/
theorem natAbs_ne_zero_of_pos {z : ℤ} (hz : 0 < z) :
    z.natAbs ≠ 0 := by
  intro hz0
  exact (ne_of_gt hz) (Int.natAbs_eq_zero.mp hz0)

/-- Taking `natAbs` turns the integer balance equation into the natural one. -/
theorem natAbs_square_balance_eq
    {b c M N : ℤ}
    (h : b ^ 2 * M = c ^ 2 * N) :
    b.natAbs ^ 2 * M.natAbs = c.natAbs ^ 2 * N.natAbs := by
  have h' := congrArg Int.natAbs h
  simpa [Int.natAbs_mul, Int.natAbs_pow] using h'

/-- If a positive integer has absolute value equal to a square absolute value,
then it is that integer square. -/
theorem int_eq_sq_of_pos_of_natAbs_eq_sq_natAbs
    {x y : ℤ}
    (hx : 0 < x)
    (hxy : x.natAbs = y.natAbs ^ 2) :
    x = y ^ 2 := by
  have hxy' : x.natAbs = (y ^ 2).natAbs := by
    simpa [Int.natAbs_pow] using hxy
  exact (Int.natAbs_inj_of_nonneg_of_nonneg
    (le_of_lt hx) (sq_nonneg y)).mp hxy'

/-- Integer square-factor balance with the coprimality hypotheses already in
`natAbs` form. -/
theorem square_factor_balance_int_natAbs
    {b c M N : ℤ}
    (hb : 0 < b) (hc : 0 < c) (hM : 0 < M) (hN : 0 < N)
    (hbc : Nat.Coprime b.natAbs c.natAbs)
    (hMN : Nat.Coprime M.natAbs N.natAbs)
    (h : b ^ 2 * M = c ^ 2 * N) :
    M = c ^ 2 ∧ N = b ^ 2 := by
  have hb0 : b.natAbs ≠ 0 := natAbs_ne_zero_of_pos hb
  have hc0 : c.natAbs ≠ 0 := natAbs_ne_zero_of_pos hc
  have hnat : b.natAbs ^ 2 * M.natAbs = c.natAbs ^ 2 * N.natAbs :=
    natAbs_square_balance_eq h
  rcases nat_square_factor_balance hb0 hc0 hbc hMN hnat with ⟨hMabs, hNabs⟩
  exact ⟨
    int_eq_sq_of_pos_of_natAbs_eq_sq_natAbs hM hMabs,
    int_eq_sq_of_pos_of_natAbs_eq_sq_natAbs hN hNabs⟩

/-- Positive integer square-factor balance in the form used by the N=12
Euler-style descent. -/
theorem square_factor_balance_int
    {b c M N : ℤ}
    (hb : 0 < b) (hc : 0 < c) (hM : 0 < M) (hN : 0 < N)
    (hbc : IsCoprime b c) (hMN : IsCoprime M N)
    (h : b ^ 2 * M = c ^ 2 * N) :
    M = c ^ 2 ∧ N = b ^ 2 := by
  exact square_factor_balance_int_natAbs hb hc hM hN
    (nat_coprime_natAbs_of_isCoprime_int hbc)
    (nat_coprime_natAbs_of_isCoprime_int hMN)
    h

end MazurProof.RationalPointsN12
