# Q2629: audited Nat square-splitting lemmas

Target: compact drop-in Lean for the four Nat lemmas.

API audit notes:

* `Nat.pow_left_injective` is not the right name to rely on here. For fixed nonzero exponent/root injectivity, use `Nat.pow_left_inj`, for example `(Nat.pow_left_inj (by norm_num : (2 : ℕ) ≠ 0)).mp h`; the root-namespace theorem `pow_left_inj (M := ℕ)` is also available from the torsion-free API. The code below avoids this entirely.
* `Nat.coprime_pow_left_iff` and `Nat.coprime_pow_right_iff` do exist, but the first argument is the positive exponent: `Nat.coprime_pow_left_iff (by norm_num : 0 < 2) a b` and similarly on the right. The code below avoids them.
* `hcop.dvd_mul_right` exists, but its receiver must have the divisor as the left coprime argument: `H : Nat.Coprime k n` gives `k ∣ m * n ↔ k ∣ m`. If your hypothesis is oriented differently, use `.symm` first.
* `hmn_coprime.of_dvd_left hdvd` is valid. The explicit form is `Nat.Coprime.of_dvd_left hdvd hmn_coprime`.
* `mul_left_inj'` is the wrong cancellation helper for left multiplication in Nat. Use `Nat.mul_left_cancel (by norm_num : 0 < c)` on `c * lhs = c * rhs`, or rewrite to right multiplication before using a right-cancellation lemma. In the code below, the only cancellation is via `Nat.mul_left_cancel`.

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace Nat

/-- If coprime natural numbers multiply to a square, the left factor is a square.

This proof intentionally goes through `Int.sq_of_gcd_eq_one`; the possible negative-square
branch over `Int` forces the natural number to be zero, hence is still a square. -/
theorem exists_sq_of_coprime_mul_eq_sq_left
    {m n N : ℕ} (hmn_coprime : Nat.Coprime m n)
    (h : m * n = N ^ 2) :
    ∃ a : ℕ, m = a ^ 2 := by
  have hgcd : Int.gcd (m : ℤ) (n : ℤ) = 1 := by
    simpa [Int.gcd_natCast_natCast] using hmn_coprime
  have hInt : (m : ℤ) * (n : ℤ) = (N : ℤ) ^ 2 := by
    exact_mod_cast h
  rcases Int.sq_of_gcd_eq_one hgcd hInt with ⟨a, ha | ha⟩
  · refine ⟨a.natAbs, ?_⟩
    calc
      m = Int.natAbs (m : ℤ) := by simp
      _ = Int.natAbs (a ^ 2) := by rw [ha]
      _ = a.natAbs ^ 2 := by simpa using (Int.natAbs_pow a 2)
  · have hm_nonneg : 0 ≤ (m : ℤ) := by exact_mod_cast (Nat.zero_le m)
    have hm_nonpos : (m : ℤ) ≤ 0 := by
      rw [ha]
      exact neg_nonpos.mpr (sq_nonneg a)
    have hm0_int : (m : ℤ) = 0 := le_antisymm hm_nonpos hm_nonneg
    have hm0 : m = 0 := by exact_mod_cast hm0_int
    exact ⟨0, by simp [hm0]⟩

/-- If coprime natural numbers multiply to a square, both factors are squares. -/
theorem coprime_mul_eq_square_split
    {m n N : ℕ} (hmn_coprime : Nat.Coprime m n)
    (h : m * n = N ^ 2) :
    ∃ a b : ℕ, m = a ^ 2 ∧ n = b ^ 2 := by
  obtain ⟨a, ha⟩ :=
    Nat.exists_sq_of_coprime_mul_eq_sq_left hmn_coprime h
  obtain ⟨b, hb⟩ :=
    Nat.exists_sq_of_coprime_mul_eq_sq_left hmn_coprime.symm
      (by simpa [mul_comm] using h)
  exact ⟨a, b, ha, hb⟩

/-- If `M` is the even member of a coprime product equal to eight times a square,
then `M` is twice a square and the other factor is a square. -/
theorem coprime_product_eq_eight_square_split_even_left
    {M n N : ℕ} (hmn_coprime : Nat.Coprime M n)
    (hM_even : Even M)
    (h : M * n = 8 * N ^ 2) :
    ∃ a b : ℕ, M = 2 * a ^ 2 ∧ n = b ^ 2 := by
  rcases hM_even with ⟨M', hM'⟩
  have hM : M = 2 * M' := by
    simpa [two_mul] using hM'
  have hM'_dvd : M' ∣ M := by
    refine ⟨2, ?_⟩
    simpa [hM, mul_comm]
  have hcop' : Nat.Coprime M' n := hmn_coprime.of_dvd_left hM'_dvd
  have hscaled : (2 * M') * n = 8 * N ^ 2 := by
    simpa [hM] using h
  have hcancel_arg : 2 * (M' * n) = 2 * (4 * N ^ 2) := by
    calc
      2 * (M' * n) = (2 * M') * n := by ring
      _ = 8 * N ^ 2 := hscaled
      _ = 2 * (4 * N ^ 2) := by ring
  have hmn4 : M' * n = 4 * N ^ 2 :=
    Nat.mul_left_cancel (by norm_num : 0 < 2) hcancel_arg
  have hsq : M' * n = (2 * N) ^ 2 := by
    calc
      M' * n = 4 * N ^ 2 := hmn4
      _ = (2 * N) ^ 2 := by ring
  obtain ⟨a, b, ha, hb⟩ := Nat.coprime_mul_eq_square_split hcop' hsq
  exact ⟨a, b, by simpa [hM, ha], hb⟩

/-- If a coprime product is eight times a square, exactly one side carries the odd
factor of two: one side is twice a square and the other side is a square. -/
theorem coprime_product_eq_eight_square_split
    {M n N : ℕ} (hmn_coprime : Nat.Coprime M n)
    (h : M * n = 8 * N ^ 2) :
    (∃ a b : ℕ, M = 2 * a ^ 2 ∧ n = b ^ 2) ∨
      (∃ a b : ℕ, M = a ^ 2 ∧ n = 2 * b ^ 2) := by
  have htwo_dvd_prod : 2 ∣ M * n := by
    rw [h]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 8) (N ^ 2)
  rcases Nat.prime_two.dvd_mul.1 htwo_dvd_prod with hM_two | hn_two
  · left
    exact Nat.coprime_product_eq_eight_square_split_even_left hmn_coprime
      (even_iff_two_dvd.mpr hM_two) h
  · right
    obtain ⟨a, b, ha, hb⟩ :=
      Nat.coprime_product_eq_eight_square_split_even_left hmn_coprime.symm
        (even_iff_two_dvd.mpr hn_two) (by simpa [mul_comm] using h)
    exact ⟨b, a, hb, ha⟩

end Nat
```
