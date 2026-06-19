# Lean drop: square denominator from coprime square equation

All proofs below are complete.  The natural-number core is the key argument:
from `a^2 * q = b^2 * N`, coprimality gives both `q ∣ b^2` and `b^2 ∣ q`, hence `q = b^2`.

```lean
import Mathlib

namespace ScratchDenominator

/--
Natural-number core.

If `a^2 * q = b^2 * N`, `gcd(a,b)=1`, and `gcd(q,N)=1`, then `q` is a
square.  No valuation or multiplicity argument is used.
-/
lemma nat_isSquare_of_sq_mul_eq_sq_mul
    {a b q N : ℕ}
    (_hq : 2 ≤ q)
    (hab : Nat.Coprime a b)
    (hqN : Nat.Coprime q N)
    (h : a ^ 2 * q = b ^ 2 * N) :
    IsSquare q := by
  have hq_dvd_bsq : q ∣ b ^ 2 := by
    have hq_dvd_rhs : q ∣ b ^ 2 * N := by
      rw [← h]
      exact Nat.dvd_mul_left q (a ^ 2)
    exact hqN.dvd_of_dvd_mul_right hq_dvd_rhs

  have hbsq_dvd_q : b ^ 2 ∣ q := by
    have hbsq_dvd_lhs : b ^ 2 ∣ a ^ 2 * q := by
      rw [h]
      exact Nat.dvd_mul_right (b ^ 2) N
    have hcop_bsq_asq : Nat.Coprime (b ^ 2) (a ^ 2) := by
      exact (hab.symm.pow_left 2).pow_right 2
    exact hcop_bsq_asq.dvd_of_dvd_mul_left hbsq_dvd_lhs

  have hq_eq : q = b ^ 2 := Nat.dvd_antisymm hq_dvd_bsq hbsq_dvd_q
  rw [hq_eq]
  exact ⟨b, by simp [pow_two]⟩

/-- Same lemma, with `Nat.gcd = 1` hypotheses instead of `Nat.Coprime`. -/
lemma nat_isSquare_of_sq_mul_eq_sq_mul_gcd
    {a b q N : ℕ}
    (hq : 2 ≤ q)
    (hab : Nat.gcd a b = 1)
    (hqN : Nat.gcd q N = 1)
    (h : a ^ 2 * q = b ^ 2 * N) :
    IsSquare q := by
  exact nat_isSquare_of_sq_mul_eq_sq_mul
    (a := a) (b := b) (q := q) (N := N)
    hq
    (by simpa [Nat.Coprime] using hab)
    (by simpa [Nat.Coprime] using hqN)
    h

/--
Integer wrapper for a cleared rational equation.

This is the direct form for `a b N : ℤ`, `q : ℕ`:
`a^2 * q = b^2 * N`, with coprimality stated as
`gcd(|a|,|b|)=1` and `gcd(q,|N|)=1`.
-/
lemma int_isSquare_of_sq_mul_eq_sq_mul
    {a b N : ℤ} {q : ℕ}
    (hq : 2 ≤ q)
    (hab : Nat.Coprime a.natAbs b.natAbs)
    (hqN : Nat.Coprime q N.natAbs)
    (h : a ^ 2 * (q : ℤ) = b ^ 2 * N) :
    IsSquare q := by
  have hnat : a.natAbs ^ 2 * q = b.natAbs ^ 2 * N.natAbs := by
    have h' := congrArg Int.natAbs h
    simpa [pow_two, Int.natAbs_mul, Int.natAbs_natCast,
      mul_assoc, mul_left_comm, mul_comm] using h'

  exact nat_isSquare_of_sq_mul_eq_sq_mul
    (a := a.natAbs) (b := b.natAbs) (q := q) (N := N.natAbs)
    hq hab hqN hnat

/-- Integer wrapper with `Nat.gcd = 1` hypotheses. -/
lemma int_isSquare_of_sq_mul_eq_sq_mul_gcd
    {a b N : ℤ} {q : ℕ}
    (hq : 2 ≤ q)
    (hab : Nat.gcd a.natAbs b.natAbs = 1)
    (hqN : Nat.gcd q N.natAbs = 1)
    (h : a ^ 2 * (q : ℤ) = b ^ 2 * N) :
    IsSquare q := by
  exact int_isSquare_of_sq_mul_eq_sq_mul
    (a := a) (b := b) (N := N) (q := q)
    hq
    (by simpa [Nat.Coprime] using hab)
    (by simpa [Nat.Coprime] using hqN)
    h

/--
Variant where the denominator `b` is already a natural number, as for `Rat.den`.
-/
lemma int_natDen_isSquare_of_sq_mul_eq_sq_mul
    {a N : ℤ} {b q : ℕ}
    (hq : 2 ≤ q)
    (hab : Nat.Coprime a.natAbs b)
    (hqN : Nat.Coprime q N.natAbs)
    (h : a ^ 2 * (q : ℤ) = (b : ℤ) ^ 2 * N) :
    IsSquare q := by
  have hnat : a.natAbs ^ 2 * q = b ^ 2 * N.natAbs := by
    have h' := congrArg Int.natAbs h
    simpa [pow_two, Int.natAbs_mul, Int.natAbs_natCast,
      mul_assoc, mul_left_comm, mul_comm] using h'

  exact nat_isSquare_of_sq_mul_eq_sq_mul
    (a := a.natAbs) (b := b) (q := q) (N := N.natAbs)
    hq hab hqN hnat

end ScratchDenominator
```
