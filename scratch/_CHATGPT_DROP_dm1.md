# `coprime_sq_dvd_implies_sq`

```lean
import Mathlib

/--
From `a^2 * q = b^2 * N`, with `(a,b)=1` and `(q,N)=1`, both `q ∣ b^2`
and `b^2 ∣ q`; hence `q = b^2`.
-/
theorem coprime_sq_dvd_implies_sq (q b : ℕ) (a N : ℤ)
    (hq : 2 ≤ q) (hab : Int.gcd a b = 1) (hqN : Nat.Coprime q N.natAbs)
    (heq : a ^ 2 * (q : ℤ) = b ^ 2 * N) : IsSquare q := by
  have hnat : a.natAbs ^ 2 * q = b ^ 2 * N.natAbs := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using congrArg Int.natAbs heq

  have habNat : Nat.Coprime a.natAbs b := by
    rw [Nat.coprime_iff_gcd_eq_one]
    cases a <;> simpa using hab

  have habSq : Nat.Coprime (a.natAbs ^ 2) (b ^ 2) :=
    Nat.Coprime.pow 2 2 habNat

  have hb2_dvd_q : b ^ 2 ∣ q := by
    have hdiv : b ^ 2 ∣ a.natAbs ^ 2 * q := by
      rw [hnat]
      exact dvd_mul_right _ _
    exact
      (Nat.Coprime.dvd_mul_left
        (m := a.natAbs ^ 2) (n := q) (k := b ^ 2) habSq.symm).1 hdiv

  have hq_dvd_b2 : q ∣ b ^ 2 := by
    have hdiv : q ∣ b ^ 2 * N.natAbs := by
      rw [← hnat]
      exact dvd_mul_of_dvd_right dvd_rfl (a.natAbs ^ 2)
    exact
      (Nat.Coprime.dvd_mul_right
        (m := b ^ 2) (n := N.natAbs) (k := q) hqN).1 hdiv

  have hq_eq_b2 : q = b ^ 2 := Nat.dvd_antisymm hq_dvd_b2 hb2_dvd_q

  refine ⟨b, ?_⟩
  first
  | simpa [pow_two] using hq_eq_b2
  | simpa [pow_two] using hq_eq_b2.symm
```
