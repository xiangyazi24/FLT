# `sq_of_cube_div_sq`

```lean
import Mathlib

/--
If `b ^ 2` divides `q ^ 3` and the quotient is coprime to `q`, then `q` is a
square.  The proof first shows the quotient is actually `1`, so
`q ^ 3 = b ^ 2`; then it applies the standard coprime-exponent power lemma.
-/
theorem perfect_sq_of_valuation (q b : ℕ) (hq : 2 ≤ q)
    (hdvd : b ^ 2 ∣ q ^ 3)
    (hN_coprime_q : Nat.Coprime (q ^ 3 / b ^ 2) q) :
    IsSquare q := by
  let N : ℕ := q ^ 3 / b ^ 2

  have hN_dvd_q3 : N ∣ q ^ 3 := by
    dsimp [N]
    exact ⟨b ^ 2, (Nat.div_mul_cancel hdvd).symm⟩

  have hN_coprime_q3 : Nat.Coprime N (q ^ 3) := by
    dsimp [N]
    exact
      ((Nat.coprime_pow_right_iff (n := 3) (by norm_num)
        (q ^ 3 / b ^ 2) q).2 hN_coprime_q)

  have hN_one : N = 1 := by
    exact Nat.eq_one_of_dvd_coprimes hN_coprime_q3 dvd_rfl hN_dvd_q3

  have hq3_eq_b2 : q ^ 3 = b ^ 2 := by
    have hmul : N * b ^ 2 = q ^ 3 := by
      dsimp [N]
      exact Nat.div_mul_cancel hdvd
    rw [hN_one, one_mul] at hmul
    exact hmul.symm

  have h32 : Nat.Coprime 3 2 := by
    decide

  obtain ⟨c, hq_eq, _hb_eq⟩ :=
    Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
      (a := q) (b := b) (m := 3) (n := 2) h32 hq3_eq_b2

  refine ⟨c, ?_⟩
  first
  | simpa [pow_two] using hq_eq
  | simpa [pow_two] using hq_eq.symm

/-- Prime-divisibility formulation of `perfect_sq_of_valuation`. -/
theorem sq_of_cube_div_sq (q b : ℕ) (hq : 2 ≤ q) (hb : 0 < b)
    (hdvd : b ^ 2 ∣ q ^ 3)
    (hcop_rhs : ∀ (ℓ : ℕ), Nat.Prime ℓ → ℓ ∣ q → ¬(ℓ ∣ (q ^ 3 / b ^ 2))) :
    IsSquare q := by
  apply perfect_sq_of_valuation q b hq hdvd
  exact Nat.coprime_of_dvd' (by
    intro ℓ hℓ hℓN hℓq
    exact False.elim ((hcop_rhs ℓ hℓ hℓq) hℓN))
```
