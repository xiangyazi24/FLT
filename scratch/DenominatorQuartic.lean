import Mathlib

/-!
# Denominator quartic via `ℤ[φ]`

This file shows the intended formal shape of the `ℤ[φ]` proof.

The hard algebraic-number-theory and Pythagorean-descent content is isolated in
`zphi_descent_step`.  Once that theorem is proved, the final contradiction is an
ordinary infinite descent on `q.natAbs`.
-/

/-- The one hard theorem produced by the `ℤ[φ]` argument.

Mathematically, this packages:
* the UFD/class-number-one argument in `ℤ[(1+√5)/2]`,
* the proof that `gcd(p²+φq², p²+φ̄q²)` is a unit,
* the reduction `p²+φq² = β²`,
* coefficient comparison `p² = a²+b²`, `q² = b(2a+b)`, and
* the Pythagorean square-leg descent producing a smaller denominator.
-/
axiom zphi_descent_step (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs

private theorem no_denominator_quartic_aux :
    ∀ n : ℕ, ∀ p q t : ℤ,
      q.natAbs ≤ n →
      2 ≤ q →
      Int.gcd p q = 1 →
      t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4 →
      False := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p q t hqn hq hcop h
      obtain ⟨p', q', t', hq', hcop', h', hdrop⟩ :=
        zphi_descent_step p q t hq hcop h
      exact ih q'.natAbs (by omega) p' q' t' le_rfl hq' hcop' h'

theorem no_denominator_quartic (p q t : ℤ) (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1) :
    t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4 → False := by
  intro h
  exact no_denominator_quartic_aux q.natAbs p q t le_rfl hq hcop h
