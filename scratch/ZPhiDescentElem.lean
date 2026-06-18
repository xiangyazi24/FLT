import Mathlib

/-!
# Elementary denominator-quartic descent step

This file proves the final `zphi_descent_step` from two explicitly isolated
Pellian/Pythagorean descent sublemmas.  No `Z[φ]` or algebraic number theory is
used in the statement of the step.
-/

namespace DenominatorQuartic

/-- The positive denominator quartic. -/
def PosQuartic (p q t : ℤ) : Prop :=
  t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4

/-- The smaller-solution output used by the descent. -/
def SmallerSolution (p q t p' q' t' : ℤ) : Prop :=
  2 ≤ q' ∧
  Int.gcd p' q' = 1 ∧
  PosQuartic p' q' t' ∧
  q'.natAbs < q.natAbs

private def pellA (p q t : ℤ) : ℤ :=
  2 * p ^ 2 + q ^ 2 - 2 * t

private def pellB (p q t : ℤ) : ℤ :=
  2 * p ^ 2 + q ^ 2 + 2 * t

/-- The Pellian factorization
`(2p²+q²-2t)(2p²+q²+2t)=5q⁴`. -/
private lemma pellian_factorization (p q t : ℤ)
    (h : PosQuartic p q t) :
    pellA p q t * pellB p q t = 5 * q ^ 4 := by
  unfold pellA pellB PosQuartic at *
  calc
    (2 * p ^ 2 + q ^ 2 - 2 * t) * (2 * p ^ 2 + q ^ 2 + 2 * t)
        = (2 * p ^ 2 + q ^ 2) ^ 2 - (2 * t) ^ 2 := by ring
    _ = 5 * q ^ 4 := by nlinarith

private lemma pellian_sum (p q t : ℤ) :
    pellA p q t + pellB p q t = 2 * (2 * p ^ 2 + q ^ 2) := by
  unfold pellA pellB
  ring

private lemma pellian_diff (p q t : ℤ) :
    pellB p q t - pellA p q t = 4 * t := by
  unfold pellA pellB
  ring

/-- Positivity of the Pellian factors.

This is useful for the eventual factor split.  It is not needed by
`zphi_descent_step` below because the two parity sublemmas take the raw factor
identities as hypotheses. -/
private lemma pellian_factors_pos (p q t : ℤ)
    (hq : 2 ≤ q)
    (h : PosQuartic p q t) :
    0 < pellA p q t ∧ 0 < pellB p q t := by
  have hprod := pellian_factorization p q t h
  have hsum := pellian_sum p q t
  have hsum_pos : 0 < pellA p q t + pellB p q t := by
    rw [hsum]
    nlinarith [sq_nonneg p, sq_nonneg q]
  have hprod_pos : 0 < pellA p q t * pellB p q t := by
    rw [hprod]
    positivity
  by_cases hA : 0 < pellA p q t
  · by_cases hB : 0 < pellB p q t
    · exact ⟨hA, hB⟩
    · have hBle : pellB p q t ≤ 0 := by omega
      have hnonpos : pellA p q t * pellB p q t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA) hBle
      nlinarith
  · have hAle : pellA p q t ≤ 0 := by omega
    by_cases hB : 0 < pellB p q t
    · have hnonpos : pellA p q t * pellB p q t ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hAle (le_of_lt hB)
      nlinarith
    · have hBle : pellB p q t ≤ 0 := by omega
      have hsum_nonpos : pellA p q t + pellB p q t ≤ 0 := by omega
      nlinarith

/--
Hard elementary lemma, odd denominator branch.

Mathematical content to fill in:

1. From `q` odd and `gcd(p,q)=1`, prove `p` and `t` are odd.
2. Prove `gcd(A,B)=1`, where
   `A = pellA p q t`, `B = pellB p q t`.
   The prime divisor argument is:
   * an odd common prime divides `A+B = 2(2p²+q²)` and `B-A=4t`;
   * using `AB=5q⁴`, such a prime is either `5` or divides `q`;
   * a divisor of `q` would divide `p`, contradiction;
   * the prime `5` cannot divide both factors because either `5∤q`, making
     `25∤5q⁴`, or `5∣q`, in which case `2p²+q² ≡ 2p² ≠ 0 mod 5`.
3. Since `AB = 5q⁴` and `A,B` are coprime positive integers, one factor is
   `5α⁴` and the other is `β⁴`, with `αβ = q` up to sign.
4. From `A+B = 2(2p²+q²)`, derive

   ```text
   p² = α⁴ + ((β²-α²)/2)²
   ```

   in one orientation, and the analogous equation in the other orientation.
5. Parametrize the primitive Pythagorean triple with square leg and construct a
   new solution of `PosQuartic` with denominator `< q`.
-/
theorem odd_pellian_factor_split_and_descent (p q t : ℤ)
    (hq : 2 ≤ q)
    (hq_odd : ¬ (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (hAB : pellA p q t * pellB p q t = 5 * q ^ 4)
    (hsum : pellA p q t + pellB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hdiff : pellB p q t - pellA p q t = 4 * t)
    (hpos : 0 < pellA p q t ∧ 0 < pellB p q t)
    (hquartic : PosQuartic p q t) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  -- HARD ELEMENTARY SUBLEMMA 1.
  -- This is deliberately not a `Z[φ]` statement; it is the integer factor-split
  -- and Pythagorean square-leg descent described above.
  sorry

/--
Hard elementary lemma, even denominator branch.

Mathematical content to fill in:

1. From `q` even and `gcd(p,q)=1`, prove `p` and `t` are odd.
2. Modulo `16`, exclude `q ≡ 2 mod 4`; hence `4 ∣ q`.
3. Prove both Pellian factors are divisible by `4` and set

   ```text
   A = 4A₁,
   B = 4B₁,
   q = 2r.
   ```

4. Then

   ```text
   A₁B₁ = 5r⁴,
   A₁+B₁ = p² + 2r².
   ```

5. Prove `gcd(A₁,B₁)=1`, split into fourth powers up to the factor `5`, and
   run the same Pythagorean square-leg descent.
-/
theorem even_pellian_factor_split_and_descent (p q t : ℤ)
    (hq : 2 ≤ q)
    (hq_even : (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (hAB : pellA p q t * pellB p q t = 5 * q ^ 4)
    (hsum : pellA p q t + pellB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hdiff : pellB p q t - pellA p q t = 4 * t)
    (hpos : 0 < pellA p q t ∧ 0 < pellB p q t)
    (hquartic : PosQuartic p q t) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  -- HARD ELEMENTARY SUBLEMMA 2.
  -- This is the normalized even-denominator factor split and the same descent.
  sorry

/--
The elementary descent step replacing the earlier `Z[φ]` black box.

This theorem has no algebraic-number-theory content.  It only:

* forms the Pellian factors;
* proves their product/sum/difference identities;
* proves positivity; and
* dispatches to the odd/even elementary factor-split descent lemmas.
-/
theorem zphi_descent_step (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : PosQuartic p q t) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      PosQuartic p' q' t' ∧
      q'.natAbs < q.natAbs := by
  have hAB : pellA p q t * pellB p q t = 5 * q ^ 4 :=
    pellian_factorization p q t h
  have hsum : pellA p q t + pellB p q t = 2 * (2 * p ^ 2 + q ^ 2) :=
    pellian_sum p q t
  have hdiff : pellB p q t - pellA p q t = 4 * t :=
    pellian_diff p q t
  have hpos : 0 < pellA p q t ∧ 0 < pellB p q t :=
    pellian_factors_pos p q t hq h
  by_cases hq_even : (2 : ℤ) ∣ q
  · obtain ⟨p', q', t', hsmall⟩ :=
      even_pellian_factor_split_and_descent p q t
        hq hq_even hcop hAB hsum hdiff hpos h
    exact ⟨p', q', t', hsmall⟩
  · obtain ⟨p', q', t', hsmall⟩ :=
      odd_pellian_factor_split_and_descent p q t
        hq hq_even hcop hAB hsum hdiff hpos h
    exact ⟨p', q', t', hsmall⟩

/-- Strong-induction core using the elementary descent step. -/
private theorem no_denominator_quartic_aux (n : ℕ) :
    ∀ p q t : ℤ,
      q.natAbs ≤ n →
      2 ≤ q →
      Int.gcd p q = 1 →
      PosQuartic p q t →
      False := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p q t hqn hq hcop hquartic
      obtain ⟨p', q', t', hq', hcop', hquartic', hdrop⟩ :=
        zphi_descent_step p q t hq hcop hquartic
      exact ih q'.natAbs (by omega) p' q' t' le_rfl hq' hcop' hquartic'

/-- The positive denominator-quartic no-solution theorem. -/
theorem no_denominator_quartic (p q t : ℤ) (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1) :
    t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4 → False := by
  intro h
  exact no_denominator_quartic_aux q.natAbs p q t le_rfl hq hcop h

end DenominatorQuartic
