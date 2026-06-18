# ChatGPT Drop File (dm2)

## Task

Formalize the Pythagorean square-leg descent step arising from the coefficient equations

```text
p² = a² + b²,
q² = b(2a+b),
```

which come from the `ℤ[φ]` square extraction

```text
p² + φ q² = ε(a+bφ)².
```

The goal is to isolate the elementary descent step:

```text
(p,q,t) solving t² = p⁴ + p²q² - q⁴, q ≥ 2, gcd(p,q)=1
        ↓
(p',q',t') solving the same equation with 2 ≤ q' and q'.natAbs < q.natAbs.
```

Then strong induction on `q.natAbs` proves no such solution exists.

## Key design choice

The Lean statement should not try to prove the `ℤ[φ]` square extraction and the Pythagorean descent in the same theorem.  The clean split is:

1. `zphi_coeff_matching`: from a primitive quartic solution, obtain primitive coefficient data
   ```text
   p² = a² + b²,
   q² = b(2a+b),
   gcd(a,b)=1,
   0 < b,
   0 < 2a+b.
   ```
   This packages the `ℤ[φ]` UFD step.

2. `pythagorean_square_leg_descent_step`: from those coefficient equations, produce a smaller quartic solution.  This packages the factor split of `q² = b(2a+b)` and the primitive Pythagorean triple descent.

3. `quartic_descent_step`: combine the two.

4. `no_denominator_quartic`: strong induction on `q.natAbs`.

The code below has exactly two isolated `sorry`s: one for the `ℤ[φ]` coefficient extraction and one for the Pythagorean square-leg descent.  The induction skeleton itself is complete.

```lean
import Mathlib

/-!
# Denominator quartic: descent skeleton

This file isolates the two genuinely hard ingredients:

1. `zphi_coeff_matching`, the `ℤ[φ]` square-extraction step.
2. `pythagorean_square_leg_descent_step`, the elementary square-leg descent from
   `p² = a²+b²` and `q² = b(2a+b)`.

Once those two steps are available, the final no-solution theorem is a short
strong induction on `q.natAbs`.
-/

namespace DenominatorQuartic

/-- The positive denominator quartic. -/
def PosQuartic (p q t : ℤ) : Prop :=
  t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4

/--
The algebraic-number-theory input from `ℤ[φ]`.

Mathematically this packages:

* factorization of `p⁴+p²q²-q⁴` as `(p²+φq²)(p²+φ̄q²)`,
* coprimality of the two conjugate factors using `gcd(p,q)=1`,
* UFD/class-number-one square extraction in `ℤ[φ]`,
* absorption of the totally positive unit, and
* coefficient comparison after writing the square as `(a+bφ)²`.

The positivity assumptions `0 < b` and `0 < 2*a+b` are harmless normalization
choices: since `q² = b(2a+b)` and `q ≠ 0`, the two factors have the same sign;
changing the square root by a unit/sign lets one choose the positive orientation.
-/
theorem zphi_coeff_matching (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : PosQuartic p q t) :
    ∃ a b : ℤ,
      Int.gcd a b = 1 ∧
      0 < b ∧
      0 < 2 * a + b ∧
      p ^ 2 = a ^ 2 + b ^ 2 ∧
      q ^ 2 = b * (2 * a + b) := by
  -- HARD `ℤ[φ]` / UFD step.
  -- This is the first isolated `sorry` boundary.
  sorry

/--
The elementary Pythagorean square-leg descent step.

Input:

```text
p² = a² + b²,
q² = b(2a+b),
gcd(a,b)=1,
0 < b,
0 < 2a+b.
```

Sketch of the proof eventually replacing this `sorry`:

1. Show `gcd(b, 2a+b)` is either `1` or `2`, using `gcd(a,b)=1`.
2. Split into parity cases.
   * If `gcd(b,2a+b)=1`, then both factors are squares:
     `b = m²`, `2a+b = n²`, and `q = m*n` up to sign.
   * In the even case, the standard normalized split gives the corresponding
     factor of `2`; after dividing by the common `2`, one again obtains square
     factors.
3. Use `p² = a²+b²` as a primitive Pythagorean triple with a square leg.
4. Parametrize the primitive triple and split the square product again.
5. Construct a new solution `(p',q',t')` of the same quartic with
   `2 ≤ q'` and `q'.natAbs < q.natAbs`.

This theorem is deliberately stated as the precise descent output needed by the
strong-induction proof below.
-/
theorem pythagorean_square_leg_descent_step (p q a b : ℤ)
    (hq : 2 ≤ q)
    (hcop_pq : Int.gcd p q = 1)
    (hcop_ab : Int.gcd a b = 1)
    (hb_pos : 0 < b)
    (hc_pos : 0 < 2 * a + b)
    (hp : p ^ 2 = a ^ 2 + b ^ 2)
    (hqeq : q ^ 2 = b * (2 * a + b)) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      PosQuartic p' q' t' ∧
      q'.natAbs < q.natAbs := by
  -- HARD elementary descent step.
  -- This is the second isolated `sorry` boundary.
  sorry

/-- Combine the `ℤ[φ]` coefficient extraction with the elementary descent. -/
theorem quartic_descent_step (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : PosQuartic p q t) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      PosQuartic p' q' t' ∧
      q'.natAbs < q.natAbs := by
  obtain ⟨a, b, hcop_ab, hb_pos, hc_pos, hp, hqeq⟩ :=
    zphi_coeff_matching p q t hq hcop h
  exact pythagorean_square_leg_descent_step p q a b
    hq hcop hcop_ab hb_pos hc_pos hp hqeq

/-- Strong-induction core: no primitive positive-quartic solution with bounded denominator. -/
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
        quartic_descent_step p q t hq hcop hquartic
      exact ih q'.natAbs (by omega) p' q' t' le_rfl hq' hcop' hquartic'

/-- The requested positive denominator-quartic no-solution theorem. -/
theorem no_denominator_quartic (p q t : ℤ) (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1) :
    t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4 → False := by
  intro h
  exact no_denominator_quartic_aux q.natAbs p q t le_rfl hq hcop h

end DenominatorQuartic
```

## What remains inside the second `sorry`

The core mathematical lemma to prove next is a square-factor split for

```text
q² = b(2a+b)
```

under

```text
gcd(a,b)=1,
0 < b,
0 < 2a+b.
```

A useful Lean sublemma boundary is:

```lean
-- Suggested eventual sublemma, not needed by the skeleton above yet.
theorem square_product_nearly_coprime_split
    (a b q : ℤ)
    (hcop : Int.gcd a b = 1)
    (hb_pos : 0 < b)
    (hc_pos : 0 < 2 * a + b)
    (hqeq : q ^ 2 = b * (2 * a + b)) :
    (∃ m n : ℤ,
      b = m ^ 2 ∧
      2 * a + b = n ^ 2 ∧
      q.natAbs = (m * n).natAbs) ∨
    (∃ m n : ℤ,
      b = 2 * m ^ 2 ∧
      2 * a + b = 2 * n ^ 2 ∧
      q.natAbs = (2 * m * n).natAbs) := by
  sorry
```

Then the Pythagorean part can be split further:

```lean
-- Suggested eventual sublemma.
theorem primitive_pythagorean_square_leg_to_smaller_quartic
    (p q a m n : ℤ)
    (hq : 2 ≤ q)
    (hcop_pq : Int.gcd p q = 1)
    (hp : p ^ 2 = a ^ 2 + m ^ 4)
    (ha : 2 * a = n ^ 2 - m ^ 2)
    (hqabs : q.natAbs = (m * n).natAbs) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      PosQuartic p' q' t' ∧
      q'.natAbs < q.natAbs := by
  sorry
```

Those two sublemmas are the precise place where the parity and gcd bookkeeping belongs.  The global infinite-descent structure should remain as in `no_denominator_quartic_aux` above.
