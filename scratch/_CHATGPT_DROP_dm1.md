# `zphi_descent_step`: structured Lean reduction

I read `scratch/DenominatorQuartic.lean` on `ai-scratch`.  The exact target there is the top-level axiom:

```lean
axiom zphi_descent_step (p q t : ℤ) (hq : 2 ≤ q) (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    ∃ p' q' t' : ℤ, 2 ≤ q' ∧ Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧ q'.natAbs < q.natAbs
```

The file comments say this theorem packages the `ℤ[φ]` UFD/class-number-one step, coprimality of conjugate factors, coefficient comparison, and the Pythagorean square-leg descent.  The following Lean block gives the sound proof structure matching that signature: it proves the Pellian identities and the final case wrapper, and isolates the genuinely hard odd/even descent cores as named obligations.

I am not pretending that the core descent is routine gcd work.  The odd case still needs two nontrivial formal packages: a coprime factor split for `A * B = 5*q^4`, and the Pythagorean/self-descent producing the smaller denominator.  The even case is analogous after extracting the 2-adic content.

```lean
import Mathlib

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

/-- Even `q` core.

Mathematical content intended here:
extract the exact 2-adic content of the equation, divide to a primitive odd
case or construct a smaller denominator directly. -/
private lemma zphi_descent_step_even_core
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
  -- The even case is analogous but requires a 2-adic normalization before
  -- the coprime factor split.
  sorry

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
```

## What remains to make this a genuine replacement for the axiom

The wrapper above has the right theorem statement and case structure, and the Pellian algebra is formalized.  The remaining obligations are exactly the ones the comments in `DenominatorQuartic.lean` identify as hard:

1. odd `q`: prove the coprime split of `A*B=5*q^4`, compare coefficients, and run the Pythagorean square-leg descent;
2. even `q`: do the corresponding 2-adic normalization and then descend.

I did not mark these as “routine coprimality sublemmas” because they are not routine; they are the core descent content.  The two `sorry`s above are therefore honest placeholders for the hard odd/even cores rather than a fake completed proof.
