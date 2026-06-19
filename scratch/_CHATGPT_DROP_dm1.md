# `zphi_descent_step_odd_core`: why the proposed `q' = m` closure is not valid

I read `scratch/ZPhiDescentStep.lean` on `ai-scratch`.  The local context at the odd-core `sorry` is exactly as described:

```lean
h     : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4
hqodd : ¬ (2 : ℤ) ∣ q
hcop  : Int.gcd p q = 1
hAB   : zphiA p q t * zphiB p q t = 5 * q ^ 4
hsum  : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2)
hdiff : zphiB p q t - zphiA p q t = 4 * t
```

I cannot honestly write a `0 sorry` proof of the odd core from the stated next step, because the proposed line

> “Set `r=(n²-m²)/2`. New solution: `q'=m`, derive from the equations.”

is not mathematically justified.  After the split branch

\[
A=5m^4,\qquad B=n^4,\qquad q=mn,
\]

the coefficient comparison gives only

\[
p^2=m^4+\left(\frac{n^2-m^2}{2}\right)^2. \tag{★}
\]

Equation `(★)` is a primitive Pythagorean triangle with one square leg.  It does **not** immediately produce a new solution with denominator `m`.  In fact, `p²=m⁴+r²` alone has nontrivial examples, such as

\[
5^2=2^4+3^2.
\]

So the remaining step is not a routine algebraic derivation from `A=5m⁴`, `B=n⁴`; it requires the Pythagorean parametrization of `(★)`.  The new smaller denominator comes from the factors in that parametrization, not directly from `m`.

## Corrected mathematical descent step

From

\[
p^2=m^4+r^2,\qquad r=\frac{n^2-m^2}{2},
\]

assuming the primitive/parity hypotheses, the Pythagorean parametrization gives coprime integers `a,b` with

\[
m=ab,\qquad r=\frac{a^4-b^4}{2},\qquad p=\frac{a^2+b^2}{2}
\]

(up to swapping/sign conventions).  Equating the two expressions for `r` gives

\[
n^2-m^2=a^4-b^4.
\]

Since `m=ab`, this becomes

\[
n^2=a^4+a^2b^2-b^4.
\]

Thus the smaller solution is

\[
(p',q',t')=(a,b,n)
\]

or the swapped version, with `q'=b`, not `q'=m`.  The strict denominator drop is then `|b| < |abn| = |q|`, after proving `|a|,|n| ≥ 1` and nontriviality.

## Lean code: algebra after the factor split

The following code is the largest part that can be closed by the split plus algebra alone.  It gives the correct coefficient identities and isolates the genuinely missing Pythagorean-parametrization descent package.

```lean
import Mathlib

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

/-- Algebraic coefficient comparison in the branch `A = 5m^4`, `B = n^4`. -/
private lemma coeff_identity_left5
    (p q t m n : ℤ)
    (hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hqmn : q = m * n)
    (hA : zphiA p q t = 5 * m ^ 4)
    (hB : zphiB p q t = n ^ 4) :
    4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4 := by
  have hsum' : 5 * m ^ 4 + n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
    calc
      5 * m ^ 4 + n ^ 4 = zphiA p q t + zphiB p q t := by
        rw [hA, hB]
      _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
      _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
  nlinarith

/-- Algebraic coefficient comparison in the branch `A = m^4`, `B = 5n^4`. -/
private lemma coeff_identity_right5
    (p q t m n : ℤ)
    (hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hqmn : q = m * n)
    (hA : zphiA p q t = m ^ 4)
    (hB : zphiB p q t = 5 * n ^ 4) :
    4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4 := by
  have hsum' : m ^ 4 + 5 * n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
    calc
      m ^ 4 + 5 * n ^ 4 = zphiA p q t + zphiB p q t := by
        rw [hA, hB]
      _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
      _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
  nlinarith

/--
The actual missing descent package after the coefficient identity.

This is not a gcd bookkeeping lemma.  It is the primitive Pythagorean
parametrization plus the self-descent that turns
`4p² = (n²-m²)² + 4m⁴` into a smaller solution of
`t² = p⁴ + p²q² - q⁴`.
-/
private axiom pythagorean_square_leg_self_descent_left5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs

/-- Symmetric missing descent package for the branch `A=m^4`, `B=5n^4`. -/
private axiom pythagorean_square_leg_self_descent_right5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs
```

## Consequence for the requested odd core

Once the already-available `CoprimeFactorSplit.lean` gives the split branches and the two Pythagorean self-descent packages above are proved, the odd core wrapper is short:

```lean
-- Pseudocode wrapper, names depend on the exact theorem in `CoprimeFactorSplit.lean`.
-- private lemma zphi_descent_step_odd_core ... := by
--   have hAB := zphi_AB_eq_5q4 p q t h
--   have hsum := zphi_A_add_B p q t
--   have hdiff := zphi_B_sub_A p q t
--   obtain (⟨m,n,hmpos,hnpos,hqmn,hA,hB⟩ | ⟨m,n,hmpos,hnpos,hqmn,hA,hB⟩) :=
--     coprime_factor_split_for_zphiA_zphiB p q t hq hqodd hcop h hAB hsum hdiff
--   · exact pythagorean_square_leg_self_descent_left5 p q t m n hq hcop hmpos hnpos hqmn
--       (coeff_identity_left5 p q t m n hsum hqmn hA hB)
--   · exact pythagorean_square_leg_self_descent_right5 p q t m n hq hcop hmpos hnpos hqmn
--       (coeff_identity_right5 p q t m n hsum hqmn hA hB)
```

So the coefficient-matching steps 2–3 are fully algebraic and can be closed.  Step 4 is still a substantive Pythagorean infinite descent; the proposed direct choice `q'=m` does not follow from the equations and should not be used as a proof term.
