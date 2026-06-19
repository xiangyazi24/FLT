# Final assembly request for `obstruction_curve_20a4_discharge`

I cannot honestly write the requested 0-sorry Lean proof from the proof chain in
the prompt, because that proof chain still contains a false algebraic step.
This is not a Lean elaboration issue.

Target requested:

```lean
theorem obstruction_curve_20a4_discharge (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1
```

## The blocking error

In the `p = -1` branch, the prompt derives

```text
w^2 = (q^2 + q - 1) / q^3.
```

Writing `w = a / b` in lowest terms gives

```text
a^2 q^3 = b^2 (q^2 + q - 1),        gcd(q, q^2 + q - 1) = 1.
```

The coprime square-divisibility lemma applies to the factor `q^3`, not to `q`.
It therefore gives

```text
q^3 = b^2,
```

not `q = b^2`.  Consequently the later line

```text
a^2 b^2 = b^4 + b^2 - 1
```

or equivalently `(ab)^2 = b^4 + b^2 - 1` does not follow from this equation.
The corrected descent is:

```text
q^3 = b^2  ⇒  q = d^2 and b = d^3,
a^2 = d^4 + d^2 - 1,
```

so the quartic obstruction is still required.

## The other required strong input

The prompt also asks to get `p = ±1` from the prime-divisor congruence.  That
local congruence only proves that prime exponents in `p` are even.  It does not
force `p` to have no prime divisors.  A genuine cover/descent theorem is still
needed for this step.

## Complete Lean for the corrected local arithmetic fact

The following is the no-valuation local lemma that is actually justified by the
`p = -1` equation.  It is the strongest conclusion available from the coprime
square-divisibility step alone.

```lean
import Mathlib

namespace Obstruction20a4Local

lemma coprime_cube_eq_sq_of_sq_mul_cube_eq_sq_mul
    {a b q N : ℕ}
    (hab : Nat.Coprime a b)
    (hqN : Nat.Coprime q N)
    (h : a ^ 2 * q ^ 3 = b ^ 2 * N) :
    q ^ 3 = b ^ 2 := by
  have hq3N : Nat.Coprime (q ^ 3) N := by
    exact hqN.pow_left 3

  have hq3_dvd_bsq : q ^ 3 ∣ b ^ 2 := by
    have hdiv : q ^ 3 ∣ b ^ 2 * N := by
      rw [← h]
      exact Nat.dvd_mul_left (q ^ 3) (a ^ 2)
    exact hq3N.dvd_of_dvd_mul_right hdiv

  have hbsq_dvd_q3 : b ^ 2 ∣ q ^ 3 := by
    have hdiv : b ^ 2 ∣ a ^ 2 * q ^ 3 := by
      rw [h]
      exact Nat.dvd_mul_right (b ^ 2) N
    have hcop : Nat.Coprime (b ^ 2) (a ^ 2) := by
      exact (hab.symm.pow_left 2).pow_right 2
    exact hcop.dvd_of_dvd_mul_left hdiv

  exact Nat.dvd_antisymm hq3_dvd_bsq hbsq_dvd_q3

end Obstruction20a4Local
```

## What a complete final assembly still needs

A valid final proof can be assembled once the file has inline versions of these
strong inputs with their actual Lean statements:

```lean
-- 1. A cover/descent theorem strong enough to turn the cleared equation into
--    the squareclass alternatives for p, not merely even valuations.

-- 2. A quartic obstruction theorem ruling out
--      a^2 = d^4 + d^2 - 1
--    for natural d ≥ 2, and the companion cover needed for the positive p case.
```

Without those strong inputs, a 0-sorry Lean proof of the requested theorem would
be a fabricated proof rather than a formalization of the stated argument.
