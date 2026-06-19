# Final assembly check for `obstruction_curve_20a4_discharge`

I did **not** write a claimed complete Lean proof here, because the proposed
assembly has a real mathematical gap at the `p = ±1` step.  The gap is not a
Lean API issue; it is in the stated argument.

## Blocking point

After writing `u = p / q` in lowest terms, the cleared equation is

```text
w^2 * q^3 = p * (p^2 + p*q - q^2).
```

For a prime `ℓ ∣ p`, coprimality gives `ℓ ∤ q`, and

```text
p^2 + p*q - q^2 ≡ -q^2 [MOD ℓ],
```

so `ℓ ∤ (p^2 + p*q - q^2)`.  However this does **not** imply a contradiction.
It only gives the valuation equation

```text
2 * vℓ(w) = vℓ(p),
```

because `ℓ ∤ q`.  Thus the conclusion is that `vℓ(p)` is even, not that `ℓ`
divides `1`.  In other words, this step can force the squarefree part of `p` to
be trivial, but it does not by itself force `p = ±1`.

So a theorem named something like

```lean
cover_forces_unit
```

must be stronger than the prime-divisor observation.  It needs the full cover or
quartic descent argument, not just the one-line congruence modulo primes
appearing in the requested Step 3.

## Corrected algebra for the `p = -1` denominator step

If the stronger cover step has already given `p = -1`, then for `q ≥ 2` the
curve equation gives

```text
w^2 = (q^2 + q - 1) / q^3.
```

Writing `w = a / b` in lowest terms gives

```text
a^2 * q^3 = b^2 * (q^2 + q - 1),
```

and

```text
gcd(q^3, q^2 + q - 1) = 1.
```

The square-divisibility lemma should therefore be applied with `Q = q^3`, not
with `Q = q`.  Its divisibility proof gives

```text
q^3 = b^2.
```

Then the coprime-exponent lemma gives `q = d^2` and `b = d^3`.  Substituting
back yields

```text
a^2 = d^4 + d^2 - 1,
```

so the quartic obstruction is applied to `d`, with `d ≥ 2` if `q ≥ 4`.

## Lean skeleton once the missing strong cover lemma is available

The final assembly should have this shape:

```lean
import Mathlib

namespace Obstruction20a4

lemma coprime_sq_mul_eq_sq_mul_eq
    {a b q N : ℕ}
    (_hq : 1 ≤ q)
    (hab : Nat.Coprime a b)
    (hqN : Nat.Coprime q N)
    (h : a ^ 2 * q = b ^ 2 * N) :
    q = b ^ 2 := by
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
  exact Nat.dvd_antisymm hq_dvd_bsq hbsq_dvd_q

/-- Needed strong input, not obtained from the prime-divisor congruence alone. -/
-- theorem cover_forces_num_unit ... : u.num = -1 ∨ u.num = 1 := ...

/-- Needed quartic obstruction. -/
-- theorem quartic_20a4_no_nat_ge_two
--     (d : ℕ) (a : ℤ) (hd : 2 ≤ d)
--     (h : a ^ 2 = (d : ℤ) ^ 4 + (d : ℤ) ^ 2 - 1) : False := ...

/-- Once the two inputs above are present, the denominator case split closes. -/
-- theorem obstruction_curve_20a4_discharge (u w : ℚ)
--     (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
--     u = -1 ∨ u = 0 ∨ u = 1 := ...

end Obstruction20a4
```

## What is needed next

The missing Lean target should be the strong cover theorem, for example a lemma
whose conclusion is directly

```lean
u.num = -1 ∨ u.num = 1
```

under the nonzero curve hypotheses, or a homogeneous quartic descent theorem
that proves the same fact.  The prime-divisor congruence alone cannot supply
that conclusion.
