# `u.den = 1` for curve 20.a4: assembly status

I did **not** write a claimed proof of

```lean
theorem rat_den_one_of_curve (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1
```

because the proposed new proof still has two mathematical gaps.  The main one
is in the `p = ±1` step; the new one is in the `p = -1` denominator step.

## Gap 1: the prime-divisor argument does not prove `p = ±1`

With `u = p / q` in lowest terms, clearing denominators gives

```text
w^2 q^3 = p (p^2 + p q - q^2).
```

For a prime `ℓ ∣ p`, one has

```text
p^2 + p q - q^2 ≡ -q^2 [MOD ℓ],
```

and `ℓ ∤ q`, hence `ℓ ∤ (p^2 + p q - q^2)`.  But this only implies the
valuation identity

```text
vℓ(p) = 2 vℓ(w)
```

because `ℓ ∤ q`; it proves the exponent of `ℓ` in `p` is even.  It does not
force `ℓ ∣ 1`, and therefore it does not force `p = ±1`.

## Gap 2: in the `p = -1` case the square lemma applies to `q^3`, not `q`

If `p = -1`, then

```text
w^2 = (q^2 + q - 1) / q^3.
```

Writing `w = a / b` in lowest terms gives

```text
a^2 q^3 = b^2 (q^2 + q - 1),        gcd(q, q^2 + q - 1) = 1.
```

The coprime square-divisibility lemma applied here has `Q = q^3`, so it gives

```text
q^3 = b^2,
```

not `q = b^2`.  Thus the proposed divisibility contradiction

```text
a^2 b^4 = b^4 + b^2 - 1
```

is not available.  Instead `q^3 = b^2` implies `q = d^2`, `b = d^3`, and the
remaining equation is the quartic obstruction

```text
a^2 = d^4 + d^2 - 1.
```

That quartic step is exactly the missing global descent/cover input.

## Complete Lean for the corrected local arithmetic lemma

This is the arithmetic fact that actually follows from the `p = -1` local
calculation.  It has no valuation API and no `sorry`.

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
    exact (hqN.pow_left 3)

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

## What is still needed for the full denominator theorem

A complete proof of `u.den = 1` still needs one of the following strong inputs:

```lean
-- after denominator clearing and coprime splitting:
--   p =  r^2, q = d^2, a^2 = r^2 * (r^4 + r^2*d^2 - d^4)
-- or
--   p = -r^2, q = d^2, a^2 = r^2 * (-r^4 + r^2*d^2 + d^4)
```

and then a no-solution theorem for the resulting quartic cover when `d ≥ 2`.
The local divisibility arguments alone only prove square/cube denominator
structure; they do not prove `q = 1`.
