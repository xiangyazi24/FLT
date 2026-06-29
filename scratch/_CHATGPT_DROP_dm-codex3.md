# Q2198 Lean drop: 2-adic companion layer for the N=12 denominator residual

This is the companion layer to the odd-prime sign splitting in
`FLT/Assumptions/MazurProof/RationalPointsN12.lean`.

Namespace expected by the file:

```lean
namespace MazurProof.RationalPointsN12
```

The key audit point is that the prime `2` behaves differently from odd primes.  If `(2 : ℤ) ∣ B`, then `gcd C B = 1` and `gcd z B = 1` force `C` and `z` odd, and therefore **both**

```lean
C - z ^ 3
C + z ^ 3
```

are divisible by `2`.  Thus the odd-prime statement “exactly one sign receives the local contribution” must not be extended to `p = 2`.

## Drop-in parity layer

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- If `2 ∣ B` and `gcd x B = 1`, then `x` is not even. -/
theorem square_denominator_two_not_dvd_of_gcd
    {x B : ℤ}
    (h2B : (2 : ℤ) ∣ B)
    (hxB : Int.gcd x B = 1) :
    ¬ (2 : ℤ) ∣ x := by
  intro h2x
  have h2gcd : (2 : ℤ) ∣ ((Int.gcd x B : ℕ) : ℤ) := by
    exact Int.dvd_coe_gcd h2x h2B
  have h2one : (2 : ℤ) ∣ (1 : ℤ) := by
    simpa [hxB] using h2gcd
  exact (by norm_num : ¬ (2 : ℤ) ∣ (1 : ℤ)) h2one

/-- Integer parity bridge: not divisible by `2` implies `Odd`. -/
private theorem int_odd_of_not_two_dvd {x : ℤ}
    (hx : ¬ (2 : ℤ) ∣ x) :
    Odd x := by
  exact Int.not_even_iff_odd.mp (by
    intro hxEven
    exact hx (Even.two_dvd hxEven))

/-- Integer parity bridge: `Odd` implies not divisible by `2`. -/
private theorem int_not_two_dvd_of_odd {x : ℤ}
    (hx : Odd x) :
    ¬ (2 : ℤ) ∣ x := by
  intro h2x
  have hxEven : Even x := even_iff_two_dvd.mpr h2x
  exact (Int.not_even_iff_odd.mpr hx) hxEven

/-- The two gcd hypotheses separately force `C` and `z` to be odd modulo `2`. -/
theorem square_denominator_two_not_dvd_C_and_z
    (B C z : ℤ)
    (h2B : (2 : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hcopz : Int.gcd z B = 1) :
    ¬ (2 : ℤ) ∣ C ∧ ¬ (2 : ℤ) ∣ z := by
  exact
    ⟨square_denominator_two_not_dvd_of_gcd (x := C) (B := B) h2B hcopC,
      square_denominator_two_not_dvd_of_gcd (x := z) (B := B) h2B hcopz⟩

/-- If `C` and `z` are odd, then both `C - z^3` and `C + z^3` are even. -/
theorem square_denominator_two_dvd_both_z_cube_factors_of_odd
    (C z : ℤ)
    (hCodd : Odd C)
    (hzodd : Odd z) :
    ((2 : ℤ) ∣ C - z ^ 3) ∧ ((2 : ℤ) ∣ C + z ^ 3) := by
  have hz3odd : Odd (z ^ 3) := hzodd.pow
  exact
    ⟨Even.two_dvd (hCodd.sub_odd hz3odd),
      Even.two_dvd (hCodd.add_odd hz3odd)⟩

/--
The version usually used in the square-denominator residual context.
If `2 ∣ B`, `gcd C B = 1`, and `gcd z B = 1`, then `2` divides both signs.
-/
theorem square_denominator_two_dvd_both_z_cube_factors
    (B C z : ℤ)
    (h2B : (2 : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hcopz : Int.gcd z B = 1) :
    ((2 : ℤ) ∣ C - z ^ 3) ∧ ((2 : ℤ) ∣ C + z ^ 3) := by
  have hnot := square_denominator_two_not_dvd_C_and_z
    (B := B) (C := C) (z := z) h2B hcopC hcopz
  exact square_denominator_two_dvd_both_z_cube_factors_of_odd
    (C := C) (z := z)
    (int_odd_of_not_two_dvd hnot.1)
    (int_odd_of_not_two_dvd hnot.2)

/-- If `4 ∣ 2*x`, then `2 ∣ x`.  Useful for the shared 2-adic factor bound. -/
private theorem two_dvd_of_four_dvd_two_mul {x : ℤ}
    (h : (4 : ℤ) ∣ 2 * x) :
    (2 : ℤ) ∣ x := by
  rcases h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  nlinarith

/--
For odd `C`, both signs cannot be divisible by `4`.
This says that the common 2-adic part of the two signs is exactly one factor of `2`.
It does **not** rule out odd common factors.
-/
theorem square_denominator_not_four_dvd_both_z_cube_factors_of_odd
    (C z : ℤ)
    (hCodd : Odd C) :
    ¬ (((4 : ℤ) ∣ C - z ^ 3) ∧ ((4 : ℤ) ∣ C + z ^ 3)) := by
  intro hboth
  have hsum : (4 : ℤ) ∣ (C - z ^ 3) + (C + z ^ 3) :=
    dvd_add hboth.1 hboth.2
  have h4_2C : (4 : ℤ) ∣ 2 * C := by
    convert hsum using 1
    ring
  have h2C : (2 : ℤ) ∣ C := two_dvd_of_four_dvd_two_mul h4_2C
  exact (int_not_two_dvd_of_odd hCodd) h2C

/--
Bundled 2-adic local statement under the usual denominator hypotheses:
`2` divides both signs, but `4` cannot divide both signs.
-/
theorem square_denominator_two_dvd_both_and_not_four_dvd_both
    (B C z : ℤ)
    (h2B : (2 : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hcopz : Int.gcd z B = 1) :
    ((2 : ℤ) ∣ C - z ^ 3) ∧
      ((2 : ℤ) ∣ C + z ^ 3) ∧
        ¬ (((4 : ℤ) ∣ C - z ^ 3) ∧ ((4 : ℤ) ∣ C + z ^ 3)) := by
  have hnot := square_denominator_two_not_dvd_C_and_z
    (B := B) (C := C) (z := z) h2B hcopC hcopz
  have hCodd : Odd C := int_odd_of_not_two_dvd hnot.1
  have hzodd : Odd z := int_odd_of_not_two_dvd hnot.2
  have htwo := square_denominator_two_dvd_both_z_cube_factors_of_odd
    (C := C) (z := z) hCodd hzodd
  exact ⟨htwo.1, htwo.2,
    square_denominator_not_four_dvd_both_z_cube_factors_of_odd
      (C := C) (z := z) hCodd⟩

end MazurProof.RationalPointsN12
```

## Optional odd-common-factor audit lemma

The statement

```lean
Int.gcd (C - z ^ 3) (C + z ^ 3) = 2
```

is false from only `(2 : ℤ) ∣ B`, `Int.gcd C B = 1`, and `Int.gcd z B = 1`.  The two-adic bound above is the safe statement.  Odd common factors can occur if `C` and `z` share an odd factor not dividing `B`.

Here is a formal counterexample shape:

```lean
import Mathlib

example :
    (2 : ℤ) ∣ (2 : ℤ) ∧
      Int.gcd (3 : ℤ) 2 = 1 ∧
        Int.gcd (3 : ℤ) 2 = 1 ∧
          Int.gcd ((3 : ℤ) - (3 : ℤ) ^ 3) ((3 : ℤ) + (3 : ℤ) ^ 3) = 6 := by
  norm_num
```

If you additionally have `Int.gcd C z = 1`, then odd common prime factors are ruled out.  This is often the right intermediate theorem before attempting a full `gcd = 2` proof.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

private theorem two_adic_odd_nat_prime_int_not_dvd_two {p : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) :
    ¬ (p : ℤ) ∣ (2 : ℤ) := by
  intro hp2
  have hp2nat : p ∣ 2 := by
    exact_mod_cast hp2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2nat with hp1 | hp2'
  · exact hp.ne_one hp1
  · exact hpodd hp2'

/--
With the extra hypothesis `gcd C z = 1`, no odd prime can divide both signs.
This is the odd-part companion to the `not_four_dvd_both` 2-adic bound.
-/
theorem square_denominator_odd_prime_not_common_z_cube_factors_of_gcd_C_z
    (C z : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hcopCz : Int.gcd C z = 1) :
    ¬ (((p : ℤ) ∣ C - z ^ 3) ∧ ((p : ℤ) ∣ C + z ^ 3)) := by
  intro hcommon
  have hpZ : Prime (p : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hpnot2 : ¬ (p : ℤ) ∣ (2 : ℤ) :=
    two_adic_odd_nat_prime_int_not_dvd_two hp hpodd
  have hsum : (p : ℤ) ∣ (C - z ^ 3) + (C + z ^ 3) :=
    dvd_add hcommon.1 hcommon.2
  have h2C : (p : ℤ) ∣ 2 * C := by
    convert hsum using 1
    ring
  have hdiff : (p : ℤ) ∣ (C + z ^ 3) - (C - z ^ 3) :=
    dvd_sub hcommon.2 hcommon.1
  have h2z3 : (p : ℤ) ∣ 2 * z ^ 3 := by
    convert hdiff using 1
    ring
  have hpC : (p : ℤ) ∣ C := by
    rcases hpZ.dvd_or_dvd h2C with hp2 | hpC
    · exact False.elim (hpnot2 hp2)
    · exact hpC
  have hpz3 : (p : ℤ) ∣ z ^ 3 := by
    rcases hpZ.dvd_or_dvd h2z3 with hp2 | hpz3
    · exact False.elim (hpnot2 hp2)
    · exact hpz3
  have hpz : (p : ℤ) ∣ z := hpZ.dvd_of_dvd_pow hpz3
  have hpG : (p : ℤ) ∣ ((Int.gcd C z : ℕ) : ℤ) :=
    Int.dvd_coe_gcd hpC hpz
  have hpOne : (p : ℤ) ∣ (1 : ℤ) := by
    simpa [hcopCz] using hpG
  exact hpZ.not_dvd_one hpOne

end MazurProof.RationalPointsN12
```

A full theorem

```lean
Int.gcd (C - z ^ 3) (C + z ^ 3) = 2
```

should require at least:

```lean
Odd C
Odd z
Int.gcd C z = 1
```

or equivalent hypotheses ruling out odd common divisors.  A reasonable later statement is:

```lean
/-- Optional later theorem; not needed for the immediate 2-adic companion layer. -/
theorem gcd_z_cube_factors_eq_two_of_odd_and_gcd_C_z
    (C z : ℤ)
    (hCodd : Odd C)
    (hzodd : Odd z)
    (hcopCz : Int.gcd C z = 1) :
    Int.gcd (C - z ^ 3) (C + z ^ 3) = 2 := by
  -- Suggested proof route:
  --   * use `Int.gcd_greatest` with `d = 2`;
  --   * lower bound `0 ≤ (2 : ℤ)` is `norm_num`;
  --   * divisibility of `2` into both signs is
  --       `square_denominator_two_dvd_both_z_cube_factors_of_odd`;
  --   * for any common divisor `e`, prove `e ∣ 2` by showing no odd prime
  --     divides it and `4` cannot divide both signs;
  --   * APIs: `Int.gcd_greatest`, `Int.gcd_dvd_left`, `Int.gcd_dvd_right`,
  --     `Int.dvd_coe_gcd`, `Prime.dvd_or_dvd`, `hpZ.dvd_of_dvd_pow`,
  --     `square_denominator_odd_prime_not_common_z_cube_factors_of_gcd_C_z`,
  --     and `square_denominator_not_four_dvd_both_z_cube_factors_of_odd`.
  sorry
```

Do not add this `gcd = 2` theorem under only the denominator hypotheses involving `B`; it is false as shown above.

## API checklist

Useful Mathlib facts for this layer:

```lean
#check Int.dvd_coe_gcd
#check Int.not_even_iff_odd
#check even_iff_two_dvd
#check Even.two_dvd
#check Odd.pow
#check Odd.sub_odd
#check Odd.add_odd
#check Int.prime_two
#check Prime.dvd_or_dvd
#check Prime.dvd_of_dvd_pow
#check Int.prime_iff_natAbs_prime
```

Recommended tactics:

- `norm_num` for `¬ (2 : ℤ) ∣ (1 : ℤ)` and small counterexamples.
- `ring` after `convert ... using 1` for identities like
  `(C - z^3) + (C + z^3) = 2*C`.
- `nlinarith` or `omega` for the small cancellation lemma `4 ∣ 2*x → 2 ∣ x`.
- `Int.dvd_coe_gcd` for converting two divisibility facts into a contradiction with `Int.gcd _ _ = 1`.

The main safe takeaway is:

```lean
(2 : ℤ) ∣ C - z ^ 3
(2 : ℤ) ∣ C + z ^ 3
¬ ((4 : ℤ) ∣ C - z ^ 3 ∧ (4 : ℤ) ∣ C + z ^ 3)
```

under `(2 : ℤ) ∣ B`, `Int.gcd C B = 1`, and `Int.gcd z B = 1`.