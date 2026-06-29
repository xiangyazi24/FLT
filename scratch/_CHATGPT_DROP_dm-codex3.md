# Q: FLT Lean N12 two-adic companion

This is the 2-adic companion layer for `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, in the existing namespace:

```lean
namespace MazurProof.RationalPointsN12
```

It is intentionally different from the odd-prime splitting layer.  For odd primes, a prime-power contribution to `B^2` lands in exactly one of `C - z^3` or `C + z^3`.  For `p = 2`, the opposite happens: under `(2 : ℤ) ∣ B`, `Int.gcd C B = 1`, and `Int.gcd z B = 1`, both `C` and `z` are odd, so both signs are even.

## Drop-in Lean code

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- If `2 ∣ B` and `gcd x B = 1`, then `x` is not divisible by `2`. -/
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

/-- Convenience version for `C` and `z` in the denominator residual context. -/
theorem square_denominator_two_not_dvd_C_and_z
    (B C z : ℤ)
    (h2B : (2 : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hcopz : Int.gcd z B = 1) :
    ¬ (2 : ℤ) ∣ C ∧ ¬ (2 : ℤ) ∣ z := by
  exact
    ⟨square_denominator_two_not_dvd_of_gcd (x := C) (B := B) h2B hcopC,
      square_denominator_two_not_dvd_of_gcd (x := z) (B := B) h2B hcopz⟩

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
The usual denominator-residual version: if `2 ∣ B` and both `C` and `z` are
coprime to `B`, then `2` divides both signs.
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

/-- If `4 ∣ 2*x`, then `2 ∣ x`. -/
private theorem two_dvd_of_four_dvd_two_mul {x : ℤ}
    (h : (4 : ℤ) ∣ 2 * x) :
    (2 : ℤ) ∣ x := by
  rcases h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  nlinarith

/--
For odd `C`, both signs cannot be divisible by `4`.
This proves the safe 2-adic bound: the shared 2-adic factor is exactly one
factor of `2`, but this says nothing about odd common factors.
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

## Audit of `Int.gcd (C - z^3) (C + z^3) = 2`

The statement

```lean
Int.gcd (C - z ^ 3) (C + z ^ 3) = 2
```

is **false from only `Odd C` and `Odd z`**.  It is also false from only the denominator-context hypotheses `(2 : ℤ) ∣ B`, `Int.gcd C B = 1`, and `Int.gcd z B = 1`.  Those hypotheses control common factors with `B`; they do not prevent `C` and `z` from sharing an odd factor away from `B`.

A small Lean counterexample shape:

```lean
import Mathlib

example :
    Odd (3 : ℤ) ∧
      Odd (3 : ℤ) ∧
        Int.gcd ((3 : ℤ) - (3 : ℤ) ^ 3)
          ((3 : ℤ) + (3 : ℤ) ^ 3) = 6 := by
  norm_num
```

Here `C = 3`, `z = 3`, so the two factors are `-24` and `30`, whose integer gcd is `6`, not `2`.

The correct safe theorem under only oddness is the 2-adic bound already proved above:

```lean
((2 : ℤ) ∣ C - z ^ 3) ∧
((2 : ℤ) ∣ C + z ^ 3) ∧
¬ (((4 : ℤ) ∣ C - z ^ 3) ∧ ((4 : ℤ) ∣ C + z ^ 3))
```

This means exactly one shared factor of `2`, but it does not rule out odd common factors.

## Optional extra hypothesis for the full gcd statement

A plausible correct version of the full gcd theorem requires an extra coprimality hypothesis such as:

```lean
Int.gcd C z = 1
```

or an equivalent condition ruling out odd common factors.  Before proving the full `gcd = 2`, I would add the following odd-prime exclusion lemma.  It is useful and much smaller than the final gcd theorem.

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

Then the full gcd statement can be staged as a later theorem:

```lean
/-- Later theorem, with the needed extra hypothesis. -/
theorem gcd_z_cube_factors_eq_two_of_odd_and_gcd_C_z
    (C z : ℤ)
    (hCodd : Odd C)
    (hzodd : Odd z)
    (hcopCz : Int.gcd C z = 1) :
    Int.gcd (C - z ^ 3) (C + z ^ 3) = 2 := by
  -- Suggested proof route:
  -- * use `Int.gcd_greatest` with `d = 2`;
  -- * use `square_denominator_two_dvd_both_z_cube_factors_of_odd` for `2 ∣` both signs;
  -- * use `square_denominator_not_four_dvd_both_z_cube_factors_of_odd` to bound the 2-part;
  -- * use `square_denominator_odd_prime_not_common_z_cube_factors_of_gcd_C_z` to rule out odd primes;
  -- * finish with a small integer divisor classification lemma: if every odd prime is excluded
  --   and `4` is excluded, then any common divisor divides `2`.
  -- I would not put this theorem in the critical path unless it is really needed.
  sorry
```

## Mathlib API and tactic checklist

Useful parity APIs over `ℤ`:

```lean
#check Int.even_iff
#check Int.not_even_iff_odd
#check even_iff_two_dvd
#check Even.two_dvd
#check Odd.pow
#check Odd.sub_odd
#check Odd.add_odd
#check Int.odd_pow
#check Int.even_sub
#check Int.even_add
```

Useful divisibility and prime APIs matching the existing style:

```lean
#check Int.dvd_coe_gcd
#check Int.prime_two
#check Int.prime_iff_natAbs_prime
#check Prime.dvd_or_dvd
#check Prime.dvd_of_dvd_pow
```

Recommended tactics:

```lean
norm_num   -- small divisibility contradictions, e.g. `¬ (2 : ℤ) ∣ (1 : ℤ)`
ring       -- after `convert ... using 1` for sums/differences of signs
nlinarith  -- for `4 ∣ 2*x → 2 ∣ x`
omega      -- for integer order side conditions elsewhere in the file
```

The safe 2-adic companion output to use next to the odd-prime splitting is:

```lean
(2 : ℤ) ∣ C - z ^ 3
(2 : ℤ) ∣ C + z ^ 3
¬ (((4 : ℤ) ∣ C - z ^ 3) ∧ ((4 : ℤ) ∣ C + z ^ 3))
```

under `(2 : ℤ) ∣ B`, `Int.gcd C B = 1`, and `Int.gcd z B = 1`.