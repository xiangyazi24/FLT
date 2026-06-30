# Q2326 Lean drop: QuarticA odd-odd RS data from primitive divided triple

Code-first answer for `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, namespace:

```lean
namespace MazurProof.RationalPointsN12
```

Main point: use Mathlib’s primed Pythagorean classification on the **swapped** divided triple.

Given

```lean
htrip : PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2)
hcop  : Int.gcd (Z / 2) (v ^ 2) = 1
hvodd : Odd v
```

use

```lean
PythagoreanTriple.coprime_classification' htrip.symm ...
```

with first leg `v ^ 2`, because `v ^ 2` is odd.  This directly returns

```lean
v ^ 2 = r ^ 2 - s ^ 2
Z / 2 = 2 * r * s
(u ^ 2 + v ^ 2) / 2 = r ^ 2 + s ^ 2
Int.gcd r s = 1
opposite parity for r,s
```

so no manual branch split is needed.

## Drop-in code

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Odd `u,v` imply `2 ∣ u^2 + v^2`. -/
private theorem quarticA_odd_odd_two_dvd_sum_sq
    {u v : ℤ} (huodd : Odd u) (hvodd : Odd v) :
    (2 : ℤ) ∣ u ^ 2 + v ^ 2 := by
  exact Even.two_dvd ((huodd.pow).add_odd hvodd.pow)

/-- If `p` is an odd natural prime, then `(p : ℤ)` does not divide `2`. -/
private theorem quarticA_nat_prime_int_not_dvd_two {p : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) :
    ¬ (p : ℤ) ∣ (2 : ℤ) := by
  intro hp2
  have hp2nat : p ∣ 2 := by
    exact_mod_cast hp2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2nat with hp1 | hp2'
  · exact hp.ne_one hp1
  · exact hpodd hp2'

/--
If `u*v ≠ 0` and `2 ∣ u^2+v^2`, then the half-sum of squares is positive.
This is the positivity input for `PythagoreanTriple.coprime_classification'`.
-/
private theorem quarticA_half_sum_sq_pos_of_mul_ne_zero_of_two_dvd
    {u v : ℤ}
    (huv0 : u * v ≠ 0)
    (h2 : (2 : ℤ) ∣ u ^ 2 + v ^ 2) :
    0 < (u ^ 2 + v ^ 2) / 2 := by
  have hu0 : u ≠ 0 := by
    intro hu
    exact huv0 (by simp [hu])
  have hv0 : v ≠ 0 := by
    intro hv
    exact huv0 (by simp [hv])
  have hsumpos : 0 < u ^ 2 + v ^ 2 := by
    have hu2pos : 0 < u ^ 2 := sq_pos_of_ne_zero hu0
    have hv2nonneg : 0 ≤ v ^ 2 := sq_nonneg v
    nlinarith
  rcases h2 with ⟨k, hk⟩
  have hkpos : 0 < k := by
    have h2kpos : 0 < 2 * k := by
      rw [← hk]
      exact hsumpos
    nlinarith
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  exact hkpos

/--
Opposite parity makes `r+s` odd.  This tiny helper keeps the gcd proof readable.
-/
private theorem odd_add_of_opposite_parity_mod_two
    {r s : ℤ}
    (hpp : (r % 2 = 0 ∧ s % 2 = 1) ∨ (r % 2 = 1 ∧ s % 2 = 0)) :
    Odd (r + s) := by
  rcases hpp with hpp | hpp
  · exact (Int.even_iff.mpr hpp.1).add_odd (Int.odd_iff.mpr hpp.2)
  · exact (Int.odd_iff.mpr hpp.1).add_even (Int.even_iff.mpr hpp.2)

/--
For coprime `r,s` of opposite parity, the two factors `r+s` and `r-s` are coprime.

This is the elementary gcd step needed after Pythagorean classification.
Proof idea: any common prime divisor of `r+s` and `r-s` divides `2*r` and
`2*s`.  If the prime is odd, it divides both `r` and `s`; if it is `2`, it
contradicts that `r+s` is odd.
-/
theorem int_gcd_add_sub_eq_one_of_gcd_eq_one_of_opp_parity
    {r s : ℤ}
    (hcop : Int.gcd r s = 1)
    (hpp : (r % 2 = 0 ∧ s % 2 = 1) ∨ (r % 2 = 1 ∧ s % 2 = 0)) :
    Int.gcd (r + s) (r - s) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hp_add, hp_sub⟩ := Nat.Prime.not_coprime_iff_dvd.mp hne
  rw [← Int.natCast_dvd] at hp_add hp_sub
  by_cases hp2 : p = 2
  · have h2_add : (2 : ℤ) ∣ r + s := by
      simpa [hp2] using hp_add
    have h_add_odd : Odd (r + s) := odd_add_of_opposite_parity_mod_two hpp
    have h_add_even : Even (r + s) := even_iff_two_dvd.mpr h2_add
    exact (Int.not_even_iff_odd.mpr h_add_odd) h_add_even
  · have hpZ : Prime (p : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
    have hp_not_dvd_two : ¬ (p : ℤ) ∣ (2 : ℤ) :=
      quarticA_nat_prime_int_not_dvd_two hp hp2
    have hp_2r : (p : ℤ) ∣ 2 * r := by
      have h := dvd_add hp_add hp_sub
      convert h using 1
      ring
    have hp_2s : (p : ℤ) ∣ 2 * s := by
      have h := dvd_sub hp_add hp_sub
      convert h using 1
      ring
    have hp_r : (p : ℤ) ∣ r := by
      rcases hpZ.dvd_or_dvd hp_2r with hp_two | hp_r
      · exact False.elim (hp_not_dvd_two hp_two)
      · exact hp_r
    have hp_s : (p : ℤ) ∣ s := by
      rcases hpZ.dvd_or_dvd hp_2s with hp_two | hp_s
      · exact False.elim (hp_not_dvd_two hp_two)
      · exact hp_s
    have hp_gcd : (p : ℤ) ∣ ((Int.gcd r s : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hp_r hp_s
    have hp_one : (p : ℤ) ∣ (1 : ℤ) := by
      simpa [hcop] using hp_gcd
    exact hpZ.not_dvd_one hp_one

/--
The promised reduction/proof of `QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem`.

Use the primed Mathlib classification on the swapped triple:
`htrip.symm : PythagoreanTriple (v^2) (Z/2) ((u^2+v^2)/2)`.
The first leg `v^2` is odd, so `coprime_classification'` returns the branch
`v^2 = r^2 - s^2` directly.
-/
theorem quarticA_oddOddRSDataOfPrimitiveDividedTripleTheorem :
    QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem := by
  intro u v Z huv0 huodd hvodd htrip hcop
  have hv2odd : Odd (v ^ 2) := hvodd.pow
  have hv2mod : v ^ 2 % 2 = 1 := Int.odd_iff.mp hv2odd
  have hcop_symm : Int.gcd (v ^ 2) (Z / 2) = 1 := by
    simpa [Int.gcd_comm] using hcop
  have h2sum : (2 : ℤ) ∣ u ^ 2 + v ^ 2 :=
    quarticA_odd_odd_two_dvd_sum_sq huodd hvodd
  have hHpos : 0 < (u ^ 2 + v ^ 2) / 2 :=
    quarticA_half_sum_sq_pos_of_mul_ne_zero_of_two_dvd huv0 h2sum
  obtain ⟨r, s, hv_sq, hZ_half, hH, hrs_coprime, hrs_parity, _hr_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      htrip.symm hcop_symm hv2mod hHpos
  refine ⟨r, s, ?_, hv_sq, hH⟩
  exact int_gcd_add_sub_eq_one_of_gcd_eq_one_of_opp_parity
    hrs_coprime hrs_parity

end MazurProof.RationalPointsN12
```

## Notes on likely local edits

The core Mathlib API is:

```lean
#check PythagoreanTriple.coprime_classification'
-- theorem coprime_classification' {x y z : ℤ} (h : PythagoreanTriple x y z)
--   (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
--   ∃ m n,
--     x = m ^ 2 - n ^ 2 ∧
--       y = 2 * m * n ∧
--         z = m ^ 2 + n ^ 2 ∧
--           Int.gcd m n = 1 ∧
--             (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m
```

The theorem intentionally applies this to `htrip.symm`, so the `x` in the classification is `v ^ 2`, not `Z / 2`.

If the `obtain` line has trouble with implicit arguments, use the fully explicit form:

```lean
  obtain ⟨r, s, hv_sq, hZ_half, hH, hrs_coprime, hrs_parity, _hr_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      (x := v ^ 2)
      (y := Z / 2)
      (z := (u ^ 2 + v ^ 2) / 2)
      htrip.symm hcop_symm hv2mod hHpos
```

If `Nat.Prime.not_coprime_iff_dvd.mp hne` in the add/sub gcd lemma is brittle, the exact same pattern appears in Mathlib’s `PythagoreanTriples.lean`: after a `by_contra` on an `Int.gcd ... = 1` goal, Mathlib uses

```lean
obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h4
rw [← Int.natCast_dvd] at hp1 hp2
```

so the proof above follows the local Mathlib style.

## Why no manual branch selection is needed

The unprimed theorem

```lean
PythagoreanTriple.coprime_classification
```

would return two branches:

```lean
x = m^2 - n^2 ∧ y = 2*m*n
```

or

```lean
x = 2*m*n ∧ y = m^2 - n^2.
```

If you used it with `x = Z/2`, `y = v^2`, you would need to rule out

```lean
v ^ 2 = 2 * m * n
```

because `v^2` is odd.  The primed theorem avoids this: apply it to the symmetric triple with first leg `v^2`, and pass `v^2 % 2 = 1`; it directly returns

```lean
v ^ 2 = r ^ 2 - s ^ 2
Z / 2 = 2 * r * s
```

plus the hypotenuse equality and opposite parity.

## Resulting data

The final theorem gives exactly the data required by your existing definition:

```lean
∃ r s : ℤ,
  Int.gcd (r + s) (r - s) = 1 ∧
  v ^ 2 = r ^ 2 - s ^ 2 ∧
  (u ^ 2 + v ^ 2) / 2 = r ^ 2 + s ^ 2
```

From here the existing wrapper to `quarticA_eisensteinParam_from_oddLegParams` should be the one from Q2316: rewrite

```lean
(r + s) * (r - s) = r ^ 2 - s ^ 2 = v ^ 2
```

by `ring`, and rewrite

```lean
2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2
```

using `Int.ediv_mul_cancel` from `2 ∣ u^2 + v^2`.