# Q2325 (dm-codex2): audit and proof of the odd-odd divided `QuarticA` primitive gcd

## Code

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/--
Integer gcd is `1` if no rational prime divides both integer arguments.
This wrapper keeps the main proof prime-local and avoids reasoning about a
composite common divisor directly.
-/
theorem int_gcd_eq_one_of_no_common_prime {x y : ℤ}
    (hprime : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → (p : ℤ) ∣ y → False) :
    Int.gcd x y = 1 := by
  rw [Int.gcd_def]
  change Nat.Coprime x.natAbs y.natAbs
  rw [Nat.coprime_iff_not_exists_prime_dvd]
  rintro ⟨p, hp, hpx, hpy⟩
  exact hprime p hp
    ((Int.natAbs_dvd_natAbs).mp (by simpa using hpx))
    ((Int.natAbs_dvd_natAbs).mp (by simpa using hpy))

/-- A rational prime dividing an integer square divides the integer. -/
theorem int_natPrime_dvd_of_dvd_sq {p : ℕ} {x : ℤ}
    (hp : p.Prime) (hpx2 : (p : ℤ) ∣ x ^ 2) :
    (p : ℤ) ∣ x := by
  have hp_int : Prime (p : ℤ) := by
    exact_mod_cast hp
  exact hp_int.dvd_of_dvd_pow hpx2

/-- Odd squares have even sum, in the precise `/ 2` form needed below. -/
theorem two_mul_ediv_two_sq_add_sq_of_odd {u v : ℤ}
    (huodd : Odd u) (hvodd : Odd v) :
    2 * ((u ^ 2 + v ^ 2) / 2) = u ^ 2 + v ^ 2 := by
  have hu2odd : Odd (u ^ 2) := by
    simpa [pow_two] using huodd.mul huodd
  have hv2odd : Odd (v ^ 2) := by
    simpa [pow_two] using hvodd.mul hvodd
  have hEven : Even (u ^ 2 + v ^ 2) := hu2odd.add_odd hv2odd
  have htwo_dvd : (2 : ℤ) ∣ u ^ 2 + v ^ 2 := by
    simpa [even_iff_two_dvd] using hEven
  simpa [mul_comm] using (Int.ediv_mul_cancel htwo_dvd)

/-- The checked divided-triple constructor, exposed as the equation it gives. -/
theorem quarticA_odd_odd_divided_pythagorean_identity
    {u v Z : ℤ}
    (huodd : Odd u) (hvodd : Odd v) (hA : QuarticA u v Z) :
    (Z / 2) ^ 2 + (v ^ 2) ^ 2 = ((u ^ 2 + v ^ 2) / 2) ^ 2 := by
  simpa [PythagoreanTriple] using
    (quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA
      (u := u) (v := v) (Z := Z) huodd hvodd hA)

/--
The requested odd-odd divided triple primitive theorem.

No `Z ≠ 0` or `u ^ 2 ≠ v ^ 2` hypothesis is needed for this gcd statement.
The supplied `u * v ≠ 0` hypothesis is also unused: `Odd u` and `Odd v` already
exclude the zero axes, but the theorem matches the interface requested by the
file.
-/
theorem quarticAOddOddDividedTriplePrimitive :
    QuarticAOddOddDividedTriplePrimitiveTheorem := by
  intro u v Z hcop _huv0 huodd hvodd hA
  apply int_gcd_eq_one_of_no_common_prime
  intro p hp hpZdiv hpv2

  let C : ℤ := (u ^ 2 + v ^ 2) / 2

  have hpt : (Z / 2) ^ 2 + (v ^ 2) ^ 2 = C ^ 2 := by
    dsimp [C]
    exact quarticA_odd_odd_divided_pythagorean_identity huodd hvodd hA

  have hpZdiv_sq : (p : ℤ) ∣ (Z / 2) ^ 2 := by
    exact dvd_pow hpZdiv 2
  have hpv4 : (p : ℤ) ∣ (v ^ 2) ^ 2 := by
    exact dvd_pow hpv2 2
  have hpC_sq : (p : ℤ) ∣ C ^ 2 := by
    have hsum : (p : ℤ) ∣ (Z / 2) ^ 2 + (v ^ 2) ^ 2 :=
      dvd_add hpZdiv_sq hpv4
    simpa [hpt] using hsum
  have hpC : (p : ℤ) ∣ C :=
    int_natPrime_dvd_of_dvd_sq hp hpC_sq

  have htwoC : 2 * C = u ^ 2 + v ^ 2 := by
    dsimp [C]
    exact two_mul_ediv_two_sq_add_sq_of_odd huodd hvodd
  have hp_sum : (p : ℤ) ∣ u ^ 2 + v ^ 2 := by
    simpa [htwoC] using dvd_mul_of_dvd_right hpC (2 : ℤ)
  have hpu2 : (p : ℤ) ∣ u ^ 2 := by
    have hsub : (p : ℤ) ∣ (u ^ 2 + v ^ 2) - v ^ 2 :=
      dvd_sub hp_sum hpv2
    simpa using hsub
  have hpu : (p : ℤ) ∣ u :=
    int_natPrime_dvd_of_dvd_sq hp hpu2
  have hpv : (p : ℤ) ∣ v :=
    int_natPrime_dvd_of_dvd_sq hp hpv2

  have hpdvd_gcd : p ∣ Int.gcd u v := by
    exact Int.dvd_gcd hpu hpv
  have hpdvd_one : p ∣ 1 := by
    simpa [hcop] using hpdvd_gcd
  exact hp.not_dvd_one hpdvd_one

end MazurProof.RationalPointsN12
```

## Audit result

The target

```lean
Int.gcd (Z / 2) (v ^ 2) = 1
```

is true under primitive odd `u,v` and `QuarticA u v Z`.  There is no counterexample to this exact gcd target.

The clean proof does **not** need to first prove `Even Z` and then transfer divisibility from `Z / 2` back to `Z`.  Instead, it uses the already checked divided Pythagorean triple equation

```lean
(Z / 2) ^ 2 + (v ^ 2) ^ 2 = ((u ^ 2 + v ^ 2) / 2) ^ 2.
```

If a rational prime `p` divided both `Z / 2` and `v ^ 2`, then the equation forces `p` to divide `((u ^ 2 + v ^ 2) / 2)`.  Since `u` and `v` are odd,

```lean
2 * ((u ^ 2 + v ^ 2) / 2) = u ^ 2 + v ^ 2,
```

so `p ∣ u ^ 2 + v ^ 2`.  Together with `p ∣ v ^ 2`, this gives `p ∣ u ^ 2`, hence `p ∣ u`; also `p ∣ v ^ 2` gives `p ∣ v`.  That contradicts `Int.gcd u v = 1`.

A slightly stronger companion statement is also true and often useful:

```lean
Int.gcd ((u ^ 2 + v ^ 2) / 2) (v ^ 2) = 1
```

under the same primitive odd hypotheses.  The theorem requested in the interface is therefore correctly targeted; no replacement primitive gcd target is needed.
