# Q1458 (dm1/dm2): `gcd(u.num.natAbs, B₀) = 1` from a square denominator

Use `u.reduced` and shrink coprimality along the divisor `B₀ ∣ u.den`.  The stable modern Mathlib spelling is `Coprime.of_dvd_right`; the older spelling `coprime_dvd_right` also works.

```lean
import Mathlib

namespace DM2

/-- Nat-coprime form: if `u.den = B₀ * B₀`, then `u.num.natAbs` is coprime to `B₀`. -/
lemma rat_num_natAbs_coprime_of_den_eq_mul_self (u : ℚ) {B₀ : ℕ}
    (hB₀ : u.den = B₀ * B₀) :
    Nat.Coprime u.num.natAbs B₀ := by
  have hB₀_dvd_den : B₀ ∣ u.den := by
    rw [hB₀]
    exact ⟨B₀, rfl⟩
  exact u.reduced.of_dvd_right hB₀_dvd_den

/-- The exact `Nat.gcd` version. -/
lemma rat_num_natAbs_gcd_of_den_eq_mul_self (u : ℚ) {B₀ : ℕ}
    (hB₀ : u.den = B₀ * B₀) :
    Nat.gcd u.num.natAbs B₀ = 1 := by
  exact (rat_num_natAbs_coprime_of_den_eq_mul_self (u := u) hB₀).gcd_eq_one

/-- If your square hypothesis is written with `^ 2` instead of `*`. -/
lemma rat_num_natAbs_gcd_of_den_eq_sq (u : ℚ) {B₀ : ℕ}
    (hB₀ : u.den = B₀ ^ 2) :
    Nat.gcd u.num.natAbs B₀ = 1 := by
  exact rat_num_natAbs_gcd_of_den_eq_mul_self (u := u)
    (B₀ := B₀) (by simpa [pow_two] using hB₀)

/-- The corresponding `Int.gcd` form, usually what the descent code wants. -/
lemma rat_num_int_gcd_of_den_eq_mul_self (u : ℚ) {B₀ : ℕ}
    (hB₀ : u.den = B₀ * B₀) :
    Int.gcd u.num (B₀ : ℤ) = 1 := by
  have hnat : Nat.gcd u.num.natAbs B₀ = 1 :=
    rat_num_natAbs_gcd_of_den_eq_mul_self (u := u) hB₀
  simpa [Int.gcd_eq_natAbs] using hnat

/-- Same `Int.gcd` form for the `^ 2` hypothesis. -/
lemma rat_num_int_gcd_of_den_eq_sq (u : ℚ) {B₀ : ℕ}
    (hB₀ : u.den = B₀ ^ 2) :
    Int.gcd u.num (B₀ : ℤ) = 1 := by
  exact rat_num_int_gcd_of_den_eq_mul_self (u := u)
    (B₀ := B₀) (by simpa [pow_two] using hB₀)

end DM2
```

If you want the old API spelling exactly as in your note, replace the final line of the first lemma by:

```lean
  exact u.reduced.coprime_dvd_right hB₀_dvd_den
```

I prefer `of_dvd_right` because Mathlib has it as the forward-compatible wrapper around `coprime_dvd_right`.