# Q1478 (dm3): `UV_coprime` for the quartic descent

## Executive answer

Use `IsRelPrime` first, then convert back to `Int.gcd = 1` at the end.  This avoids trying to reason directly about the natural-valued `Int.gcd` while doing prime-divisor arguments over `ℤ`.

The main proof shape is:

1. Let
   ```text
   A = 2*r^2 + B^2,
   U = A - 2*s,
   V = A + 2*s.
   ```
2. Prove
   ```text
   U * V = 5 * B^4.
   ```
3. To prove `IsRelPrime U V`, take a common divisor `d` of `U,V`.  If `d` is not a unit, choose a natural prime `p ∣ d.natAbs`, hence `(p : ℤ) ∣ d`, hence `(p : ℤ) ∣ U,V`.
4. From `(p : ℤ) ∣ U,V`, get `(p : ℤ)^2 ∣ U*V = 5*B^4`.
5. Also, from `(p : ℤ) ∣ U,V`, get `(p : ℤ) ∣ 2*A`; if `p ≠ 2`, then `(p : ℤ) ∣ A`.
6. Show `(p : ℤ) ∤ B`: otherwise `p ∣ A` and `p ∣ B` imply `p ∣ 2*r^2`; since the `p=2` case contradicts `B % 2 = 1`, the odd-prime case gives `p ∣ r`, contradicting `Int.gcd r B = 1`.
7. Now `(p : ℤ)^2 ∣ 5*B^4` and `p ∤ B`.  First `p ∣ 5`; hence `p=5`.  Then `25 ∣ 5*B^4`, so `5 ∣ B^4`, hence `5 ∣ B`, contradiction.

This is cleaner than pushing the whole argument through `Int.gcd_greatest` manually.

## Lean code

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace FLT.DM3

lemma not_two_dvd_of_emod_eq_one {z : ℤ} (hz : z % 2 = 1) :
    ¬ (2 : ℤ) ∣ z := by
  intro h
  have h0 : z % 2 = 0 := by
    simpa [Int.ModEq] using
      (Int.modEq_zero_iff_dvd.mpr h : z ≡ 0 [ZMOD (2 : ℤ)])
  rw [hz] at h0
  norm_num at h0

/--
Coprimality of the two quartic-descent factors.

This is the requested statement, written with `Int.gcd`.  The positivity assumptions are kept
because they match the quartic-descent call site, although this particular gcd proof only uses
`hcop`, `hr_odd`, `hB_odd`, and `heq`.
-/
theorem UV_coprime
    (r B s : ℤ)
    (hr : 0 < r) (hBpos : 0 < B)
    (hcop : Int.gcd r B = 1)
    (hr_odd : r % 2 = 1) (hB_odd : B % 2 = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    Int.gcd (2 * r ^ 2 + B ^ 2 - 2 * s)
      (2 * r ^ 2 + B ^ 2 + 2 * s) = 1 := by
  classical

  let A : ℤ := 2 * r ^ 2 + B ^ 2
  let U : ℤ := A - 2 * s
  let V : ℤ := A + 2 * s

  change Int.gcd U V = 1

  have hcopI : IsCoprime r B := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd_def] using hcop

  have hprod : U * V = 5 * B ^ 4 := by
    dsimp [U, V, A]
    nlinarith [heq]

  have hrel : IsRelPrime U V := by
    intro d hdU hdV
    by_contra hd_not_unit

    have hd_nat_ne_one : d.natAbs ≠ 1 := by
      intro hdabs
      exact hd_not_unit (Int.isUnit_iff_natAbs_eq.mpr hdabs)

    obtain ⟨p, hp, hpd_nat⟩ := Nat.exists_prime_and_dvd hd_nat_ne_one
    have hpd : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd_nat
    have hpU : (p : ℤ) ∣ U := hpd.trans hdU
    have hpV : (p : ℤ) ∣ V := hpd.trans hdV

    have hp2A : (p : ℤ) ∣ 2 * A := by
      have hsum : (p : ℤ) ∣ U + V := dvd_add hpU hpV
      convert hsum using 1
      ring_nf [U, V, A]

    have hpA_of_ne_two (hpne2 : p ≠ 2) : (p : ℤ) ∣ A := by
      rcases Int.Prime.dvd_mul' hp hp2A with hp2 | hpA
      · have hp2_nat : p ∣ (2 : ℕ) := by
          exact_mod_cast hp2
        have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2_nat
        have hge2 : 2 ≤ p := hp.two_le
        exact (hpne2 (le_antisymm hple2 hge2)).elim
      · exact hpA

    have hpnB : ¬ (p : ℤ) ∣ B := by
      intro hpB
      by_cases hp2 : p = 2
      · subst p
        exact (not_two_dvd_of_emod_eq_one hB_odd) hpB
      · have hpA : (p : ℤ) ∣ A := hpA_of_ne_two hp2
        have hpB2 : (p : ℤ) ∣ B ^ 2 := pow_dvd_pow hpB 2
        have hp2r2 : (p : ℤ) ∣ 2 * r ^ 2 := by
          have hsub : (p : ℤ) ∣ A - B ^ 2 := dvd_sub hpA hpB2
          convert hsub using 1
          ring_nf [A]
        rcases Int.Prime.dvd_mul' hp hp2r2 with hp_dvd_two | hp_dvd_r2
        · have hp2_nat : p ∣ (2 : ℕ) := by
            exact_mod_cast hp_dvd_two
          have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2_nat
          have hge2 : 2 ≤ p := hp.two_le
          exact (hp2 (le_antisymm hple2 hge2)).elim
        · have hpr : (p : ℤ) ∣ r := Int.Prime.dvd_pow' hp hp_dvd_r2
          have hunitp : IsUnit (p : ℤ) :=
            hcopI.isUnit_of_dvd' hpr hpB
          exact (Nat.prime_iff_prime_int.mp hp).not_unit hunitp

    have hpUV : (p : ℤ) ^ 2 ∣ U * V := by
      simpa [pow_two] using mul_dvd_mul hpU hpV

    have hp2prod : (p : ℤ) ^ 2 ∣ 5 * B ^ 4 := by
      simpa [hprod] using hpUV

    have hpdivprod : (p : ℤ) ∣ 5 * B ^ 4 := by
      have hppow : (p : ℤ) ∣ (p : ℤ) ^ 2 := by
        exact ⟨(p : ℤ), by ring⟩
      exact hppow.trans hp2prod

    rcases Int.Prime.dvd_mul' hp hpdivprod with hp_dvd_five | hp_dvd_B4
    · have hp_dvd_five_nat : p ∣ (5 : ℕ) := by
        exact_mod_cast hp_dvd_five
      have hple5 : p ≤ 5 := Nat.le_of_dvd (by norm_num) hp_dvd_five_nat
      have hge2 : 2 ≤ p := hp.two_le
      have hp_eq_five : p = 5 := by
        interval_cases p <;> norm_num at hp hp_dvd_five_nat
      subst p
      have h5B4 : (5 : ℤ) ∣ B ^ 4 := by
        have h25 : (5 : ℤ) * 5 ∣ 5 * B ^ 4 := by
          simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hp2prod
        exact Int.dvd_of_mul_dvd_mul_left h25 (by norm_num : (5 : ℤ) ≠ 0)
      have h5B : (5 : ℤ) ∣ B :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 5) h5B4
      exact hpnB h5B
    · have hpB : (p : ℤ) ∣ B := Int.Prime.dvd_pow' hp hp_dvd_B4
      exact hpnB hpB

  have hcopUV : IsCoprime U V := isRelPrime_iff_isCoprime.mp hrel
  have hcopUV_nat : Nat.Coprime U.natAbs V.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hcopUV
  simpa [Int.gcd_def, Nat.coprime_iff_gcd_eq_one] using hcopUV_nat

end FLT.DM3
```

## Notes for integration

The proof deliberately uses `IsRelPrime U V` as the middle target.  The key conversion at the end is:

```lean
have hcopUV : IsCoprime U V := isRelPrime_iff_isCoprime.mp hrel
have hcopUV_nat : Nat.Coprime U.natAbs V.natAbs :=
  Int.isCoprime_iff_nat_coprime.mp hcopUV
simpa [Int.gcd_def, Nat.coprime_iff_gcd_eq_one] using hcopUV_nat
```

The only fragile line is the cancellation line:

```lean
exact Int.dvd_of_mul_dvd_mul_left h25 (by norm_num : (5 : ℤ) ≠ 0)
```

If your local import exposes the arguments in the opposite order, replace it by:

```lean
exact Int.dvd_of_mul_dvd_mul_left (by norm_num : (5 : ℤ) ≠ 0) h25
```

The rest uses the pinned Mathlib APIs:

```lean
Int.gcd_def
Int.isCoprime_iff_nat_coprime
Int.Prime.dvd_mul'
Int.Prime.dvd_pow'
isRelPrime_iff_isCoprime
```
