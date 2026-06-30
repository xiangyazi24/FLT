# Q2324: `QuarticA` opposite-parity leg coprime

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/--
In the opposite-parity branch both QuarticA factors are odd, hence their
product is odd.  This is the parity fact that rules out a common factor `2`
between `Z` and `2 * v ^ 2`.
-/
lemma quarticA_oppParity_factor_product_odd {u v : ℤ}
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) :
    Odd ((u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) := by
  rcases hopp with h | h
  · rcases h with ⟨hu, hv⟩
    have hu2 : Odd (u ^ 2) := by
      simpa using (hu.pow : Odd (u ^ 2))
    have hv2 : Even (v ^ 2) := by
      simpa using ((Int.even_pow' (m := v) (n := 2) (by decide)).2 hv)
    have hleft : Odd (u ^ 2 - v ^ 2) := hu2.sub_even hv2
    have h3v2 : Even (3 * v ^ 2) := hv2.mul_left 3
    have hright : Odd (u ^ 2 + 3 * v ^ 2) := hu2.add_even h3v2
    exact hleft.mul hright
  · rcases h with ⟨hu, hv⟩
    have hu2 : Even (u ^ 2) := by
      simpa using ((Int.even_pow' (m := u) (n := 2) (by decide)).2 hu)
    have hv2 : Odd (v ^ 2) := by
      simpa using (hv.pow : Odd (v ^ 2))
    have hleft : Odd (u ^ 2 - v ^ 2) := hu2.sub_odd hv2
    have hthree : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have h3v2 : Odd (3 * v ^ 2) := hthree.mul hv2
    have hright : Odd (u ^ 2 + 3 * v ^ 2) := hu2.add_odd h3v2
    exact hleft.mul hright

/-- QuarticA plus opposite parity forces `Z` odd. -/
lemma quarticA_oppParity_Z_odd {u v Z : ℤ}
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z) :
    Odd Z := by
  have hAeq :
      Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
    simpa [QuarticA] using hA
  have hZ2 : Odd (Z ^ 2) := by
    rw [hAeq]
    exact quarticA_oppParity_factor_product_odd (u := u) (v := v) hopp
  exact ((Int.odd_pow' (m := Z) (n := 2) (by decide)).1 hZ2)

/--
A direct primitive-leg coprimality proof for the QuarticA Pythagorean triple
`(Z, 2 * v ^ 2, u ^ 2 + v ^ 2)`.

The hypotheses `u * v ≠ 0` and `u ^ 2 ≠ v ^ 2` are not used for this gcd
statement; they are kept to match the project-facing bridge interface.
-/
theorem quarticA_oppParity_leg_coprime
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (_huv0 : u * v ≠ 0)
    (_hne : u ^ 2 ≠ v ^ 2)
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z) :
    Int.gcd Z (2 * v ^ 2) = 1 := by
  rw [Int.gcd_eq_natAbs, ← Nat.coprime_iff_gcd_eq_one]
  refine Nat.coprime_of_dvd' ?_
  intro p hp hpZ hpLeg
  have hpZ_int : (p : ℤ) ∣ Z := by
    rwa [Int.natCast_dvd]
  have hpLeg_int : (p : ℤ) ∣ 2 * v ^ 2 := by
    rwa [Int.natCast_dvd]
  rcases prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp hpLeg_int with rfl | hpv_nat
  · exfalso
    have hZodd : Odd Z := quarticA_oppParity_Z_odd (u := u) (v := v) (Z := Z) hopp hA
    have hZeven : Even Z := even_iff_two_dvd.mpr hpZ_int
    exact (Int.not_odd_iff_even.mpr hZeven) hZodd
  · have hAeq :
        Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
      simpa [QuarticA] using hA
    have hpv_int : (p : ℤ) ∣ v := by
      rwa [Int.natCast_dvd]
    have hpZ2 : (p : ℤ) ∣ Z ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hpZ_int Z
    have hprod :
        (p : ℤ) ∣ (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
      rwa [← hAeq]
    have hpv2 : (p : ℤ) ∣ v ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hpv_int v
    have hpv4 : (p : ℤ) ∣ v ^ 4 := by
      exact dvd_trans hpv2 ⟨v ^ 2, by ring⟩
    have hterm1 : (p : ℤ) ∣ 2 * u ^ 2 * v ^ 2 := by
      exact dvd_mul_of_dvd_right hpv2 (2 * u ^ 2)
    have hterm2 : (p : ℤ) ∣ 3 * v ^ 4 := by
      exact dvd_mul_of_dvd_right hpv4 3
    have htail : (p : ℤ) ∣ 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4 :=
      dvd_sub hterm1 hterm2
    have hfac_expand :
        (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) =
          u ^ 4 + 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4 := by
      ring
    rw [hfac_expand] at hprod
    have hpu4' :
        (p : ℤ) ∣
          (u ^ 4 + 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4) -
            (2 * u ^ 2 * v ^ 2 - 3 * v ^ 4) :=
      dvd_sub hprod htail
    have hpu4 : (p : ℤ) ∣ u ^ 4 := by
      convert hpu4' using 1
      ring
    have hpu_int : (p : ℤ) ∣ u := Int.Prime.dvd_pow' hp hpu4
    have hpu_nat : p ∣ u.natAbs := by
      rwa [← Int.natCast_dvd]
    have hp_gcd : p ∣ Int.gcd u v := by
      rw [Int.gcd_eq_natAbs]
      exact Nat.dvd_gcd hpu_nat hpv_nat
    simpa [hcop] using hp_gcd

end MazurProof.RationalPointsN12
```

## Answers to the critical questions

1. **Which classification leg is `2 * v ^ 2`?**  In the opposite-parity branch, `Z` is odd by `quarticA_oppParity_Z_odd`, while `2 * v ^ 2` is even.  Therefore, in the primitive Pythagorean classification of
   ```lean
   PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2)
   ```
   the second leg `2 * v ^ 2` is the even leg `2 * m * n`.  If using `PythagoreanTriple.coprime_classification.mp` directly, the returned first disjunction is the usable one:
   ```lean
   Z = m ^ 2 - n ^ 2 ∧ 2 * v ^ 2 = 2 * m * n
   ```
   The swapped disjunction would make `Z = 2 * m * n`, hence `Z` even, contradicting `Odd Z`.

2. **Can `r * s = v ^ 2` be obtained exactly?**  Yes, after the orientation is fixed.  From
   ```lean
   h2v : 2 * v ^ 2 = 2 * m * n
   ```
   one gets exactly
   ```lean
   have hprod : m * n = v ^ 2 := by
     have htwo : (2 : ℤ) * (m * n) = 2 * (v ^ 2) := by
       calc
         (2 : ℤ) * (m * n) = 2 * m * n := by ring
         _ = 2 * v ^ 2 := h2v.symm
         _ = 2 * (v ^ 2) := by ring
     exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) htwo
   ```
   There is no sign ambiguity in this product equation.  The classification theorem’s sign ambiguity is on the hypotenuse equation `z = ±(m ^ 2 + n ^ 2)`, not on the leg equation.

3. **Does the branch need `Z` sign normalized or `Z ≠ 0`?**  No.  The gcd lemma above does not use sign normalization for `Z`, and it does not require an explicit `Z ≠ 0`.  In fact, opposite parity plus `QuarticA u v Z` already gives `Odd Z`, hence `Z ≠ 0` if needed later.  The hypotheses `u * v ≠ 0` and `u ^ 2 ≠ v ^ 2` are not needed for this particular gcd statement, though they may still belong in the safe bridge interface.

4. **Is the target `Int.gcd Z (2 * v ^ 2) = 1` correct?**  Yes.  It is not `2`.  The factor `2` is excluded because `Z` is odd.  Any odd prime divisor common to `Z` and `2 * v ^ 2` divides `v`; using
   ```lean
   Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)
   ```
   and reducing the right-hand side modulo that prime gives divisibility of `u ^ 4`, hence divisibility of `u`, contradicting `Int.gcd u v = 1`.
