# Q2512 distance-two pair helper for WeakPrimitiveAPPairwise

## Verdict

Use the prime-divisor route, but make the proof modular.  The key helpers are:

1. `int_odd_mod_two_not_dvd`: turns `a % 2 = 1` into `¬ (2 : ℤ) ∣ a`.
2. `prime_dvd_rootGCD4_of_dvd_all`: packages the contradiction with `hroot : rootGCD4 p q r s = 1`.
3. `weakPrimitiveAP_distanceTwo_gcd_pr_eq_one`: proves `Int.gcd p r = 1`.

I could not fetch `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean` from GitHub `main`; it appears not to be present on the remote branch available to the connector.  The code below is therefore written as a standalone paste-in block.  If `rootGCD4` is already defined in the current file, omit the local `def rootGCD4` line.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Int.Basic

/-- Omit this if already present in `N12FourSquaresAP.lean`. -/
def rootGCD4 (a b c d : ℤ) : ℕ :=
  Nat.gcd a.natAbs (Nat.gcd b.natAbs (Nat.gcd c.natAbs d.natAbs))

/-- Integer oddness in the local `% 2 = 1` form rules out divisibility by `2`. -/
theorem int_odd_mod_two_not_dvd {a : ℤ} (ha : a % 2 = 1) :
    ¬ (2 : ℤ) ∣ a := by
  intro h2a
  have hmodEq : a ≡ 0 [ZMOD (2 : ℤ)] := Int.modEq_zero_iff_dvd.mpr h2a
  have hmod0 : a % 2 = 0 := by
    simpa [Int.ModEq] using hmodEq
  rw [hmod0] at ha
  norm_num at ha

/-- A natural prime dividing all four roots divides `rootGCD4`. -/
theorem prime_dvd_rootGCD4_of_dvd_all
    {ℓ : ℕ} {p q r s : ℤ}
    (hℓp : ℓ ∣ p.natAbs)
    (hℓq : ℓ ∣ q.natAbs)
    (hℓr : ℓ ∣ r.natAbs)
    (hℓs : ℓ ∣ s.natAbs) :
    ℓ ∣ rootGCD4 p q r s := by
  unfold rootGCD4
  exact Nat.dvd_gcd hℓp (Nat.dvd_gcd hℓq (Nat.dvd_gcd hℓr hℓs))

/-- If an odd natural prime divides `2 * Δ`, then it divides `Δ`.

The input prime is natural, but divisibility is over `ℤ`, which is the convenient
form for the AP equations.
-/
theorem natPrime_dvd_of_dvd_two_mul_int_of_ne_two
    {ℓ : ℕ} {Δ : ℤ}
    (hℓprime : Nat.Prime ℓ)
    (hℓne2 : ℓ ≠ 2)
    (hℓtwoΔ : (ℓ : ℤ) ∣ 2 * Δ) :
    (ℓ : ℤ) ∣ Δ := by
  have hcases : (ℓ : ℤ) ∣ (2 : ℤ) ∨ (ℓ : ℤ) ∣ Δ :=
    Int.Prime.dvd_mul' hℓprime hℓtwoΔ
  rcases hcases with hℓtwo | hℓΔ
  · exfalso
    have hℓdvd2Nat : ℓ ∣ (2 : ℕ) := by
      simpa using (Int.natCast_dvd.mp hℓtwo)
    have hℓle2 : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓdvd2Nat
    have h2leℓ : 2 ≤ ℓ := hℓprime.two_le
    exact hℓne2 (le_antisymm hℓle2 h2leℓ)
  · exact hℓΔ

/-- Distance-two coprimality for the first and third roots in a primitive
four-square AP.

Mathematical route: if a natural prime `ℓ` divides `p` and `r`, then it divides
`r^2 - p^2 = 2*Δ`.  If `ℓ = 2`, this contradicts `p % 2 = 1`.  If `ℓ ≠ 2`,
then `ℓ ∣ Δ`; the AP equations propagate divisibility to `q` and `s`, so `ℓ`
divides `rootGCD4 p q r s = 1`, impossible.
-/
theorem weakPrimitiveAP_distanceTwo_gcd_pr_eq_one
    {p q r s Δ : ℤ}
    (hpq : q^2 - p^2 = Δ)
    (hqr : r^2 - q^2 = Δ)
    (hrs : s^2 - r^2 = Δ)
    (hroot : rootGCD4 p q r s = 1)
    (hp_odd : p % 2 = 1)
    (_hr_odd : r % 2 = 1) :
    Int.gcd p r = 1 := by
  by_contra hbad
  have hbadNat : ¬ Nat.Coprime p.natAbs r.natAbs := by
    intro hcop
    apply hbad
    simpa [Int.gcd_def, Nat.Coprime] using hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hbadNat with
    ⟨ℓ, hℓprime, hℓpNat, hℓrNat⟩
  have hℓp : (ℓ : ℤ) ∣ p := Int.natCast_dvd.mpr hℓpNat
  have hℓr : (ℓ : ℤ) ∣ r := Int.natCast_dvd.mpr hℓrNat

  by_cases hℓeq2 : ℓ = 2
  · subst ℓ
    have h2p : (2 : ℤ) ∣ p := by simpa using hℓp
    exact int_odd_mod_two_not_dvd hp_odd h2p

  have hℓ_r2_sub_p2 : (ℓ : ℤ) ∣ r^2 - p^2 := by
    exact dvd_sub (pow_dvd_pow_of_dvd hℓr 2) (pow_dvd_pow_of_dvd hℓp 2)
  have hrp_twoDelta : r^2 - p^2 = 2 * Δ := by
    nlinarith
  have hℓ_twoDelta : (ℓ : ℤ) ∣ 2 * Δ := by
    rwa [hrp_twoDelta] at hℓ_r2_sub_p2
  have hℓΔ : (ℓ : ℤ) ∣ Δ :=
    natPrime_dvd_of_dvd_two_mul_int_of_ne_two hℓprime hℓeq2 hℓ_twoDelta

  have hℓq : (ℓ : ℤ) ∣ q := by
    apply Int.Prime.dvd_pow' hℓprime
    have hq2 : q^2 = p^2 + Δ := by
      nlinarith
    rw [hq2]
    exact dvd_add (pow_dvd_pow_of_dvd hℓp 2) hℓΔ

  have hℓs : (ℓ : ℤ) ∣ s := by
    apply Int.Prime.dvd_pow' hℓprime
    have hs2 : s^2 = r^2 + Δ := by
      nlinarith
    rw [hs2]
    exact dvd_add (pow_dvd_pow_of_dvd hℓr 2) hℓΔ

  have hℓroot : ℓ ∣ rootGCD4 p q r s :=
    prime_dvd_rootGCD4_of_dvd_all
      (Int.natCast_dvd.mp hℓp)
      (Int.natCast_dvd.mp hℓq)
      (Int.natCast_dvd.mp hℓr)
      (Int.natCast_dvd.mp hℓs)
  have hℓone : ℓ ∣ (1 : ℕ) := by
    simpa [hroot] using hℓroot
  have hℓeq1 : ℓ = 1 := Nat.dvd_one.mp hℓone
  exact hℓprime.ne_one hℓeq1
```

For the `q,s` distance-two pair, either duplicate the theorem with the roles shifted, or call the same theorem on the reversed AP after proving the corresponding permutation of `rootGCD4`.  The proof above intentionally only needs the oddness of the first root in the pair; `_hr_odd` is kept in the signature so it matches the `WeakPrimitiveAPPairwise` data flow.
