# Q2519 endpoint pair helper for WeakPrimitiveAPPairwise

Paste after the existing `rootGCD4` definition.  This is endpoint-specific content, not Q2450 content.

```lean
/-- If a natural prime divides integer `3`, then it is `3`. -/
lemma q2519_nat_prime_eq_three_of_int_dvd_three
    {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ((ℓ : ℤ) ∣ (3 : ℤ))) :
    ℓ = 3 := by
  have hNat : ℓ ∣ (3 : ℕ) := by
    simpa using (Int.natCast_dvd.mp h)
  have hle : ℓ ≤ 3 := Nat.le_of_dvd (by decide : 0 < (3 : ℕ)) hNat
  have hge : 2 ≤ ℓ := hℓ.two_le
  interval_cases ℓ <;> norm_num at hNat ⊢

/-- If a Nat prime divides all four roots, it contradicts `rootGCD4 = 1`. -/
lemma q2519_false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
    {p q r s : ℤ} {ℓ : ℕ}
    (hroot : rootGCD4 p q r s = 1)
    (hℓ : ℓ.Prime)
    (hp : ℓ ∣ p.natAbs)
    (hq : ℓ ∣ q.natAbs)
    (hr : ℓ ∣ r.natAbs)
    (hs : ℓ ∣ s.natAbs) :
    False := by
  have hℓroot : ℓ ∣ rootGCD4 p q r s := by
    unfold rootGCD4
    exact Nat.dvd_gcd hp (Nat.dvd_gcd hq (Nat.dvd_gcd hr hs))
  have hℓone : ℓ ∣ (1 : ℕ) := by
    simpa [hroot] using hℓroot
  have hle : ℓ ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hℓone
  exact (not_lt_of_ge hle) hℓ.one_lt

/-- The special `ℓ = 3` endpoint residue check.  In `ZMod 3`, if the endpoint
squares are both zero and the three square differences are equal, then the two
middle roots are also zero. -/
lemma q2519_zmod3_endpoint_square_ap_forces_middle_zero
    (P Q R S Δ : ZMod 3)
    (hp : P = 0) (hs : S = 0)
    (hpq : Q ^ 2 - P ^ 2 = Δ)
    (hqr : R ^ 2 - Q ^ 2 = Δ)
    (hrs : S ^ 2 - R ^ 2 = Δ) :
    Q = 0 ∧ R = 0 := by
  fin_cases P <;> fin_cases Q <;> fin_cases R <;>
    fin_cases S <;> fin_cases Δ <;>
    norm_num at hp hs hpq hqr hrs ⊢

/-- Endpoint propagation for `(p,s)`: any Nat prime dividing endpoint roots
propagates to all four roots in a four-square AP.  The `ℓ = 3` case is handled
by `q2519_zmod3_endpoint_square_ap_forces_middle_zero`; all other primes cancel
from `ℓ ∣ 3*Δ`. -/
lemma q2519_nat_prime_dvd_all_roots_of_dvd_ps_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hp : ℓ ∣ p.natAbs)
    (hs : ℓ ∣ s.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  by_cases h3 : ℓ = 3
  · subst ℓ
    have hpZ3 : ((3 : ℤ) ∣ p) := Int.natCast_dvd.mpr hp
    have hsZ3 : ((3 : ℤ) ∣ s) := Int.natCast_dvd.mpr hs
    have hp0 : (p : ZMod 3) = 0 := by
      exact (CharP.intCast_eq_intCast (ZMod 3) 3).mpr
        (Int.modEq_zero_iff_dvd.mpr hpZ3)
    have hs0 : (s : ZMod 3) = 0 := by
      exact (CharP.intCast_eq_intCast (ZMod 3) 3).mpr
        (Int.modEq_zero_iff_dvd.mpr hsZ3)
    have hpq3 : (q : ZMod 3) ^ 2 - (p : ZMod 3) ^ 2 = (Δ : ZMod 3) := by
      have := congrArg (fun z : ℤ => (z : ZMod 3)) hpq
      simpa using this
    have hqr3 : (r : ZMod 3) ^ 2 - (q : ZMod 3) ^ 2 = (Δ : ZMod 3) := by
      have := congrArg (fun z : ℤ => (z : ZMod 3)) hqr
      simpa using this
    have hrs3 : (s : ZMod 3) ^ 2 - (r : ZMod 3) ^ 2 = (Δ : ZMod 3) := by
      have := congrArg (fun z : ℤ => (z : ZMod 3)) hrs
      simpa using this
    rcases q2519_zmod3_endpoint_square_ap_forces_middle_zero
        (p : ZMod 3) (q : ZMod 3) (r : ZMod 3) (s : ZMod 3) (Δ : ZMod 3)
        hp0 hs0 hpq3 hqr3 hrs3 with ⟨hq0, hr0⟩
    have hqZ3 : ((3 : ℤ) ∣ q) := by
      exact Int.modEq_zero_iff_dvd.mp <|
        (CharP.intCast_eq_intCast (ZMod 3) 3).mp hq0
    have hrZ3 : ((3 : ℤ) ∣ r) := by
      exact Int.modEq_zero_iff_dvd.mp <|
        (CharP.intCast_eq_intCast (ZMod 3) 3).mp hr0
    have hq : 3 ∣ q.natAbs := Int.natCast_dvd.mp hqZ3
    have hr : 3 ∣ r.natAbs := Int.natCast_dvd.mp hrZ3
    exact ⟨hp, hq, hr, hs⟩
  · have hpZ : ((ℓ : ℤ) ∣ p) := Int.natCast_dvd.mpr hp
    have hsZ : ((ℓ : ℤ) ∣ s) := Int.natCast_dvd.mpr hs
    have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := pow_dvd_pow_of_dvd hpZ 2
    have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := pow_dvd_pow_of_dvd hsZ 2
    have hdiffZ : ((ℓ : ℤ) ∣ s ^ 2 - p ^ 2) := Int.dvd_sub hs2Z hp2Z
    have hsum : s ^ 2 - p ^ 2 = 3 * Δ := by
      calc
        s ^ 2 - p ^ 2 = (q ^ 2 - p ^ 2) + (r ^ 2 - q ^ 2) + (s ^ 2 - r ^ 2) := by ring
        _ = Δ + Δ + Δ := by rw [hpq, hqr, hrs]
        _ = 3 * Δ := by ring
    have h3DeltaZ : ((ℓ : ℤ) ∣ 3 * Δ) := by
      rwa [hsum] at hdiffZ
    have hDeltaZ : ((ℓ : ℤ) ∣ Δ) := by
      rcases Int.Prime.dvd_mul' hℓ h3DeltaZ with hℓ3 | hΔ
      · exact False.elim (h3 (q2519_nat_prime_eq_three_of_int_dvd_three hℓ hℓ3))
      · exact hΔ
    have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := by
      have hq_sq : q ^ 2 = p ^ 2 + Δ := by nlinarith [hpq]
      rw [hq_sq]
      exact Int.dvd_add hp2Z hDeltaZ
    have hq : ℓ ∣ q.natAbs := Int.Prime.dvd_pow hℓ hq2Z
    have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
      have hr_sq : r ^ 2 = q ^ 2 + Δ := by nlinarith [hqr]
      rw [hr_sq]
      exact Int.dvd_add hq2Z hDeltaZ
    have hr : ℓ ∣ r.natAbs := Int.Prime.dvd_pow hℓ hr2Z
    exact ⟨hp, hq, hr, hs⟩

/-- Endpoint gcd residual for `WeakPrimitiveAPPairwise`.  The oddness assumptions
are accepted to match the residual interface, but the proof does not need them. -/
theorem int_gcd_ps_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1)
    (_hp_odd : p % 2 = 1)
    (_hs_odd : s % 2 = 1) :
    Int.gcd p s = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hp hs
  rcases q2519_nat_prime_dvd_all_roots_of_dvd_ps_weak_ap hℓ hpq hqr hrs hp hs with
    ⟨hp', hq', hr', hs'⟩
  exact False.elim <|
    q2519_false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
      hroot hℓ hp' hq' hr' hs'
```
