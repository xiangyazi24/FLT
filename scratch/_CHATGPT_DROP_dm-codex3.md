# Q2506 WeakPrimitiveAPPairwise adjacent-pair Lean helper

This round gives a no-`sorry` adjacent-pair helper for the hard `WeakPrimitiveAPPairwise` residual. Paste the code below after the existing `rootGCD4` definition in `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.

The `(p,q)` adjacent case is easier than the endpoint case and does **not** need the oddness assumptions: if a prime `ℓ` divides both `p` and `q`, then `ℓ ∣ Δ`; from `r^2 = q^2 + Δ` and `s^2 = r^2 + Δ`, primality propagates `ℓ` to `r` and `s`, contradicting `rootGCD4 = 1`.

```lean
import Mathlib

/-- Exact bridge used below: a natural divisor of `x.natAbs` is the same as its
integer cast dividing `x`.  This is just `Int.natCast_dvd`. -/
theorem nat_dvd_natAbs_iff_int_dvd {n : ℕ} {x : ℤ} :
    n ∣ x.natAbs ↔ ((n : ℤ) ∣ x) := by
  exact Int.natCast_dvd.symm

/-- If a Nat prime divides all four roots, it contradicts `rootGCD4 = 1`. -/
theorem false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
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

/-- Adjacent-pair propagation for `(p,q)`: any Nat prime dividing `p` and `q`
propagates to all four roots in a four-square AP. -/
theorem nat_prime_dvd_all_roots_of_dvd_pq_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hp : ℓ ∣ p.natAbs)
    (hq : ℓ ∣ q.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  have hpZ : ((ℓ : ℤ) ∣ p) := Int.natCast_dvd.mpr hp
  have hqZ : ((ℓ : ℤ) ∣ q) := Int.natCast_dvd.mpr hq
  have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := pow_dvd_pow_of_dvd hpZ 2
  have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := pow_dvd_pow_of_dvd hqZ 2
  have hDeltaZ : ((ℓ : ℤ) ∣ Δ) := by
    rw [← hpq]
    exact Int.dvd_sub hq2Z hp2Z
  have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
    have hr_sq : r ^ 2 = q ^ 2 + Δ := by
      nlinarith [hqr]
    rw [hr_sq]
    exact Int.dvd_add hq2Z hDeltaZ
  have hr : ℓ ∣ r.natAbs := Int.Prime.dvd_pow hℓ hr2Z
  have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := by
    have hs_sq : s ^ 2 = r ^ 2 + Δ := by
      nlinarith [hrs]
    rw [hs_sq]
    exact Int.dvd_add hr2Z hDeltaZ
  have hs : ℓ ∣ s.natAbs := Int.Prime.dvd_pow hℓ hs2Z
  exact ⟨hp, hq, hr, hs⟩

/-- The adjacent `(p,q)` gcd residual.  This is the first reusable piece of
`WeakPrimitiveAPPairwise`; it needs no parity hypotheses. -/
theorem int_gcd_pq_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd p q = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hp hq
  exact False.elim <|
    false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
      hroot hℓ
      (nat_prime_dvd_all_roots_of_dvd_pq_weak_ap hℓ hpq hqr hrs hp hq).1
      (nat_prime_dvd_all_roots_of_dvd_pq_weak_ap hℓ hpq hqr hrs hp hq).2.1
      (nat_prime_dvd_all_roots_of_dvd_pq_weak_ap hℓ hpq hqr hrs hp hq).2.2.1
      (nat_prime_dvd_all_roots_of_dvd_pq_weak_ap hℓ hpq hqr hrs hp hq).2.2.2
```

A slightly cleaner variant avoids recomputing the propagation tuple in the last theorem:

```lean
theorem int_gcd_pq_eq_one_of_weak_ap'
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd p q = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hp hq
  rcases nat_prime_dvd_all_roots_of_dvd_pq_weak_ap hℓ hpq hqr hrs hp hq with
    ⟨hp', hq', hr', hs'⟩
  exact False.elim <|
    false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
      hroot hℓ hp' hq' hr' hs'
```

Use either `int_gcd_pq_eq_one_of_weak_ap` or the primed version, not both, if you want to avoid duplicate theorem clutter.

## Exact APIs used

These are the important current Mathlib APIs to check if your local snapshot differs:

```lean
#check Int.natCast_dvd
-- `((n : ℤ) ∣ x) ↔ n ∣ x.natAbs`; use `.mpr` from Nat divisibility to Int divisibility.

#check Int.Prime.dvd_pow
-- Nat prime `p`, integer divisibility `(p : ℤ) ∣ n^k` implies `p ∣ n.natAbs`.

#check pow_dvd_pow_of_dvd
-- Turns `(ℓ : ℤ) ∣ p` into `(ℓ : ℤ) ∣ p^2`.

#check Int.dvd_sub
#check Int.dvd_add
#check Nat.dvd_gcd
#check Nat.coprime_of_dvd'
#check Nat.coprime_iff_gcd_eq_one
#check Int.gcd_def
```

## How to extend

The same adjacent argument proves `Int.gcd q r = 1` and `Int.gcd r s = 1` by renaming variables / shifting the AP equations. The non-adjacent pairs are the remaining work:

* `(p,r)` and `(q,s)` need cancellation from `ℓ ∣ 2*Δ`; parity rules out `ℓ = 2`.
* `(p,s)` needs cancellation from `ℓ ∣ 3*Δ`, with a special `ZMod 3` finite-case branch when `ℓ = 3`.
