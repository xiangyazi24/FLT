# Q1491 (dm2/dm4): `MN_coprime_even` for the even branch

## Honest status

I do **not** want to claim I have a connector-verified, paste-and-compile proof here.  This lemma is long enough that it should be checked in the target Lean tree.  The important simplification is that the proposed ZMod-5 nonresidue argument is **not needed** for `gcd(U₁,V₁)=1`.

Once a prime `p` divides both `U₁` and `V₁`, we get

```text
p^2 ∣ U₁ * V₁ = 5 * B₁^4.
```

Then:

* if `p ∤ B₁`, `p ∣ 5`, hence `p = 5`; but `p^2 ∣ 5 * B₁^4` forces `p ∣ B₁`, contradiction.
* if `p ∣ B₁`, use `p ∣ U₁ + V₁ = r^2 + 2B₁^2` to get `p ∣ r^2`, hence `p ∣ r`; since `p ∣ B₁`, also `p ∣ 2B₁`, contradicting `Int.gcd r (2*B₁)=1`.

This avoids the quadratic-residue step entirely.  It is also more robust in Lean because it stays in divisibility/factorization instead of requiring field inverses in `ZMod 5`.

## Recommended decomposition

Define the normalized factors once:

```lean
import Mathlib

namespace QuarticPlusEven

noncomputable section

local notation "M" r B₁ s => ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / (4 : ℤ))
local notation "N" r B₁ s => ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / (4 : ℤ))
```

Then prove the division-normalization identities separately.

```lean
lemma MN_sum {r B₁ s : ℤ}
    (hdiv4U : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s))
    (hdiv4V : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s)) :
    M r B₁ s + N r B₁ s = r ^ 2 + 2 * B₁ ^ 2 := by
  rcases hdiv4U with ⟨u, hu⟩
  rcases hdiv4V with ⟨v, hv⟩
  have hM : M r B₁ s = u := by
    dsimp
    rw [hu, Int.mul_ediv_cancel_left]
    norm_num
  have hN : N r B₁ s = v := by
    dsimp
    rw [hv, Int.mul_ediv_cancel_left]
    norm_num
  rw [hM, hN]
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  calc
    (4 : ℤ) * (u + v)
        = (4 * u) + (4 * v) := by ring
    _ = (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) +
        (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) := by rw [← hu, ← hv]
    _ = 4 * (r ^ 2 + 2 * B₁ ^ 2) := by ring

lemma MN_diff {r B₁ s : ℤ}
    (hdiv4U : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s))
    (hdiv4V : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s)) :
    N r B₁ s - M r B₁ s = s := by
  rcases hdiv4U with ⟨u, hu⟩
  rcases hdiv4V with ⟨v, hv⟩
  have hM : M r B₁ s = u := by
    dsimp
    rw [hu, Int.mul_ediv_cancel_left]
    norm_num
  have hN : N r B₁ s = v := by
    dsimp
    rw [hv, Int.mul_ediv_cancel_left]
    norm_num
  rw [hM, hN]
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  calc
    (4 : ℤ) * (v - u)
        = (4 * v) - (4 * u) := by ring
    _ = (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) -
        (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) := by rw [← hv, ← hu]
    _ = 4 * s := by ring
```

The `MN_diff` identity is not actually needed for the gcd proof below, but it is useful to keep around.

## Divisibility helper for the contradiction with `gcd r (2*B₁)=1`

```lean
lemma prime_not_dvd_both_of_gcd_one
    {p : ℕ} (hp : p.Prime) {r B₁ : ℤ}
    (hcop : Int.gcd r (2 * B₁) = 1) :
    ¬ ((p : ℤ) ∣ r ∧ (p : ℤ) ∣ B₁) := by
  rintro ⟨hpr, hpB⟩
  have hp2B : (p : ℤ) ∣ 2 * B₁ := dvd_mul_of_dvd_right hpB 2
  have hpgcd : (p : ℤ) ∣ (Int.gcd r (2 * B₁) : ℤ) :=
    Int.dvd_coe_gcd hpr hp2B
  have hp1Z : (p : ℤ) ∣ (1 : ℤ) := by
    simpa [hcop] using hpgcd
  have hp1N : p ∣ (1 : ℕ) := by
    exact_mod_cast hp1Z
  exact hp.not_dvd_one hp1N
```

## Product-only replacement for the ZMod-5 nonresidue branch

This is the key simplification.  It says: if a prime divides both normalized factors, then it must divide `B₁`.

```lean
lemma common_prime_dvd_B₁
    {p : ℕ} (hp : p.Prime) {r B₁ s : ℤ}
    (hpM : (p : ℤ) ∣ M r B₁ s)
    (hpN : (p : ℤ) ∣ N r B₁ s)
    (hprod : M r B₁ s * N r B₁ s = 5 * B₁ ^ 4) :
    (p : ℤ) ∣ B₁ := by
  have hpMN : (p : ℤ) ^ 2 ∣ M r B₁ s * N r B₁ s := by
    rw [pow_two]
    exact mul_dvd_mul hpM hpN
  have hpRHS : (p : ℤ) ^ 2 ∣ 5 * B₁ ^ 4 := by
    simpa [hprod] using hpMN

  by_cases hpB : (p : ℤ) ∣ B₁
  · exact hpB

  have hp_prod_once : (p : ℤ) ∣ 5 * B₁ ^ 4 := by
    exact dvd_trans (dvd_mul_right (p : ℤ) (p : ℤ)) hpRHS

  have hp5_or_B4 : (p : ℤ) ∣ (5 : ℤ) ∨ (p : ℤ) ∣ B₁ ^ 4 :=
    Int.Prime.dvd_mul' hp hp_prod_once

  have hp5 : (p : ℤ) ∣ (5 : ℤ) := by
    rcases hp5_or_B4 with hp5 | hpB4
    · exact hp5
    · exact False.elim (hpB (Int.Prime.dvd_pow' hp hpB4))

  have hp_eq5 : p = 5 := by
    have hp5N : p ∣ (5 : ℕ) := by
      exact_mod_cast hp5
    exact hp.eq_of_dvd_of_prime (by norm_num) hp5N

  subst hp_eq5

  -- Now `25 ∣ 5 * B₁^4`; cancel one `5` to get `5 ∣ B₁^4`, hence `5 ∣ B₁`.
  have h25 : (25 : ℤ) ∣ 5 * B₁ ^ 4 := by
    simpa [pow_two] using hpRHS
  have h5B4 : (5 : ℤ) ∣ B₁ ^ 4 := by
    -- This is the small integer-cancellation step.
    -- A robust proof is:
    --   rcases h25 with ⟨k, hk⟩
    --   use k
    --   nlinarith
    rcases h25 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    nlinarith
  exact Int.Prime.dvd_pow' (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 5)) h5B4
```

Depending on the current imported namespace, the line

```lean
exact hp.eq_of_dvd_of_prime (by norm_num) hp5N
```

may need one of these equivalent variants:

```lean
exact Nat.Prime.eq_of_dvd_of_prime hp (by norm_num) hp5N
-- or simply:
have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by norm_num) hp5N
have hp_ge2 : 2 ≤ p := hp.two_le
omega
```

I would use the `omega` fallback if the method-name projection does not resolve.

## Main lemma

```lean
theorem MN_coprime_even {r B₁ s : ℤ} (hr : 0 < r) (hB₁ : 0 < B₁)
    (hcop : Int.gcd r (2 * B₁) = 1)
    (hr_odd : r % 2 = 1)
    (hprod : ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / 4) *
             ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / 4) = 5 * B₁ ^ 4)
    (hdiv4U : 4 ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s))
    (hdiv4V : 4 ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s)) :
    Int.gcd ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / 4)
            ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / 4) = 1 := by
  classical
  let M₁ : ℤ := M r B₁ s
  let V₁ : ℤ := N r B₁ s

  by_contra hg

  have hg' : Int.gcd M₁ V₁ ≠ 1 := by
    dsimp [M₁, V₁]
    simpa using hg

  obtain ⟨p, hp, hpdg⟩ := Nat.exists_prime_and_dvd hg'

  have hpdgZ : (p : ℤ) ∣ (Int.gcd M₁ V₁ : ℤ) := by
    exact_mod_cast hpdg

  have hpM : (p : ℤ) ∣ M₁ :=
    hpdgZ.trans (Int.gcd_dvd_left M₁ V₁)

  have hpV : (p : ℤ) ∣ V₁ :=
    hpdgZ.trans (Int.gcd_dvd_right M₁ V₁)

  have hpM0 : (p : ℤ) ∣ M r B₁ s := by
    simpa [M₁] using hpM

  have hpV0 : (p : ℤ) ∣ N r B₁ s := by
    simpa [V₁] using hpV

  have hpB : (p : ℤ) ∣ B₁ :=
    common_prime_dvd_B₁ hp hpM0 hpV0 hprod

  have hsum : M r B₁ s + N r B₁ s = r ^ 2 + 2 * B₁ ^ 2 :=
    MN_sum hdiv4U hdiv4V

  have hp_sum : (p : ℤ) ∣ r ^ 2 + 2 * B₁ ^ 2 := by
    have htmp : (p : ℤ) ∣ M r B₁ s + N r B₁ s := dvd_add hpM0 hpV0
    simpa [hsum] using htmp

  have hp_2Bsq : (p : ℤ) ∣ 2 * B₁ ^ 2 := by
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpB 2) 2

  have hp_rsq : (p : ℤ) ∣ r ^ 2 := by
    have := dvd_sub hp_sum hp_2Bsq
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  have hpr : (p : ℤ) ∣ r :=
    Int.Prime.dvd_pow' hp hp_rsq

  exact prime_not_dvd_both_of_gcd_one hp hcop ⟨hpr, hpB⟩

end
end QuarticPlusEven
```

## Notes on two likely API touch points

1. `Nat.exists_prime_and_dvd` accepts a natural `n ≠ 1` and returns a prime divisor.  Here the natural is `Int.gcd M₁ V₁`.

2. If `hp.eq_of_dvd_of_prime` does not resolve, replace the `p = 5` proof by:

```lean
have hp_eq5 : p = 5 := by
  have hp5N : p ∣ (5 : ℕ) := by exact_mod_cast hp5
  have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by norm_num) hp5N
  have hp_ge2 : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at hp
```

or use `omega` after `hp_le5`, `hp_ge2`, and `hp5N`.

## Why this is better than the ZMod-5 route

The ZMod argument is mathematically correct, but it is unnecessary for gcd.  Since a common prime divides both factors, its **square** divides the product.  The product is `5 * B₁^4`.  If the prime is not already in `B₁`, the only possible prime is `5`, but then the square divisibility would force another factor of `5` into `B₁^4`, contradiction.  This is the cleanest Lean route.
