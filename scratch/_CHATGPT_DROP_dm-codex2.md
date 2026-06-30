# Q2516 WeakPrimitiveAPPairwise final assembly route

This drop gives a paste-after-definitions assembly block for `WeakPrimitiveAPPairwise`, with distinct names.  It does two things:

1. gives a compile-oriented endpoint reduction from `Int.gcd p s ≠ 1` to a common prime divisor of `p` and `s`;
2. gives the final six-field assembly theorem, parameterized by the adjacent, distance-two, and endpoint component helpers.  If the Q2506/Q2512 helper signatures in your file are narrower, wrap them with lambdas and ignore the unused hypotheses.

The code assumes it is pasted inside the existing namespace `MazurProof.RationalPointsN12`, after the definitions of `rootGCD4` and `WeakPrimitiveAPPairwise`.

Required imports if not already present:

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
```

## Paste-after-definitions code

```lean
/-- If an integer gcd is not `1`, some natural prime divides both integers. -/
private theorem n12_common_prime_of_int_gcd_ne_one {a b : ℤ}
    (h : Int.gcd a b ≠ 1) :
    ∃ ℓ : ℕ, Nat.Prime ℓ ∧ (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b := by
  obtain ⟨ℓ, hℓprime, hℓdvd⟩ := Nat.exists_prime_and_dvd h
  have hga : Int.gcd a b ∣ a.natAbs := by
    rw [Int.gcd_def]
    exact Nat.gcd_dvd_left _ _
  have hgb : Int.gcd a b ∣ b.natAbs := by
    rw [Int.gcd_def]
    exact Nat.gcd_dvd_right _ _
  have hℓaNat : ℓ ∣ a.natAbs := hℓdvd.trans hga
  have hℓbNat : ℓ ∣ b.natAbs := hℓdvd.trans hgb
  have hℓa : (ℓ : ℤ) ∣ a := by
    rw [Int.natCast_dvd]
    exact hℓaNat
  have hℓb : (ℓ : ℤ) ∣ b := by
    rw [Int.natCast_dvd]
    exact hℓbNat
  exact ⟨ℓ, hℓprime, hℓa, hℓb⟩

/--
Endpoint gcd from the endpoint prime-propagation contradiction.

Use this after proving the genuine endpoint arithmetic lemma:
any natural prime dividing both endpoints `p` and `s` contradicts the AP equations
and primitive four-root gcd.  The prime-propagation proof is exactly where the
`ℓ ≠ 3` cancellation and `ℓ = 3` residue check belong.
-/
theorem n12_endpoint_ps_gcd_eq_one_of_no_common_prime
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1)
    (hp_odd : p % 2 = 1)
    (hs_odd : s % 2 = 1)
    (hprime :
      ∀ ℓ : ℕ,
        Nat.Prime ℓ →
        (ℓ : ℤ) ∣ p →
        (ℓ : ℤ) ∣ s →
          False) :
    Int.gcd p s = 1 := by
  -- Keep the endpoint AP/parity hypotheses visible for the local prime-propagation wrapper.
  have _hpq_keep := hpq
  have _hqr_keep := hqr
  have _hrs_keep := hrs
  have _hroot_keep := hroot
  have _hp_odd_keep := hp_odd
  have _hs_odd_keep := hs_odd
  by_contra hne
  obtain ⟨ℓ, hℓprime, hℓp, hℓs⟩ :=
    n12_common_prime_of_int_gcd_ne_one (a := p) (b := s) hne
  exact hprime ℓ hℓprime hℓp hℓs

/-- Uniform component-helper type for one pairwise gcd field. -/
private def N12PairwiseComponentHelper (i j : ℤ → ℤ → ℤ → ℤ → ℤ) : Prop :=
  ∀ {p q r s Δ : ℤ},
    q ^ 2 - p ^ 2 = Δ →
    r ^ 2 - q ^ 2 = Δ →
    s ^ 2 - r ^ 2 = Δ →
    rootGCD4 p q r s = 1 →
    p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
      Int.gcd (i p q r s) (j p q r s) = 1

/--
Final assembly of all six gcd fields.

Feed in the three adjacent helpers, two distance-two helpers, and the endpoint helper.
This theorem is deliberately parameterized so it is independent of the exact Q2506/Q2512
local theorem names.
-/
theorem n12_weakPrimitiveAPPairwise_from_component_helpers
    (hpq_pair :
      ∀ {p q r s Δ : ℤ},
        q ^ 2 - p ^ 2 = Δ →
        r ^ 2 - q ^ 2 = Δ →
        s ^ 2 - r ^ 2 = Δ →
        rootGCD4 p q r s = 1 →
        p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
          Int.gcd p q = 1)
    (hpr_pair :
      ∀ {p q r s Δ : ℤ},
        q ^ 2 - p ^ 2 = Δ →
        r ^ 2 - q ^ 2 = Δ →
        s ^ 2 - r ^ 2 = Δ →
        rootGCD4 p q r s = 1 →
        p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
          Int.gcd p r = 1)
    (hps_pair :
      ∀ {p q r s Δ : ℤ},
        q ^ 2 - p ^ 2 = Δ →
        r ^ 2 - q ^ 2 = Δ →
        s ^ 2 - r ^ 2 = Δ →
        rootGCD4 p q r s = 1 →
        p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
          Int.gcd p s = 1)
    (hqr_pair :
      ∀ {p q r s Δ : ℤ},
        q ^ 2 - p ^ 2 = Δ →
        r ^ 2 - q ^ 2 = Δ →
        s ^ 2 - r ^ 2 = Δ →
        rootGCD4 p q r s = 1 →
        p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
          Int.gcd q r = 1)
    (hqs_pair :
      ∀ {p q r s Δ : ℤ},
        q ^ 2 - p ^ 2 = Δ →
        r ^ 2 - q ^ 2 = Δ →
        s ^ 2 - r ^ 2 = Δ →
        rootGCD4 p q r s = 1 →
        p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
          Int.gcd q s = 1)
    (hrs_pair :
      ∀ {p q r s Δ : ℤ},
        q ^ 2 - p ^ 2 = Δ →
        r ^ 2 - q ^ 2 = Δ →
        s ^ 2 - r ^ 2 = Δ →
        rootGCD4 p q r s = 1 →
        p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
          Int.gcd r s = 1) :
    WeakPrimitiveAPPairwise := by
  intro p q r s Δ hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd
  exact
    ⟨ hpq_pair hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd
    , hpr_pair hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd
    , hps_pair hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd
    , hqr_pair hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd
    , hqs_pair hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd
    , hrs_pair hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd ⟩
```

## How to connect local Q2506/Q2512/Q2513 helpers

After your local endpoint prime-propagation helper is available, make a wrapper with this shape:

```lean
-- expected endpoint wrapper shape
-- theorem n12_endpoint_ps_pair
--     {p q r s Δ : ℤ}
--     (hpq : q ^ 2 - p ^ 2 = Δ)
--     (hqr : r ^ 2 - q ^ 2 = Δ)
--     (hrs : s ^ 2 - r ^ 2 = Δ)
--     (hroot : rootGCD4 p q r s = 1)
--     (hp_odd : p % 2 = 1)
--     (hs_odd : s % 2 = 1) :
--     Int.gcd p s = 1 :=
--   n12_endpoint_ps_gcd_eq_one_of_no_common_prime
--     hpq hqr hrs hroot hp_odd hs_odd
--     (fun ℓ hℓ hℓp hℓs =>
--       n12_endpoint_no_common_prime hpq hqr hrs hroot hp_odd hs_odd ℓ hℓ hℓp hℓs)
```

Then close the target by passing your five existing component wrappers plus `n12_endpoint_ps_pair` to
`n12_weakPrimitiveAPPairwise_from_component_helpers`.  If an adjacent or distance-two helper only needs a subset of the hypotheses, pass it through a lambda and ignore the rest.
