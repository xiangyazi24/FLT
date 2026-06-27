# Q1539 (dm2/dm3): clean statement for the even-branch `gcd(M,N)=1`

## Recommendation

Use **(a)**: state a reusable core lemma with `M,N` as explicit integer parameters and with the already-normalized identities as hypotheses.

Do **not** make the main gcd lemma mention `/4`.  Integer division is irrelevant to the prime-divisor argument once you know the normalized identities:

```lean
hprod : M * N = 5 * B₁ ^ 4
hsum  : M + N = r ^ 2 + 2 * B₁ ^ 2
hcop  : Int.gcd r (2 * B₁) = 1
```

The raw `/4` theorem should be a thin wrapper proving `hsum` from divisibility by `4`, then calling the core lemma.

You also do **not** need `N - M = s` for this gcd proof.  The product and sum identities suffice.

## Core theorem statement

```lean
import Mathlib

namespace QuarticPlusEvenCoprime

/-- Core prime-divisor argument for the even branch.

If `M*N = 5*B₁^4`, `M+N = r^2 + 2B₁^2`, and `gcd(r,2B₁)=1`, then
`M,N` are coprime.  This is the theorem to prove and reuse. -/
theorem MN_coprime_core {M N r B₁ : ℤ}
    (hprod : M * N = 5 * B₁ ^ 4)
    (hsum : M + N = r ^ 2 + 2 * B₁ ^ 2)
    (hcop : Int.gcd r (2 * B₁) = 1) :
    Int.gcd M N = 1 := by
  classical

  /- Helper: a prime common divisor of `M,N` must divide `B₁`.
     Reason: p² | M*N = 5B₁⁴. If p ∤ B₁, then p|5, so p=5; but then
     p² | 5B₁⁴ forces p|B₁⁴, hence p|B₁, contradiction. -/
  have common_prime_dvd_B₁ :
      ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ M → (p : ℤ) ∣ N → (p : ℤ) ∣ B₁ := by
    intro p hp hpM hpN
    have hp2MN : (p : ℤ) ^ 2 ∣ M * N := by
      rw [pow_two]
      exact mul_dvd_mul hpM hpN
    have hp2RHS : (p : ℤ) ^ 2 ∣ 5 * B₁ ^ 4 := by
      simpa [hprod] using hp2MN

    by_cases hpB : (p : ℤ) ∣ B₁
    · exact hpB

    have hpRHS : (p : ℤ) ∣ 5 * B₁ ^ 4 := by
      exact dvd_trans (by rw [pow_two]; exact dvd_mul_right (p : ℤ) (p : ℤ)) hp2RHS

    have hp5_or_B4 : (p : ℤ) ∣ (5 : ℤ) ∨ (p : ℤ) ∣ B₁ ^ 4 :=
      Int.Prime.dvd_mul' hp hpRHS

    have hp5 : (p : ℤ) ∣ (5 : ℤ) := by
      rcases hp5_or_B4 with hp5 | hpB4
      · exact hp5
      · exact False.elim (hpB (Int.Prime.dvd_pow' hp hpB4))

    have hp_eq5 : p = 5 := by
      have hp5N : p ∣ (5 : ℕ) := by
        exact_mod_cast hp5
      have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by norm_num) hp5N
      have hp_ge2 : 2 ≤ p := hp.two_le
      interval_cases p <;> norm_num at hp5N hp

    subst hp_eq5

    have h25 : (25 : ℤ) ∣ 5 * B₁ ^ 4 := by
      simpa [pow_two] using hp2RHS

    have h5B4 : (5 : ℤ) ∣ B₁ ^ 4 := by
      rcases h25 with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      nlinarith

    exact False.elim
      (hpB (Int.Prime.dvd_pow' (by norm_num : Nat.Prime 5) h5B4))

  by_contra hg

  have hg_ne : Int.gcd M N ≠ 1 := hg
  obtain ⟨p, hp, hpdg⟩ := Nat.exists_prime_and_dvd hg_ne

  have hpdgZ : (p : ℤ) ∣ (Int.gcd M N : ℤ) := by
    exact_mod_cast hpdg

  have hpM : (p : ℤ) ∣ M :=
    hpdgZ.trans (Int.gcd_dvd_left M N)

  have hpN : (p : ℤ) ∣ N :=
    hpdgZ.trans (Int.gcd_dvd_right M N)

  have hpB : (p : ℤ) ∣ B₁ :=
    common_prime_dvd_B₁ hp hpM hpN

  have hp_sum : (p : ℤ) ∣ r ^ 2 + 2 * B₁ ^ 2 := by
    have hMNsum : (p : ℤ) ∣ M + N := dvd_add hpM hpN
    simpa [hsum] using hMNsum

  have hp_2Bsq : (p : ℤ) ∣ 2 * B₁ ^ 2 := by
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpB 2) 2

  have hp_rsq : (p : ℤ) ∣ r ^ 2 := by
    have hsub := dvd_sub hp_sum hp_2Bsq
    convert hsub using 1 <;> ring

  have hpr : (p : ℤ) ∣ r :=
    Int.Prime.dvd_pow' hp hp_rsq

  have hp2B : (p : ℤ) ∣ 2 * B₁ :=
    dvd_mul_of_dvd_right hpB 2

  have hpgcd : (p : ℤ) ∣ (Int.gcd r (2 * B₁) : ℤ) :=
    Int.dvd_coe_gcd hpr hp2B

  have hp1Z : (p : ℤ) ∣ (1 : ℤ) := by
    simpa [hcop] using hpgcd

  have hp1N : p ∣ (1 : ℕ) := by
    exact_mod_cast hp1Z

  exact hp.not_dvd_one hp1N
```

## Wrapper theorem for the raw `/4` expressions

This is where integer division belongs.  Prove the sum identity once, then call `MN_coprime_core`.

```lean
/-- Sum identity for the raw even-branch normalized factors. -/
lemma MN_sum_raw {r B₁ s : ℤ}
    (hdiv4U : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s))
    (hdiv4V : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s)) :
    ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / 4) +
      ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / 4) =
        r ^ 2 + 2 * B₁ ^ 2 := by
  rcases hdiv4U with ⟨u, hu⟩
  rcases hdiv4V with ⟨v, hv⟩

  have hU : ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / 4) = u := by
    rw [hu, Int.mul_ediv_cancel_left]
    norm_num

  have hV : ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / 4) = v := by
    rw [hv, Int.mul_ediv_cancel_left]
    norm_num

  rw [hU, hV]
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  calc
    (4 : ℤ) * (u + v)
        = 4 * u + 4 * v := by ring
    _ = (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) +
        (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) := by
          rw [← hu, ← hv]
    _ = 4 * (r ^ 2 + 2 * B₁ ^ 2) := by ring

/-- Raw-expression version.  Notice the unused hypotheses from the original mathematical setup
are absent: once `hprod` is supplied, the gcd proof only needs `hcop`, `hprod`, and divisibility
by `4` to derive the sum identity. -/
theorem MN_coprime_raw {r B₁ s : ℤ}
    (hcop : Int.gcd r (2 * B₁) = 1)
    (hprod : ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / 4) *
             ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / 4) = 5 * B₁ ^ 4)
    (hdiv4U : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s))
    (hdiv4V : (4 : ℤ) ∣ (2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s)) :
    Int.gcd ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / 4)
            ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / 4) = 1 := by
  exact MN_coprime_core
    (M := ((2 * r ^ 2 + (2 * B₁) ^ 2 - 2 * s) / 4))
    (N := ((2 * r ^ 2 + (2 * B₁) ^ 2 + 2 * s) / 4))
    (r := r) (B₁ := B₁)
    hprod
    (MN_sum_raw hdiv4U hdiv4V)
    hcop

end QuarticPlusEvenCoprime
```

## Why this is the cleanest shape

### (a) Explicit `M,N` parameters + product/sum hypotheses

This is best.  The prime-divisor argument is algebraic and does not care that `M,N` came from `/4`.

### (b) Raw `U/4,V/4` expressions

Use only as a wrapper.  It is ugly because every divisibility and gcd line now carries large expressions.

### (c) Reuse `UV_coprime` directly

Do not do this directly.  The raw `U,V` in the even branch have a forced common factor `4`, so the original `UV_coprime` statement is the wrong abstraction.  Reuse the **same proof pattern**, not the theorem itself.

## Minimal hypotheses

After normalization, the core lemma does not need:

```lean
4 ∣ B
r odd
s odd
s² = r⁴ + r²B² - B⁴
N - M = s
```

Those are only needed upstream to prove `hprod`, `hdiv4U`, `hdiv4V`, and perhaps positivity/descent inequalities.  The gcd proof needs only:

```lean
M * N = 5 * B₁ ^ 4
M + N = r ^ 2 + 2 * B₁ ^ 2
Int.gcd r (2 * B₁) = 1
```
