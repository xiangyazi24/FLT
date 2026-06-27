# Q1386 (dm1/dm4): factor-splitting `U*V = 5*B^4`

## Answer

Use `Nat.factorization`, not the generic `UniqueFactorizationMonoid` interface.  The generic UFM API is mathematically right, but for this concrete arithmetic lemma over positive integers, `Nat.factorization` gives the cleanest Lean proof: every statement is a pointwise equality of exponents.

I do **not** know a packaged Mathlib theorem with this exact shape.  The key theorem to add locally is:

```lean
coprime_mul_eq_fourth_power
```

and then the `5*B^4` split is a short wrapper around it.

## Useful Mathlib API

```lean
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

-- Main APIs you want:
Nat.factorization
Nat.factorization_mul
Nat.factorization_pow
Nat.factorization_div
Nat.factorization_le_iff_dvd
Nat.Prime.factorization_self
Nat.factorization_pow_self
Nat.dvd_of_factorization_pos
Nat.Prime.dvd_mul
Nat.Coprime.of_dvd_right
Nat.Coprime.of_dvd_left
```

For reconstructing a number from its exponents, use:

```lean
Nat.prod_factorization_pow_eq_self
```

and/or the `factorizationEquiv` API if you build a new exponent function explicitly.

## Exact local theorem to prove first

This is the clean core lemma.  It says: if two coprime positive integers multiply to a fourth power, then each is a fourth power.

```lean
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace DM4

/--
Core UFD lemma.  Prove this by `Nat.factorization`.
-/
theorem coprime_mul_eq_fourth_power
    {x y z : ℕ}
    (hxy : x * y = z ^ 4)
    (hcop : Nat.Coprime x y)
    (hx : 0 < x) (hy : 0 < y) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      x = a ^ 4 ∧ y = b ^ 4 ∧ a * b = z := by
  -- Factorization proof plan:
  -- For every prime p:
  --   (x*y).factorization p = x.factorization p + y.factorization p
  --   (z^4).factorization p = 4 * z.factorization p
  --   coprimality implies not both x.factorization p and y.factorization p are positive.
  -- Hence each exponent is divisible by 4.
  -- Define a.factorization p = x.factorization p / 4,
  --        b.factorization p = y.factorization p / 4.
  -- Reconstruct using `Nat.prod_factorization_pow_eq_self` or `factorizationEquiv`.
  sorry

end DM4
```

This is the only genuinely UFD-heavy proof.  Everything below is case splitting and cancellation.

## Wrapper for `U*V = 5*B^4`

```lean
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace DM4

/--
Coprime split of `U*V = 5*B^4`.

The oddness assumptions are not needed for the fourth-power split itself; they are
useful later if you also want to prove `a,b` odd.
-/
theorem quartic_factor_split_nat
    {U V B : ℕ}
    (hUV : U * V = 5 * B ^ 4)
    (hcop : Nat.Coprime U V)
    (hUpos : 0 < U) (hVpos : 0 < V) (hBpos : 0 < B)
    (hUodd : Odd U) (hVodd : Odd V) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a * b = B ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  -- First, 5 divides one of U,V.
  have h5dvdUV : 5 ∣ U * V := by
    rw [hUV]
    exact dvd_mul_right 5 (B ^ 4)

  rcases Nat.prime_five.dvd_mul.mp h5dvdUV with h5U | h5V

  · -- Branch: `5 ∣ U`.
    rcases h5U with ⟨U0, hUeq⟩

    have hU0pos : 0 < U0 := by
      by_contra hnot
      have hU0 : U0 = 0 := Nat.eq_zero_of_not_pos hnot
      subst U0
      simp at hUeq
      omega

    have hU0V : U0 * V = B ^ 4 := by
      -- From `U=5*U0` and `U*V=5*B^4`, cancel the common factor `5`.
      -- A robust proof is:
      --   rewrite `hUeq` into `hUV`, normalize by `ring_nf`, then use
      --   `Nat.mul_left_cancel` with `5 ≠ 0`.
      sorry

    have hcopU0V : Nat.Coprime U0 V := by
      have hU0dvdU : U0 ∣ U := by
        refine ⟨5, ?_⟩
        rw [hUeq, mul_comm]
      exact Nat.Coprime.of_dvd_left hU0dvdU hcop

    rcases coprime_mul_eq_fourth_power hU0V hcopU0V hU0pos hVpos with
      ⟨a, b, ha_pos, hb_pos, hab_cop, hU0pow, hVpow, hab⟩

    refine ⟨a, b, ha_pos, hb_pos, hab_cop, hab, Or.inr ?_⟩
    constructor
    · rw [hUeq, hU0pow]
      ring
    · exact hVpow

  · -- Branch: `5 ∣ V`.
    rcases h5V with ⟨V0, hVeq⟩

    have hV0pos : 0 < V0 := by
      by_contra hnot
      have hV0 : V0 = 0 := Nat.eq_zero_of_not_pos hnot
      subst V0
      simp at hVeq
      omega

    have hUV0 : U * V0 = B ^ 4 := by
      -- From `V=5*V0` and `U*V=5*B^4`, cancel the common factor `5`.
      -- Same proof pattern as above with `Nat.mul_left_cancel`.
      sorry

    have hcopUV0 : Nat.Coprime U V0 := by
      have hV0dvdV : V0 ∣ V := by
        refine ⟨5, ?_⟩
        rw [hVeq, mul_comm]
      exact Nat.Coprime.of_dvd_right hV0dvdV hcop

    rcases coprime_mul_eq_fourth_power hUV0 hcopUV0 hUpos hV0pos with
      ⟨a, b, ha_pos, hb_pos, hab_cop, hUpow, hV0pow, hab⟩

    refine ⟨a, b, ha_pos, hb_pos, hab_cop, hab, Or.inl ?_⟩
    constructor
    · exact hUpow
    · rw [hVeq, hV0pow]
      ring

end DM4
```

The two small cancellation `sorry`s are not UFD facts; they are just Nat arithmetic.  The true proof obligation is still `coprime_mul_eq_fourth_power`.

## Factorization proof details for `coprime_mul_eq_fourth_power`

For a prime `p`, prove:

```lean
x.factorization p + y.factorization p = 4 * z.factorization p
```

using

```lean
Nat.factorization_mul hx.ne' hy.ne'
Nat.factorization_pow
```

Then use coprimality to prove:

```lean
x.factorization p = 0 ∨ y.factorization p = 0
```

because if both are positive, then `p ∣ x` and `p ∣ y` by

```lean
Nat.dvd_of_factorization_pos
```

contradicting `Nat.Coprime x y`.

So in each case the nonzero exponent is equal to `4 * z.factorization p` minus `0`, hence divisible by `4`.  That lets you define fourth roots with exponent functions

```lean
p ↦ x.factorization p / 4
p ↦ y.factorization p / 4
```

and reconstruct `a,b`.

## Integer version

For an integer statement with `0 < U,V,B`, first convert to Nat by `natAbs`:

```lean
Un := U.natAbs
Vn := V.natAbs
Bn := B.natAbs
```

Positivity rewrites the casts back to the original integers.  The unique-factorization content should remain entirely in the Nat theorem above.

## Bottom line

There is a clean API: **`Nat.factorization`**.  There is not a single packaged theorem for your exact split.  Add and prove this local theorem:

```lean
coprime_mul_eq_fourth_power
```

Then `quartic_factor_split_nat` is a short wrapper: split where the prime `5` goes, cancel `5`, apply the fourth-power lemma, and rebuild the desired disjunction.
