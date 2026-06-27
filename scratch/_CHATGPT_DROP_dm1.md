# Q1370 (dm1/dm2): exact factor-split `sorry`

Mathlib has the machinery, but I do not know of a packaged theorem with exactly this statement.

Use the Nat factorization API, not `Associates`, for this local descent lemma.  The relevant import is:

```lean
import Mathlib.Data.Nat.Factorization.Basic
```

Useful API names:

```lean
Nat.factorization
Nat.factorization_mul
Nat.factorization_pow
Nat.factorization_div
Nat.factorization_le_iff_dvd
Nat.Prime.factorization_self
Nat.factorization_pow_self
Nat.Prime.dvd_mul
Nat.Coprime
Nat.Coprime.dvd_mul_left
Nat.Coprime.dvd_mul_right
```

There is no one-line `coprime_factors_of_five_fourth_power` theorem.  The exact `sorry` should be the Nat split lemma below.  After this Nat lemma exists, the integer statement is just transport through `natAbs` using the positivity hypotheses.

## Exact `sorry` to isolate

```lean
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace DM2

/--
Nat version of the coprime factor split.

This is the exact UFD/factorization lemma to prove by `Nat.factorization`.
It packages: the prime `5` goes to exactly one side, and all other exponents
are multiples of `4`.
-/
theorem quartic_factor_split_nat
    {U V B : ℕ}
    (hUV : U * V = 5 * B ^ 4)
    (hcop : Nat.Coprime U V)
    (hUpos : 0 < U) (hVpos : 0 < V) (hBpos : 0 < B)
    (hUodd : Odd U) (hVodd : Odd V) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a * b = B ∧
      Odd a ∧ Odd b ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  -- Exact proof plan:
  -- 1. Split on `Nat.Prime.dvd_mul Nat.prime_five` applied to `5 ∣ U*V`.
  -- 2. Coprimality rules out `5 ∣ U` and `5 ∣ V` simultaneously.
  -- 3. In the branch `5 ∣ V`, write `V = 5*V₀` and cancel `5` from
  --      U*V = 5*B^4
  --    to get `U*V₀ = B^4`.
  -- 4. Prove `Nat.Coprime U V₀` from `Nat.Coprime U V` and `V₀ ∣ V`.
  -- 5. Apply the internal lemma `coprime_mul_eq_fourth_power`:
  --      if x*y=z^4 and gcd(x,y)=1, then x=a^4, y=b^4, a*b=z.
  -- 6. The branch `5 ∣ U` is symmetric.
  -- 7. Oddness of `a,b` follows from `a*b=B` and oddness of `B`, itself
  --    obtained from oddness of `U*V = 5*B^4`.
  sorry

/--
The inner factorization lemma.  This is often the best first target.

For every prime `p`, use
`Nat.factorization_mul`, `Nat.factorization_pow`, and coprimality to show the
exponent of `p` in `x` or `y` is a multiple of `4`; then reconstruct fourth
roots from the divided exponent functions.
-/
theorem coprime_mul_eq_fourth_power
    {x y z : ℕ}
    (hxy : x * y = z ^ 4)
    (hcop : Nat.Coprime x y)
    (hx : 0 < x) (hy : 0 < y) :
    ∃ a b : ℕ,
      x = a ^ 4 ∧ y = b ^ 4 ∧ a * b = z := by
  -- This is the core `Nat.factorization` proof.
  -- For each prime p:
  --   factorization(x*y)(p) = factorization(x)(p)+factorization(y)(p)
  --   factorization(z^4)(p) = 4*factorization(z)(p)
  --   coprime x y implies at most one of factorization(x)(p), factorization(y)(p)
  --   is nonzero.
  -- Hence both exponents are divisible by 4, and the quotient exponents define
  -- `a` and `b`.
  sorry

end DM2
```

## Integer statement using that exact Nat lemma

The integer version should be stated with `0 < B`; otherwise `a*b=B` with `a,b>0` is false for negative `B`.

```lean
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace DM2

/-- Integer version.  Prove by transporting `quartic_factor_split_nat`. -/
theorem quartic_factor_split_int
    {U V B : ℤ}
    (hUV : U * V = 5 * B ^ 4)
    (hcop : Int.gcd U V = 1)
    (hUpos : 0 < U) (hVpos : 0 < V) (hBpos : 0 < B)
    (hUodd : Odd U) (hVodd : Odd V) :
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ a * b = B ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  -- Transport route:
  --   let Un := U.natAbs, Vn := V.natAbs, Bn := B.natAbs.
  --   hUpos/hVpos/hBpos identify casts of these natAbs values with U,V,B.
  --   Convert hUV to `Un*Vn = 5*Bn^4`.
  --   Convert hcop to `Nat.Coprime Un Vn`.
  --   Apply `quartic_factor_split_nat`.
  --   Return `a,b : ℤ` by casting the Nat witnesses.
  -- This is routine but verbose cast bookkeeping; the unique-factorization
  -- content is entirely in `quartic_factor_split_nat` above.
  sorry

end DM2
```

## Bottom line

Mathlib has the factorization primitives, but not the exact descent lemma.  The exact proof obligation to isolate is:

```lean
quartic_factor_split_nat
```

and inside it the only genuinely hard sublemma is:

```lean
coprime_mul_eq_fourth_power
```
