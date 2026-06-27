# Q1362 (dm1): coprime factor split of `5*B^4`

The lemma as stated is false over `ℤ`: you did not assume `0 < B`.  Take

```text
U = 1, V = 5, B = -1.
```

Then `U*V = 5*B^4`, `gcd(U,V)=1`, `U,V > 0`, and both are odd.  But the requested conclusion asks for `a > 0`, `b > 0`, and `a*b = B = -1`, impossible.

Here is a Lean counterexample to the exact statement shape.

```lean
import Mathlib

namespace DM1

/-- The requested integer split is false without `0 < B`. -/
theorem quartic_factor_split_statement_false :
    ¬ (∀ U V B : ℤ,
      U * V = 5 * B ^ 4 →
      Int.gcd U V = 1 →
      0 < U → 0 < V →
      Odd U → Odd V →
      ∃ a b : ℤ,
        0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ a * b = B ∧
        Odd a ∧ Odd b ∧
          ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
           (U = 5 * a ^ 4 ∧ V = b ^ 4))) := by
  intro h
  have hex :=
    h 1 5 (-1)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by exact ⟨0, by norm_num⟩)
      (by exact ⟨2, by norm_num⟩)
  rcases hex with ⟨a, b, ha, hb, _hgcd, hab, _haodd, _hbodd, _hsplit⟩
  have hpos : 0 < a * b := mul_pos ha hb
  rw [hab] at hpos
  norm_num at hpos

end DM1
```

## Corrected statement

In the descent context you have `0 < B`, so state the lemma with that hypothesis:

```lean
import Mathlib

namespace DM1

/-- Correct integer statement: add `0 < B`. -/
lemma quartic_factor_split_int_correct_statement
    {U V B : ℤ}
    (hUV : U * V = 5 * B ^ 4)
    (hcop : Int.gcd U V = 1)
    (hUpos : 0 < U) (hVpos : 0 < V) (hBpos : 0 < B)
    (hUodd : Odd U) (hVodd : Odd V) :
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ a * b = B ∧
      Odd a ∧ Odd b ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  -- This is the real unique-factorization/valuation lemma.
  -- Recommended implementation route:
  --   1. Convert to naturals using `U.natAbs`, `V.natAbs`, `B.natAbs`.
  --   2. Since `0 < U,V,B`, replace natAbs casts by the original integers at the end.
  --   3. Prove the Nat split with `Nat.factorization`.
  --   4. Cast the resulting Nat roots back to positive integers.
  -- This proof is not currently a one-line Mathlib lemma.
  sorry

end DM1
```

## Recommended Nat lemma to prove first

The cleanest formalization is a Nat lemma:

```lean
lemma quartic_factor_split_nat
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
  -- Proof outline:
  -- * Since `5 ∣ U*V`, `Nat.prime_five.dvd_mul` gives `5 ∣ U ∨ 5 ∣ V`.
  -- * Coprimality prevents `5` from dividing both.
  -- * If `5 ∣ V`, write `V = 5*V₀`; cancellation gives `U*V₀ = B^4`.
  -- * Since `U` and `V₀` are coprime, all prime exponents in each are multiples of 4.
  -- * Use `Nat.factorization` to build fourth roots `a,b` and prove `U=a^4`, `V₀=b^4`, `B=a*b`.
  -- * The `5 ∣ U` case is symmetric.
  sorry
```

The hard sublemma inside the Nat proof is:

```lean
lemma coprime_mul_eq_fourth_power
    {x y z : ℕ}
    (hxy : x * y = z ^ 4)
    (hcop : Nat.Coprime x y)
    (hx : 0 < x) (hy : 0 < y) :
    ∃ a b : ℕ, x = a ^ 4 ∧ y = b ^ 4 ∧ a * b = z := by
  -- Prove by `Nat.factorization`: for every prime p, the exponent of p
  -- in exactly one of x,y is the exponent in z^4, hence divisible by 4.
  sorry
```

So the answer is: add `0 < B`; otherwise the theorem is false.  Then prove the Nat factorization lemma first and transport it back to integers.
