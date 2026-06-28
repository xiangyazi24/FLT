# Q1785 (dm1): parity proof for the even product case

Here is the short proof I would paste.  It avoids modular API and just splits `a` and `b` by `Int.even_or_odd`.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.GCD

example {a b j k : ℤ}
    (hab : a * b = 2 * k)
    (hcop : Int.gcd a b = 1) :
    (2 : ℤ) ∣ ((2 * j + 1) - (a ^ 2 - b ^ 2)) := by
  classical

  -- Split `a` into `2*x` or `2*x+1`.
  obtain ⟨x, hx_even | hx_odd⟩ := Int.even_or_odd a

  · -- a = 2*x
    obtain ⟨y, hy_even | hy_odd⟩ := Int.even_or_odd b

    · -- b = 2*y: impossible, since then 2 divides gcd(a,b)=1.
      exfalso

      have h2a : (2 : ℤ) ∣ a := by
        refine ⟨x, ?_⟩
        rw [hx_even]
        ring

      have h2b : (2 : ℤ) ∣ b := by
        refine ⟨y, ?_⟩
        rw [hy_even]
        ring

      have h2g : (2 : ℤ) ∣ (Int.gcd a b : ℤ) := by
        exact Int.dvd_gcd h2a h2b

      have h21 : (2 : ℤ) ∣ (1 : ℤ) := by
        simpa [hcop] using h2g

      norm_num at h21

    · -- a = 2*x, b = 2*y+1.  Then odd - (even - odd) is even.
      refine ⟨j - 2 * x ^ 2 + 2 * y ^ 2 + 2 * y + 1, ?_⟩
      rw [hx_even, hy_odd]
      ring

  · -- a = 2*x+1
    obtain ⟨y, hy_even | hy_odd⟩ := Int.even_or_odd b

    · -- a = 2*x+1, b = 2*y.  Then odd - (odd - even) is even.
      refine ⟨j - 2 * x ^ 2 - 2 * x + 2 * y ^ 2, ?_⟩
      rw [hx_odd, hy_even]
      ring

    · -- both odd: impossible because a*b would be odd but `a*b = 2*k`.
      exfalso

      let t : ℤ := 2 * x * y + x + y

      have hpar : 2 * t + 1 = 2 * k := by
        calc
          2 * t + 1 = a * b := by
            dsimp [t]
            rw [hx_odd, hy_odd]
            ring
          _ = 2 * k := hab

      omega
```

If your local `Int.even_or_odd` has the alternative disjunction-of-existentials shape, replace the first split by:

```lean
rcases Int.even_or_odd a with ⟨x, hx_even⟩ | ⟨x, hx_odd⟩
```

and similarly for `b`; the four branch bodies are unchanged.

For the exact context with `B₁ = a*b` and `B₁ = 2*k`, first make the product equality:

```lean
have hab2 : a * b = 2 * k := by
  rw [← hB₁_ab, hB₁_val]
```

then call the proof above with `hab := hab2`.