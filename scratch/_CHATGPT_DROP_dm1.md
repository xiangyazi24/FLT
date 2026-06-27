# Q1302 (dm1): if `n^3` is a square, then `n` is a square

Here is the Lean proof I would use. It uses `Nat.ceilRoot`, which is Mathlib's packaged factorization-root API: internally, `Nat.ceilRoot 2 a` rounds each prime exponent of `a` up after division by `2`, and the theorem `Nat.dvd_pow_iff_ceilRoot_dvd` is exactly the factorization/divisibility bridge.

The proof is shorter than manually constructing the product over `n.factorization`: if `n^3 = c^2`, then `n^2 ∣ c^2`; by the `ceilRoot` adjunction, `Nat.ceilRoot 2 (n^2) ∣ c`, hence `n ∣ c`. Write `c = n*d`; then cancel `n^2` from `n^3 = (n*d)^2` to get `n = d^2`.

```lean
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

namespace DM1

/-- If `n ≠ 0` and `n^3` is a square, then `n` is a square. -/
theorem isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases (isSquare_iff_exists_sq (n ^ 3)).1 h with ⟨c, hc⟩

  -- From `n^3 = c^2`, certainly `n^2 ∣ c^2`.
  have hndvd : n ^ 2 ∣ c ^ 2 := by
    rw [← hc]
    exact ⟨n, by ring⟩

  -- `Nat.ceilRoot 2 (n^2) = n`.
  have hceil : Nat.ceilRoot 2 (n ^ 2) = n := by
    simpa using
      (Nat.ceilRoot_pow_self (n := 2) (a := n)
        (by norm_num : (2 : ℕ) ≠ 0))

  -- The `ceilRoot` adjunction says `a ∣ b^2 ↔ ceilRoot 2 a ∣ b`.
  have hn_dvd_c : n ∣ c := by
    have hraw : Nat.ceilRoot 2 (n ^ 2) ∣ c :=
      ((Nat.dvd_pow_iff_ceilRoot_dvd
        (a := n ^ 2) (b := c) (n := 2)
        (by norm_num : (2 : ℕ) ≠ 0)).1 hndvd)
    simpa [hceil] using hraw

  rcases hn_dvd_c with ⟨d, rfl⟩

  -- Now `n^3 = (n*d)^2`; cancel `n^2` to get `n = d^2`.
  refine (isSquare_iff_exists_sq n).2 ⟨d, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.pos_of_ne_zero hn) 2)
  calc
    n ^ 2 * n = n ^ 3 := by ring
    _ = (n * d) ^ 2 := hc
    _ = n ^ 2 * d ^ 2 := by ring

end DM1
```

## Why this is the same valuation proof

`Nat.ceilRoot` is defined from the prime factorization of a natural number. In `Mathlib.Data.Nat.Factorization.Root`, the key simp lemma is

```lean
Nat.factorization_ceilRoot (n a : ℕ) :
  (Nat.ceilRoot n a).factorization = a.factorization ⌈/⌉ n
```

and the divisibility theorem used above is

```lean
Nat.dvd_pow_iff_ceilRoot_dvd (hn : n ≠ 0) :
  a ∣ b ^ n ↔ Nat.ceilRoot n a ∣ b
```

So the line proving `n ∣ c` is precisely the factorization argument: from `n^2 ∣ c^2`, every valuation of `n` is at most the corresponding valuation of `c`.
