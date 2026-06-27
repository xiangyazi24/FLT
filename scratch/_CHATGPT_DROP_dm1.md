# Q1363 (dm1/dm2): Pythagorean extraction for the quartic descent

The Mathlib theorem you want for the useful output is

```lean
PythagoreanTriple.coprime_classification'
```

not the less convenient `isPrimitiveClassified_of_coprime`.  The important orientation is

```lean
PythagoreanTriple (b^2) h r
```

because `coprime_classification'` assumes the **first** leg is odd.  This gives `b^2 = m^2-n^2` and `h = 2mn` directly.

## Compilable extraction of `m,n`

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace DM2

/--
From `h^2 + b^4 = r^2`, with `gcd(h,b)=1`, `b` odd, and `r>0`,
extract the primitive Pythagorean parameters in the orientation needed for the descent:
`b^2 = m^2-n^2`, `h = 2mn`, `r = m^2+n^2`.
-/
lemma pythagorean_extract_mn
    {h b r : ℤ}
    (heq : h ^ 2 + b ^ 4 = r ^ 2)
    (hcop : Int.gcd h b = 1)
    (hbodd : b % 2 = 1)
    (hrpos : 0 < r) :
    ∃ m n : ℤ,
      b ^ 2 = m ^ 2 - n ^ 2 ∧
      h = 2 * m * n ∧
      r = m ^ 2 + n ^ 2 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      0 ≤ m := by
  have hpt : PythagoreanTriple (b ^ 2) h r := by
    dsimp [PythagoreanTriple]
    rw [show (b ^ 2) * (b ^ 2) + h * h = h ^ 2 + b ^ 4 by ring]
    rw [show r * r = r ^ 2 by ring]
    exact heq

  have hb_h_coprime : IsCoprime b h :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm

  have hcop_b2_h : Int.gcd (b ^ 2) h = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    simpa [sq] using (IsCoprime.mul_left hb_h_coprime hb_h_coprime)

  have hb2odd : (b ^ 2) % 2 = 1 := by
    rw [sq, Int.mul_emod, hbodd]
    decide

  exact hpt.coprime_classification' hcop_b2_h hb2odd hrpos

end DM2
```

## Factoring `(m-n)(m+n)=b^2`

After the previous lemma, you get

```lean
hb2_mn : b^2 = m^2 - n^2
hmn_gcd : Int.gcd m n = 1
hmn_parity : (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
```

Then the algebraic product is immediate:

```lean
have hprod : (m - n) * (m + n) = b ^ 2 := by
  rw [hb2_mn]
  ring
```

To apply `Int.sq_of_gcd_eq_one`, you still need to prove the standard coprime-factor lemma

```lean
have hcop_factors : Int.gcd (m - n) (m + n) = 1 := by
  -- from `hmn_gcd` and opposite parity `hmn_parity`
  -- any common divisor divides `2*m` and `2*n`; opposite parity removes the factor 2
  sorry
```

Then the square split starts as follows:

```lean
obtain ⟨u0, hu0 | hu0neg⟩ := Int.sq_of_gcd_eq_one hcop_factors hprod
```

The negative branch `m-n = -u0^2` is killed by the positivity lemma `0 < m-n`; similarly for `m+n`.  In the descent proof, prove these sign facts before the split:

```lean
have hmn_sub_pos : 0 < m - n := by
  -- from `b^2 = m^2-n^2 > 0` and the chosen orientation of the primitive triple
  sorry

have hmn_add_pos : 0 < m + n := by
  -- follows from `0 ≤ m` and the positivity/orientation facts from classification
  sorry
```

Once you have

```lean
hsub : m - n = u^2
hadd : m + n = v^2
```

the remaining identities are pure algebra:

```lean
have hb_sq_uv_sq : b ^ 2 = (u * v) ^ 2 := by
  calc
    b ^ 2 = (m - n) * (m + n) := hprod.symm
    _ = u ^ 2 * v ^ 2 := by rw [hsub, hadd]
    _ = (u * v) ^ 2 := by ring
```

With `0 < b`, `0 < u`, and `0 < v`, use `eq_or_eq_neg_of_sq_eq_sq` to get `b = u*v`:

```lean
have hb_uv : b = u * v := by
  rcases eq_or_eq_neg_of_sq_eq_sq b (u * v) hb_sq_uv_sq with h | h
  · exact h
  · exfalso
    have huv_pos : 0 < u * v := mul_pos hu_pos hv_pos
    rw [h] at hb_pos
    linarith
```

So: the Pythagorean parametrization block above is complete.  The later `u,v` split requires two additional local lemmas: `gcd(m-n,m+n)=1` and positivity of `m±n`; those are not produced directly by `coprime_classification'`.
