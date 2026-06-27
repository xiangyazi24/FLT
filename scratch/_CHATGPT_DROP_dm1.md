# Q1426 (dm1/dm2): `UV_odd` for quartic descent

The clean proof is to prove the two factors are `Odd`, then convert back with `Int.odd_iff`.

Note that the `r % 2 = 1` hypothesis is actually unnecessary for this lemma: `2 * r^2` is even for every integer `r`.  I keep the hypothesis in the theorem statement for downstream compatibility.

```lean
import Mathlib

namespace DM2

abbrev U (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
abbrev V (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

lemma U_isOdd_of_B_odd {r B s : ℤ} (hB : B % 2 = 1) :
    Odd (U r B s) := by
  have hBodd : Odd B := Int.odd_iff.mpr hB
  have hB2odd : Odd (B ^ 2) := hBodd.pow
  have h2r_even : Even (2 * r ^ 2) := even_two_mul (r ^ 2)
  have h2s_even : Even (2 * s) := even_two_mul s
  have hsum_odd : Odd (2 * r ^ 2 + B ^ 2) :=
    h2r_even.add_odd hB2odd
  dsimp [U]
  change Odd ((2 * r ^ 2 + B ^ 2) - (2 * s))
  rw [Int.odd_sub]
  exact ⟨fun _ => h2s_even, fun _ => hsum_odd⟩

lemma V_isOdd_of_B_odd {r B s : ℤ} (hB : B % 2 = 1) :
    Odd (V r B s) := by
  have hBodd : Odd B := Int.odd_iff.mpr hB
  have hB2odd : Odd (B ^ 2) := hBodd.pow
  have h2r_even : Even (2 * r ^ 2) := even_two_mul (r ^ 2)
  have h2s_even : Even (2 * s) := even_two_mul s
  have hsum_odd : Odd (2 * r ^ 2 + B ^ 2) :=
    h2r_even.add_odd hB2odd
  dsimp [V]
  exact hsum_odd.add_even h2s_even

/-- Both quartic descent factors are odd. -/
theorem UV_odd {r B s : ℤ}
    (_hr : r % 2 = 1) (hB : B % 2 = 1) :
    (2 * r ^ 2 + B ^ 2 - 2 * s) % 2 = 1 ∧
      (2 * r ^ 2 + B ^ 2 + 2 * s) % 2 = 1 := by
  have hU : (U r B s) % 2 = 1 :=
    Int.odd_iff.mp (U_isOdd_of_B_odd (r := r) (B := B) (s := s) hB)
  have hV : (V r B s) % 2 = 1 :=
    Int.odd_iff.mp (V_isOdd_of_B_odd (r := r) (B := B) (s := s) hB)
  simpa [U, V] using And.intro hU hV

end DM2
```

The important API pieces are:

```lean
Int.odd_iff.mpr hB       -- from `B % 2 = 1` to `Odd B`
hBodd.pow               -- `Odd (B^2)`
even_two_mul (r ^ 2)    -- `Even (2*r^2)`
even_two_mul s          -- `Even (2*s)`
Even.add_odd            -- even + odd = odd
Odd.add_even            -- odd + even = odd
Int.odd_sub             -- odd - even = odd
```
