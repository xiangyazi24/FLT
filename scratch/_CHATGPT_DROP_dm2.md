# Lean drop: `IsSquare (q^3) → IsSquare q`

Complete Lean 4 proof, no `sorry`.

```lean
import Mathlib

namespace ScratchCubeSquare

/--
If a natural-number cube is a square, then the base is a square.

From `IsSquare (q^3)` we get `q^3 = d^2`.  Since `3` and `2` are coprime,
Mathlib's exponent-coprime power theorem gives `q = c^2`, hence `q` is a
square.
-/
lemma isSquare_of_isSquare_cube (q : ℕ) (h : IsSquare (q ^ 3)) :
    IsSquare q := by
  rcases h with ⟨d, hd⟩
  have hpow : q ^ 3 = d ^ 2 := by
    simpa [pow_two] using hd
  obtain ⟨c, hcq, _hcd⟩ :=
    Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
      (a := q) (b := d) (m := 3) (n := 2)
      (by decide : Nat.Coprime 3 2)
      hpow
  exact ⟨c, by simpa [pow_two] using hcq⟩

/-- The same result as an implication-shaped theorem. -/
lemma isSquare_cube_imp_isSquare {q : ℕ} :
    IsSquare (q ^ 3) → IsSquare q := by
  exact isSquare_of_isSquare_cube q

end ScratchCubeSquare
```
