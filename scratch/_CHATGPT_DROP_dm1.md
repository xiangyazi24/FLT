# Q1312 (dm1/dm3): rational square of an integer is an integer square

A direct `Rat.num` proof is enough: `Rat.mul_self_num` is the Mathlib lemma that packages the reduced numerator/denominator argument using `Rat.reduced`.

```lean
import Mathlib.Data.Rat.Lemmas

namespace DM3

/-- If a nonnegative integer is a square in `ℚ`, then it is a square in `ℤ`. -/
theorem int_square_of_rat_square {n : ℤ} (_hn : 0 ≤ n)
    (h : ∃ q : ℚ, q ^ 2 = (n : ℚ)) :
    ∃ c : ℤ, c ^ 2 = n := by
  rcases h with ⟨q, hq⟩
  refine ⟨q.num, ?_⟩
  have hnum := congrArg Rat.num hq
  simpa [pow_two, Rat.mul_self_num, Rat.num_intCast] using hnum

end DM3
```

The nonnegativity hypothesis is harmless but not needed by the proof: the existence of `q : ℚ` with `q^2 = (n : ℚ)` already forces nonnegativity.
