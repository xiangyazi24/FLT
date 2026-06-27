# Q1356 (dm1): `IsSquare (n : ℚ) ↔ IsSquare n`

Yes. The exact theorem is:

```lean
Rat.isSquare_intCast_iff {z : ℤ} : IsSquare (z : ℚ) ↔ IsSquare z
```

Import path:

```lean
import Mathlib.Data.Rat.Lemmas
```

It is tagged `[norm_cast, simp]`, so `simpa`/`norm_cast` can often use it automatically.

Related nearby facts in the same file:

```lean
Rat.isSquare_iff {q : ℚ} : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den
Rat.isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℚ) ↔ IsSquare n
Rat.isSquare_intCast_iff {z : ℤ} : IsSquare (z : ℚ) ↔ IsSquare z
```

Minimal use:

```lean
import Mathlib.Data.Rat.Lemmas

example {n : ℤ} : IsSquare (n : ℚ) ↔ IsSquare n :=
  Rat.isSquare_intCast_iff

example {n : ℤ} (h : IsSquare (n : ℚ)) : IsSquare n := by
  exact Rat.isSquare_intCast_iff.mp h
```

If your hypothesis is stated as an explicit rational square:

```lean
import Mathlib.Data.Rat.Lemmas

/-- If an integer is a square after casting to `ℚ`, it is already an integer square. -/
theorem int_isSquare_of_rat_isSquare {n : ℤ}
    (h : ∃ q : ℚ, q ^ 2 = (n : ℚ)) :
    ∃ c : ℤ, c ^ 2 = n := by
  have hsqQ : IsSquare (n : ℚ) := by
    rcases h with ⟨q, hq⟩
    exact ⟨q, by simpa [pow_two] using hq.symm⟩
  rcases (Rat.isSquare_intCast_iff.mp hsqQ) with ⟨c, hc⟩
  exact ⟨c, by simpa [pow_two] using hc.symm⟩
```

There is no need to manually use `Rat.num`, `Rat.den`, or `Rat.reduced` here; `Rat.isSquare_intCast_iff` is exactly the packaged version of that argument. Under the hood, the more general `Rat.isSquare_iff` says a rational is a square iff both its reduced numerator and denominator are squares.
