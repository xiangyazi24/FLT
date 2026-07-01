# Q2744: slope scale equations and coprime scale extraction

Target file: `FLT/Assumptions/MazurProof/N12ParamBridge.lean`.
Namespace: `MazurProof.RationalPointsN12`.

Important correction: the requested `eisenstein_scale_equations_of_slope` signature without a nonzero scale hypothesis is false. Example: take

```lean
X = 1, Y = 0, Z = -1, m = 1, n = 0, C = 0.
```

Then `EisensteinTriple X Y Z`, `Y = n*C`, and `Z+X = m*C` all hold, but

```lean
(2*m-n)*Z = -2 ≠ 0 = (m^2-m*n+n^2)*C.
```

In the intended positive slope application, `C` is nonzero, usually positive. The compile-ready lemma below adds `hC : C ≠ 0`.

## Code

```lean
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Algebraic scale equations from the reduced Eisenstein slope.

The extra hypothesis `C ≠ 0` is necessary: without it the statement is false. -/
theorem eisenstein_scale_equations_of_slope_of_ne_zero {X Y Z m n C : ℤ}
    (hC : C ≠ 0)
    (hE : EisensteinTriple X Y Z)
    (hY : Y = n * C)
    (hW : Z + X = m * C) :
    (2 * m - n) * Z = (m ^ 2 - m * n + n ^ 2) * C ∧
      (2 * m - n) * X = (m ^ 2 - n ^ 2) * C ∧
      (2 * m - n) * Y = (2 * m * n - n ^ 2) * C := by
  have hE0 : Z ^ 2 = X ^ 2 - X * Y + Y ^ 2 := by
    unfold EisensteinTriple at hE
    nlinarith [hE]
  have hXeq : X = m * C - Z := by
    nlinarith [hW]
  have hE1 :
      Z ^ 2 = (m * C - Z) ^ 2 - (m * C - Z) * (n * C) + (n * C) ^ 2 := by
    simpa [hXeq, hY] using hE0
  have h1zero :
      C * (((2 * m - n) * Z) - ((m ^ 2 - m * n + n ^ 2) * C)) = 0 := by
    nlinarith [hE1]
  have h1diff :
      ((2 * m - n) * Z) - ((m ^ 2 - m * n + n ^ 2) * C) = 0 := by
    exact (mul_eq_zero.mp h1zero).resolve_left hC
  have h1 : (2 * m - n) * Z = (m ^ 2 - m * n + n ^ 2) * C :=
    sub_eq_zero.mp h1diff
  refine ⟨h1, ?_, ?_⟩
  · calc
      (2 * m - n) * X
          = (2 * m - n) * (Z + X) - (2 * m - n) * Z := by ring
      _ = (2 * m - n) * (m * C) - (2 * m - n) * Z := by rw [hW]
      _ = (2 * m - n) * (m * C) - (m ^ 2 - m * n + n ^ 2) * C := by rw [h1]
      _ = (m ^ 2 - n ^ 2) * C := by ring
  · calc
      (2 * m - n) * Y
          = (2 * m - n) * (n * C) := by rw [hY]
      _ = (2 * m * n - n ^ 2) * C := by ring

/-- Positive-scale wrapper. -/
theorem eisenstein_scale_equations_of_slope_of_pos {X Y Z m n C : ℤ}
    (hCpos : 0 < C)
    (hE : EisensteinTriple X Y Z)
    (hY : Y = n * C)
    (hW : Z + X = m * C) :
    (2 * m - n) * Z = (m ^ 2 - m * n + n ^ 2) * C ∧
      (2 * m - n) * X = (m ^ 2 - n ^ 2) * C ∧
      (2 * m - n) * Y = (2 * m * n - n ^ 2) * C := by
  exact eisenstein_scale_equations_of_slope_of_ne_zero
    (ne_of_gt hCpos) hE hY hW

/-- If `a` and `b` are coprime and `a*C = b*X`, then the common scale is unique.

Divisibility orientation used here:
`hab.dvd_of_dvd_mul_left` consumes `a ∣ b * X` and returns `a ∣ X` from
`hab : IsCoprime a b`. -/
theorem coprime_mul_eq_mul_scale {a b C X : ℤ}
    (hab : IsCoprime a b) (ha : 0 < a) (hXpos : 0 < X)
    (h : a * C = b * X) :
    ∃ k : ℤ, 0 < k ∧ X = k * a ∧ C = k * b := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hadvd : a ∣ b * X := by
    refine ⟨C, ?_⟩
    exact h.symm
  have ha_dvd_X : a ∣ X := hab.dvd_of_dvd_mul_left hadvd
  rcases ha_dvd_X with ⟨k, hk⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · have hmulpos : 0 < a * k := by
      simpa [hk] using hXpos
    exact pos_of_mul_pos_left hmulpos (le_of_lt ha)
  · calc
      X = a * k := hk
      _ = k * a := by ring
  · have hCeq_mul : a * C = a * (k * b) := by
      calc
        a * C = b * X := h
        _ = b * (a * k) := by rw [hk]
        _ = a * (k * b) := by ring
    exact mul_left_cancel₀ ha_ne hCeq_mul

end MazurProof.RationalPointsN12
```

## If dot notation for the coprime API fails

Replace this line:

```lean
  have ha_dvd_X : a ∣ X := hab.dvd_of_dvd_mul_left hadvd
```

with the fully explicit form:

```lean
  have ha_dvd_X : a ∣ X := IsCoprime.dvd_of_dvd_mul_left hab hadvd
```

The orientation is: from `hab : IsCoprime a b`, a proof of `a ∣ b * X` gives `a ∣ X`.
