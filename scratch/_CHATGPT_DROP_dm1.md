# Q497 (dm1): diagonal-difference lemma for `PowerSeries.subst`

## Executive answer

The clean Lean atom is stronger than divisibility: define the explicit bivariate divided-difference quotient

```lean
Q(e0,e1) = coeff f (e0 + e1 + 1)
```

as a two-variable `MvPowerSeries`.  Then prove coefficientwise

```lean
f(X0) - f(X1) = (X0 - X1) * Q.
```

This avoids the proposed `dvd_sum` proof.  The `dvd_sum` idea is mathematically fine for polynomial truncations, but the actual power-series expression is an infinite sum, so a finite `dvd_sum` proof does not directly apply.  The coefficientwise quotient is the safer Lean statement.

The proof below uses current Mathlib APIs:

* `PowerSeries.subst` and `PowerSeries.coeff_subst_single` from `Mathlib.RingTheory.PowerSeries.Substitution`.
* `MvPowerSeries.X_def` and `MvPowerSeries.coeff_monomial_mul` from `Mathlib.RingTheory.MvPowerSeries.Basic`.

I could not run Lean in this environment, so this is written as a complete Lean file but may need small local repairs if the exact current imported theorem argument names differ in the target checkout.

---

## Complete Lean file

```lean
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

open scoped PowerSeries

namespace DiagonalDifferencePowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The explicit bivariate divided-difference quotient for
`f(X₀)-f(X₁)`.  Its coefficient at `X₀^i X₁^j` is `coeff f (i+j+1)`.

Mathematically:

`dividedDiff f = Σ_{i,j≥0} a_{i+j+1} X₀^i X₁^j`.
-/
def dividedDiff (f : R⟦X⟧) : MvPowerSeries (Fin 2) R :=
  fun e => PowerSeries.coeff (e (0 : Fin 2) + e (1 : Fin 2) + 1) f

@[simp]
lemma coeff_dividedDiff (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (dividedDiff f) =
      PowerSeries.coeff (e (0 : Fin 2) + e (1 : Fin 2) + 1) f := by
  rfl

/-- Coefficients of `f(X₀)`. -/
lemma coeff_subst_X0 (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) f) =
      if e (1 : Fin 2) = 0 then PowerSeries.coeff (e (0 : Fin 2)) f else 0 := by
  classical
  rw [PowerSeries.coeff_subst_single (s := (0 : Fin 2)) (f := f) (e := e)]
  by_cases h1 : e (1 : Fin 2) = 0
  · have he : e = Finsupp.single (0 : Fin 2) (e (0 : Fin 2)) := by
      ext i
      fin_cases i <;> simp [h1]
    simp [he, h1]
  · have hne : e ≠ Finsupp.single (0 : Fin 2) (e (0 : Fin 2)) := by
      intro he
      apply h1
      have h := congrArg (fun p : Fin 2 →₀ ℕ => p (1 : Fin 2)) he
      simpa using h
    simp [hne, h1]

/-- Coefficients of `f(X₁)`. -/
lemma coeff_subst_X1 (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f) =
      if e (0 : Fin 2) = 0 then PowerSeries.coeff (e (1 : Fin 2)) f else 0 := by
  classical
  rw [PowerSeries.coeff_subst_single (s := (1 : Fin 2)) (f := f) (e := e)]
  by_cases h0 : e (0 : Fin 2) = 0
  · have he : e = Finsupp.single (1 : Fin 2) (e (1 : Fin 2)) := by
      ext i
      fin_cases i <;> simp [h0]
    simp [he, h0]
  · have hne : e ≠ Finsupp.single (1 : Fin 2) (e (1 : Fin 2)) := by
      intro he
      apply h0
      have h := congrArg (fun p : Fin 2 →₀ ℕ => p (0 : Fin 2)) he
      simpa using h
    simp [hne, h0]

/-- Coefficients of `X₀ * dividedDiff f`. -/
lemma coeff_X0_mul_dividedDiff (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) * dividedDiff f) =
      if e (0 : Fin 2) = 0 then 0
      else PowerSeries.coeff (e (0 : Fin 2) + e (1 : Fin 2)) f := by
  classical
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases hle : Finsupp.single (0 : Fin 2) 1 ≤ e
  · have h0 : e (0 : Fin 2) ≠ 0 := by
      have hh := hle (0 : Fin 2)
      simpa using hh
    have hsum :
        (e - Finsupp.single (0 : Fin 2) 1) (0 : Fin 2) +
            (e - Finsupp.single (0 : Fin 2) 1) (1 : Fin 2) + 1 =
          e (0 : Fin 2) + e (1 : Fin 2) := by
      simp [Finsupp.sub_apply]
      omega
    simp [dividedDiff, hle, h0, hsum]
  · have h0 : e (0 : Fin 2) = 0 := by
      by_contra h0
      apply hle
      intro i
      fin_cases i
      · simpa [Nat.succ_le_iff] using Nat.pos_iff_ne_zero.mpr h0
      · simp
    simp [dividedDiff, hle, h0]

/-- Coefficients of `X₁ * dividedDiff f`. -/
lemma coeff_X1_mul_dividedDiff (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) * dividedDiff f) =
      if e (1 : Fin 2) = 0 then 0
      else PowerSeries.coeff (e (0 : Fin 2) + e (1 : Fin 2)) f := by
  classical
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases hle : Finsupp.single (1 : Fin 2) 1 ≤ e
  · have h1 : e (1 : Fin 2) ≠ 0 := by
      have hh := hle (1 : Fin 2)
      simpa using hh
    have hsum :
        (e - Finsupp.single (1 : Fin 2) 1) (0 : Fin 2) +
            (e - Finsupp.single (1 : Fin 2) 1) (1 : Fin 2) + 1 =
          e (0 : Fin 2) + e (1 : Fin 2) := by
      simp [Finsupp.sub_apply]
      omega
    simp [dividedDiff, hle, h1, hsum]
  · have h1 : e (1 : Fin 2) = 0 := by
      by_contra h1
      apply hle
      intro i
      fin_cases i
      · simp
      · simpa [Nat.succ_le_iff] using Nat.pos_iff_ne_zero.mpr h1
    simp [dividedDiff, hle, h1]

/-- Strong form: the explicit quotient identity. -/
theorem subst_X0_subst_X1_eq_mul_dividedDiff (f : R⟦X⟧) :
    PowerSeries.subst
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) f -
      PowerSeries.subst
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f =
      ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) -
          MvPowerSeries.X (1 : Fin 2)) * dividedDiff f := by
  classical
  have hcoeff :
      PowerSeries.subst
          (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) f -
        PowerSeries.subst
          (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f =
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) * dividedDiff f -
          (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) * dividedDiff f := by
    ext e
    simp only [map_sub]
    by_cases h0 : e (0 : Fin 2) = 0
    · by_cases h1 : e (1 : Fin 2) = 0
      · simp [coeff_subst_X0, coeff_subst_X1, coeff_X0_mul_dividedDiff,
          coeff_X1_mul_dividedDiff, h0, h1]
      · have hsum : e (0 : Fin 2) + e (1 : Fin 2) = e (1 : Fin 2) := by
          omega
        simp [coeff_subst_X0, coeff_subst_X1, coeff_X0_mul_dividedDiff,
          coeff_X1_mul_dividedDiff, h0, h1, hsum]
    · by_cases h1 : e (1 : Fin 2) = 0
      · have hsum : e (0 : Fin 2) + e (1 : Fin 2) = e (0 : Fin 2) := by
          omega
        simp [coeff_subst_X0, coeff_subst_X1, coeff_X0_mul_dividedDiff,
          coeff_X1_mul_dividedDiff, h0, h1, hsum]
      · simp [coeff_subst_X0, coeff_subst_X1, coeff_X0_mul_dividedDiff,
          coeff_X1_mul_dividedDiff, h0, h1]
  simpa [sub_mul] using hcoeff

/-- The requested divisibility lemma. -/
theorem subst_X0_subst_X1_dvd (f : R⟦X⟧) :
    ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) -
        MvPowerSeries.X (1 : Fin 2)) ∣
      PowerSeries.subst
          (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) f -
        PowerSeries.subst
          (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f := by
  exact ⟨dividedDiff f, subst_X0_subst_X1_eq_mul_dividedDiff f⟩

end

end DiagonalDifferencePowerSeries
```

---

## Notes for integration

1. The quotient is canonical for the sign convention in the theorem:

```lean
f(X0) - f(X1) = (X0 - X1) * dividedDiff f
```

If the target later uses `X1 - X0`, the quotient should be negated.

2. This is stronger than the requested lemma and more useful for the formal-group normalization step, because it gives the actual quotient series.

3. If a local Mathlib checkout complains about the argument names of `PowerSeries.coeff_subst_single`, replace the two rewrites by:

```lean
simpa using
  PowerSeries.coeff_subst_single
    (s := (0 : Fin 2)) (f := f) (e := e)
```

and analogously for `s := 1`.  The theorem exists in `PowerSeries.Substitution`; its rendered statement is exactly the `if e = Finsupp.single s (e s)` coefficient formula.
