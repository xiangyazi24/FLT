# Q677 (dm4): coefficients of constant multiplication in `MvPowerSeries`

## Answer

Yes.  Mathlib already has the two lemmas you want:

```lean
MvPowerSeries.coeff_C_mul
MvPowerSeries.coeff_mul_C
```

They are also tagged `[simp]`, so in many goals `simp` is enough.

The names are slightly easy to mix up:

```lean
MvPowerSeries.coeff_C_mul  -- coeff e (C a * f) = a * coeff e f
MvPowerSeries.coeff_mul_C  -- coeff e (f * C a) = coeff e f * a
```

Here is a complete Lean file with direct wrappers and also proofs from the monomial-shift lemmas.

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic

noncomputable section

open MvPowerSeries

namespace Q677

variable {σ R : Type*} [Semiring R]

/-- Direct use of the existing Mathlib lemma:
`coeff e (C a * f) = a * coeff e f`. -/
theorem coeff_C_mul_direct
    (a : R) (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.C a * f) =
      a * MvPowerSeries.coeff e f := by
  simpa using (MvPowerSeries.coeff_C_mul (σ := σ) (R := R) e f a)

/-- Direct use of the existing Mathlib lemma:
`coeff e (f * C a) = coeff e f * a`. -/
theorem coeff_mul_C_direct
    (a : R) (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (f * MvPowerSeries.C a) =
      MvPowerSeries.coeff e f * a := by
  simpa using (MvPowerSeries.coeff_mul_C (σ := σ) (R := R) e f a)

/-- Since `coeff_C_mul` and `coeff_mul_C` are simp lemmas, this proof also works. -/
theorem coeff_C_mul_by_simp
    (a : R) (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.C a * f) =
      a * MvPowerSeries.coeff e f := by
  simp

/-- Since `coeff_C_mul` and `coeff_mul_C` are simp lemmas, this proof also works. -/
theorem coeff_mul_C_by_simp
    (a : R) (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (f * MvPowerSeries.C a) =
      MvPowerSeries.coeff e f * a := by
  simp

/-- A proof from the monomial shift lemma.

This uses that `C a` is definitionally the monomial at `0` with coefficient `a`,
and `coeff_add_monomial_mul` has already specialized the conditional in
`coeff_monomial_mul`. -/
theorem coeff_C_mul_from_monomial
    (a : R) (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.C a * f) =
      a * MvPowerSeries.coeff e f := by
  simpa using
    (MvPowerSeries.coeff_add_monomial_mul
      (R := R)
      (m := (0 : σ →₀ ℕ))
      (n := e)
      (φ := f)
      (a := a))

/-- The right-multiplication version from the monomial shift lemma. -/
theorem coeff_mul_C_from_monomial
    (a : R) (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (f * MvPowerSeries.C a) =
      MvPowerSeries.coeff e f * a := by
  simpa using
    (MvPowerSeries.coeff_add_mul_monomial
      (R := R)
      (m := e)
      (n := (0 : σ →₀ ℕ))
      (φ := f)
      (a := a))

end Q677
```

For ordinary use in your formal-group coefficient proof, I would simply write:

```lean
simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_mul_C]
```

or just:

```lean
simp
```

because both lemmas are already simp-normal forms.
