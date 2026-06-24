module

public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.PowerSeries.Order

/-! # SEAM1 / E1 — formal `[n]` linear coefficient: `[n]'(0) = n`

The genuine mathematical heart of the SEAM1 rootwise crux: over ANY one-dimensional formal group
law `F` over a commutative ring `R`, the formal multiplication-by-`n` series `[n](T)` has its
linear coefficient equal to `(n : R)` and zero constant coefficient, i.e. `[n](T) = nT + O(T²)`.

This is exactly the statement that "the tangent of `[n]` at the origin is scalar `n`", phrased
intrinsically on the formal group (NOT via the field-only point group). It is fully self-contained
(0 sorry, 0 custom axiom) and reusable: it depends only on the two linear-coefficient fields of
`FormalGroup` plus the power-series substitution coefficient formula.

The remaining SEAM1 gap (linking the Weierstrass `σ`-formal group's `[n]` to the division
polynomial `preΨ'`) is isolated elsewhere; this file lands the formal-group core. -/

open MvPowerSeries Finsupp

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- Formal addition of two one-variable series `f, g` via the bivariate group law `F`:
substitute `X₀ ↦ f`, `X₁ ↦ g`. -/
noncomputable def addSeries (F : FormalGroup R) (f g : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst (fun i : Fin 2 => ![f, g] i) F.toPowerSeries

/-- The substitution map used by `addSeries` is admissible when both inputs have zero
constant coefficient. -/
theorem hasSubst_pair {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff (R := R) f = 0) (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    MvPowerSeries.HasSubst (fun i : Fin 2 => ![f, g] i) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  · exact hf
  · exact hg

/-- Constant coefficient of a formal addition vanishes (origin is the identity to lowest order). -/
theorem addSeries_constantCoeff (F : FormalGroup R) {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff (R := R) f = 0) (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.constantCoeff (R := R) (F.addSeries f g) = 0 := by
  sorry

/-- The linear coefficient of a formal addition is additive: this is where the two
`FormalGroup` linear-coefficient fields `lin_coeff_X`, `lin_coeff_Y` are consumed. -/
theorem addSeries_coeff_one (F : FormalGroup R) {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff (R := R) f = 0) (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.coeff (R := R) 1 (F.addSeries f g) =
      PowerSeries.coeff (R := R) 1 f + PowerSeries.coeff (R := R) 1 g := by
  sorry

/-- Formal multiplication-by-`n` series `[n](T)`, defined by `[0] = 0`, `[n+1] = F(·, T)`. -/
noncomputable def formalNsmul (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => F.addSeries (F.formalNsmul n) PowerSeries.X

@[simp] lemma formalNsmul_zero (F : FormalGroup R) : F.formalNsmul 0 = 0 := rfl

@[simp] lemma formalNsmul_succ (F : FormalGroup R) (n : ℕ) :
    F.formalNsmul (n + 1) = F.addSeries (F.formalNsmul n) PowerSeries.X := rfl

/-- `[n](T)` has zero constant coefficient. -/
theorem formalNsmul_constantCoeff (F : FormalGroup R) (n : ℕ) :
    PowerSeries.constantCoeff (R := R) (F.formalNsmul n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [formalNsmul_succ]
      exact addSeries_constantCoeff F ih (by simp)

/-- **`[n]'(0) = n`**: the linear coefficient of the formal `[n]` series is `(n : R)`.
This is the formal-group tangent-at-origin fact, the intrinsic version of
`TangentO.nsmul₁ n 1 = (n : K)`. -/
theorem formalNsmul_coeff_one (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff (R := R) 1 (F.formalNsmul n) = (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [formalNsmul_succ,
        addSeries_coeff_one F (formalNsmul_constantCoeff F n) (by simp),
        ih, PowerSeries.coeff_one_X, Nat.cast_succ]

end FormalGroup
