# Q448 / dm2 — Lean code for the formal projective point

Target: define the formal projective point

```text
P(t) = [t : -1 : w(t)]
```

and prove it satisfies the projective Weierstrass equation.

The main API correction is that `W.toProjective.Equation` is over the coefficient ring of `W`.  Since the point coordinates are in `PowerSeries K`, the curve must first be mapped along

```lean
PowerSeries.C : K →+* PowerSeries K
```

So the correct equation statement is not

```lean
W.toProjective.Equation (W.formalPoint)
```

but

```lean
((W.map (PowerSeries.C : K →+* PowerSeries K)).toProjective).Equation (W.formalPoint)
```

or the abbreviation `W.formalCurve.Equation W.formalPoint` below.

I could not fetch the exact short commit `7017415` through the connector, so the snippet is written against Mathlib's current `Projective.Equation` / `Projective.dblXYZ` API and the recurrence theorem name used in the visible HasseWeil file, namely `formalW_recurrence`.  If your scratch file names the recurrence theorem differently, replace only that last identifier.

## Code

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

open WeierstrassCurve PowerSeries

namespace WeierstrassCurve

variable {K : Type*} [CommRing K]

/-- The Weierstrass curve `W`, base-changed to `PowerSeries K` via constants. -/
noncomputable def formalCurve (W : WeierstrassCurve K) :
    WeierstrassCurve.Projective (PowerSeries K) :=
  (W.map (PowerSeries.C : K →+* PowerSeries K)).toProjective

/-- The formal projective point near infinity: `P(t) = [t : -1 : w(t)]`. -/
noncomputable def formalPoint (W : WeierstrassCurve K) : Fin 3 → PowerSeries K :=
  ![(PowerSeries.X : PowerSeries K), (-1 : PowerSeries K), W.formalW]

/-- The expanded recurrence RHS for `formalW`.  This is useful because the projective
    equation reduces exactly to `formalW - formalW_rhs = 0`. -/
noncomputable def formalW_rhs (W : WeierstrassCurve K) : PowerSeries K :=
  (PowerSeries.X : PowerSeries K) ^ 3
    + PowerSeries.C W.a₁ * (PowerSeries.X : PowerSeries K) * W.formalW
    + PowerSeries.C W.a₂ * (PowerSeries.X : PowerSeries K) ^ 2 * W.formalW
    + PowerSeries.C W.a₃ * W.formalW ^ 2
    + PowerSeries.C W.a₄ * (PowerSeries.X : PowerSeries K) * W.formalW ^ 2
    + PowerSeries.C W.a₆ * W.formalW ^ 3

/-- `P(t) = [t:-1:w(t)]` lies on the coefficient-lifted projective Weierstrass curve. -/
theorem formalPoint_equation (W : WeierstrassCurve K) :
    (W.formalCurve).Equation (W.formalPoint) := by
  rw [WeierstrassCurve.Projective.equation_iff]
  -- After expanding `Equation`, this is just the defining equation for `formalW`.
  simp only [formalCurve, formalPoint, formalW_rhs,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    one_pow, neg_mul, mul_neg, one_mul, mul_one]
  -- If your theorem is named differently, replace `W.formalW_recurrence` here.
  -- Expected type:
  --   W.formalW = W.formalW_rhs
  change W.formalW - W.formalW_rhs = 0
  exact sub_eq_zero.mpr W.formalW_recurrence

/-- One-variable doubling substitute: this is `dblXYZ(P(t))`, not the two-variable
    formal group law.  Use this only for the doubling sanity check. -/
noncomputable def formalDblXYZ (W : WeierstrassCurve K) : Fin 3 → PowerSeries K :=
  (W.formalCurve).dblXYZ (W.formalPoint)

end WeierstrassCurve
```

## If the final `change` line does not match syntactically

Depending on how `formalW_recurrence` is stated in `scratch/FormalGroupW.lean`, the last three lines may need this slightly more explicit replacement:

```lean
  have hw : W.formalW = W.formalW_rhs := by
    simpa [formalW_rhs] using W.formalW_recurrence
  change W.formalW - W.formalW_rhs = 0
  exact sub_eq_zero.mpr hw
```

If `simp only` leaves the target in a different but ring-equivalent order, use this fallback:

```lean
  have hw : W.formalW = W.formalW_rhs := by
    simpa [formalW_rhs] using W.formalW_recurrence
  linear_combination (norm := ring_nf) hw
```

but the `change ...; exact sub_eq_zero.mpr hw` route is preferable because it avoids asking `ring_nf` to normalize `PowerSeries K` expressions.

## Notes for the next step

For `P(t)+P(t)` use `dblXYZ`, not `addXYZ`:

```lean
#check WeierstrassCurve.Projective.dblXYZ
#check WeierstrassCurve.formalDblXYZ
```

For the real formal group law, the one-variable point above must be transported to two different variables in `MvPowerSeries (Fin 2) K`.  The two-variable version should have the shape

```text
P₁ = [T₁, -1, w(T₁)]
P₂ = [T₂, -1, w(T₂)]
addXYZ(P₁,P₂)
```

where the curve is mapped to `MvPowerSeries (Fin 2) K` by `MvPowerSeries.C` and `w(Tᵢ)` is obtained by substituting/renaming the one-variable `formalW` into variable `i`.
