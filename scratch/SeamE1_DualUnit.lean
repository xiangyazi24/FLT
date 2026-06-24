module

public import scratch.SeamE1_Jet
public import Mathlib.Tactic

/-! # SEAM1 / E1 — dual-number unit facts

Two reusable, fully-proven (0 sorry, 0 custom axiom) algebra facts for the SEAM1 rootwise crux:

* `dualNumber_isUnit_of_fst_ne_zero`: a dual number `z ∈ K[ε]` with nonzero scalar part `fst z`
  is a unit (explicit inverse `(fst z)⁻¹ - ε·(snd z)·(fst z)⁻²`).
* `psi2_dual_isUnit`: the lifted `ψ₂ = W_Y` evaluated at the dual point `(x+ε, y+ε·slope)` is a
  unit, because its scalar part is `W_Y(x,y) = hY ≠ 0`.

These discharge step 2 of the bridge-2 design (`DESIGN_bridge2_crux.md`): the `ψ₂`-unit condition
needed by the raw `[n]`-coordinate multiplication formula over `DualNumber K`. -/

@[expose] public section

open TrivSqZeroExt

namespace WeierstrassCurve.SEAM1

variable {K : Type*} [Field K]

/-- A dual number with nonzero scalar part is a unit. Explicit inverse:
`(fst z)⁻¹ + ε·(-(snd z)·(fst z)⁻²)`. -/
theorem dualNumber_isUnit_of_fst_ne_zero (z : D K) (hz : TrivSqZeroExt.fst z ≠ 0) :
    IsUnit z := by
  have hmul : z * (inl (fst z)⁻¹ + inr (-(snd z * (fst z)⁻¹ * (fst z)⁻¹))) = 1 := by
    conv_lhs => rw [show z = inl (fst z) + inr (snd z) from
      (TrivSqZeroExt.inl_fst_add_inr_snd_eq z).symm]
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
        op_smul_eq_mul, smul_eq_mul, add_zero]
    · field_simp
    · field_simp; ring
  exact IsUnit.of_mul_eq_one _ hmul

/-- The scalar part of the lifted `ψ₂ = W_Y` at the dual point `(x+ε, y+ε·slope)` is exactly
the original `W_Y(x,y)`. -/
theorem psi2_dual_fst (W : WeierstrassCurve K) {x y : K} :
    TrivSqZeroExt.fst ((W.toAffine.baseChange (D K)).polynomialY.evalEval
        (MultipleRootBridge.xε x) (MultipleRootBridge.yε W x y))
      = W.toAffine.polynomialY.evalEval x y := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY,
      WeierstrassCurve.Affine.evalEval_polynomialY]
  simp only [AffineJet.bc_a₁, AffineJet.bc_a₃, MultipleRootBridge.xε, MultipleRootBridge.yε,
    Dual.c, Dual.e]
  have h2 : TrivSqZeroExt.fst (2 : D K) = (2 : K) := rfl
  simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, h2]

/-- **Dual `ψ₂` is a unit at a non-2-torsion point.** The lifted `ψ₂ = W_Y` evaluated at the
dual point `(x+ε, y+ε·slope)` is a unit in `K[ε]`, because its scalar part is `W_Y(x,y) ≠ 0`.

This discharges step 2 of the bridge-2 design: the `ψ₂`-unit hypothesis required by the raw
`[n]`-coordinate multiplication-by-`n` formula over `DualNumber K`. -/
theorem psi2_dual_isUnit (W : WeierstrassCurve K) {x y : K}
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    IsUnit ((W.toAffine.baseChange (D K)).polynomialY.evalEval
      (MultipleRootBridge.xε x) (MultipleRootBridge.yε W x y)) := by
  apply dualNumber_isUnit_of_fst_ne_zero
  rw [psi2_dual_fst]
  exact hY

end WeierstrassCurve.SEAM1
