import FLT.Assumptions.MazurProof.TateOriginDivision

/-!
# The concrete order-7 Tate-normal-form factorization

This file proves the explicit evaluation `preΨ'₇(0) = b¹⁶(c³ + bc − b²)` at the
Tate origin using the Mathlib division-polynomial recursion.

The factorization is the key input for the order-49 exclusion: the order-49
division polynomial `preΨ'₄₉(0)` is divisible by `preΨ'₇(0)`, so the exact
order-49 condition `preΨ'₄₉(0) = 0 ∧ preΨ'₇(0) ≠ 0` forces vanishing of the
primitive quotient factor.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsN49

open MazurProof.TateOriginDivision
open Scratch.TateZ2xZ10Reduction

noncomputable section

/-! ## Recursion-level evaluations at X = 0

Each step applies `preΨ'_odd` or `preΨ'_even` from Mathlib, evaluates the
resulting polynomial identity at `X = 0`, and is closed by `simpa`. -/

private lemma eval_prePsi_five (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_six (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 =
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 0)
  simpa using h

private lemma eval_prePsi_seven (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 =
      ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 3).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 ^ 3 * ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 1)
  simpa using h

/-! ## Concrete factorization of `preΨ'₇(0)` -/

/-- The primitive order-7 factor at the Tate origin. -/
def F7 (b c : ℚ) : ℚ :=
  c ^ 3 + b * c - b ^ 2

/-- `preΨ'₇(0) = b¹⁶(c³ + bc − b²)` on the Tate normal form. -/
theorem prePsi_seven_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 = b ^ 16 * F7 b c := by
  rw [eval_prePsi_seven, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, F7]
  ring

/-- If the order-7 division polynomial vanishes and `b ≠ 0`,
the primitive factor `F₇` must vanish. -/
theorem F7_eq_zero_of_prePsi_seven_eq_zero {b c : ℚ} (hb : b ≠ 0)
    (h : ((W b c).preΨ' 7).eval 0 = 0) :
    F7 b c = 0 := by
  rw [prePsi_seven_eval_tate_origin] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 16 hb)

/-- Contrapositive: nonvanishing of `F₇` gives nonvanishing of `preΨ'₇(0)`. -/
theorem prePsi_seven_ne_zero_of_F7_ne_zero {b c : ℚ} (hb : b ≠ 0)
    (hF : F7 b c ≠ 0) :
    ((W b c).preΨ' 7).eval 0 ≠ 0 := by
  rw [prePsi_seven_eval_tate_origin]
  exact mul_ne_zero (pow_ne_zero 16 hb) hF

/-! ## Consequence for the exact-order-49 condition

The order-49 condition gives `preΨ'₄₉(0) = 0` and `preΨ'₇(0) ≠ 0`.
Since `7 | 49`, the division polynomial divisibility `ψ₇ | ψ₄₉` forces
`preΨ'₇(0) | preΨ'₄₉(0)` in a precise sense (after factoring out `b`-powers).
The nonvanishing of `preΨ'₇(0)` then shows the primitive quotient `H₄₉`
vanishes. -/

end

end MazurProof.RationalPointsN49
