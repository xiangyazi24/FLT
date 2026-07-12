import FLT.Assumptions.MazurProof.N18RouteC_Split
import Mathlib.Data.Fintype.WithTopBot

/-!
# The seven-point reduction group for N18 Route C

The good model at the prime above `3` reduces to a seven-element elliptic
curve.  This file turns the existing six-affine-point Boolean certificate into
the exact finite point-group exponent consumed by separatedness.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.Reduction

instance reducedGood_isElliptic : reducedGoodCurve.IsElliptic where
  isUnit := by
    apply isUnit_iff_ne_zero.mpr
    decide

abbrev RedPoint := WeierstrassCurve.Affine.Point reducedGoodCurve

theorem reducedGoodAffine_eq_true_iff (x y : ZMod 3) :
    reducedGoodAffine x y = true ↔
      WeierstrassCurve.Affine.Equation reducedGoodCurve x y := by
  simp [reducedGoodAffine, reducedGoodCurve,
    WeierstrassCurve.Affine.equation_iff]

def pointEquiv :
    RedPoint ≃
      Option {p : ZMod 3 × ZMod 3 //
        reducedGoodAffine p.1 p.2 = true} where
  toFun
    | .zero => none
    | .some x y h => .some ⟨(x, y),
        (reducedGoodAffine_eq_true_iff x y).2 h.1⟩
  invFun
    | none => .zero
    | .some p => WeierstrassCurve.Affine.Point.mk
        ((reducedGoodAffine_eq_true_iff p.1.1 p.1.2).1 p.2)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

instance : Fintype RedPoint :=
  Fintype.ofEquiv
    (Option {p : ZMod 3 × ZMod 3 //
      reducedGoodAffine p.1 p.2 = true}) pointEquiv.symm

theorem redPoint_card : Fintype.card RedPoint = 7 := by
  set_option maxHeartbeats 0 in
    decide

theorem seven_nsmul (P : RedPoint) : (7 : ℕ) • P = 0 := by
  have h : Fintype.card RedPoint • P = 0 := card_nsmul_eq_zero
  rw [redPoint_card] at h
  exact h

end MazurProof.N18RouteC.Reduction
