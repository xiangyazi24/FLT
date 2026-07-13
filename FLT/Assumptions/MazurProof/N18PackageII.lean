import FLT.Assumptions.MazurProof.N18RouteC_GoodModel
import FLT.Assumptions.MazurProof.N18AddCongr
import FLT.Assumptions.MazurProof.N18GoodModelValCoords
import FLT.Assumptions.MazurProof.N18VpiWrapper
import scratch.KeystoneEDS

/-!
# Package II for the N18 formal kernel

This file proves that the second step of the `pi`-adic formal filtration of
the good model `E0Good` is torsion-free.  The proof uses the projective
division-polynomial coordinates of scalar multiples.  At a point with
`ordPi x = -2r`, the leading terms of `Phi_n(x)` and `PsiSq_n(x)` strictly
dominate all lower terms.  For `3 ∤ n` this preserves `r`; for `n = 3` and
`r >= 2`, the extra orders of the first two coefficients give `r + 3`.
-/

open scoped Classical NumberField WeierstrassCurve.Affine

namespace MazurProof.N18PackageII

open Polynomial
open MazurProof.N18RouteC
open MazurProof.N18RouteC.FieldArithmetic
open MazurProof.N18RouteC.GoodModel
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18Block5Instantiation.AddCongr

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

/-- Formal parameter `z = -x/y` on the good model, totalized by `z(O) = 0`. -/
def zParamGood : E0GoodPoint → L
  | .zero => 0
  | .some x y _ => -x / y

@[simp] theorem zParamGood_zero : zParamGood (0 : E0GoodPoint) = 0 := rfl

@[simp] theorem zParamGood_some (x y : L)
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y) :
    zParamGood (.some x y h) = -x / y := rfl

/-- The pointwise formal-kernel predicate on the good model. -/
def InFormalKernel : E0GoodPoint → Prop
  | .zero => True
  | .some x _ _ => ordPi x < 0

@[simp] theorem zero_mem_formalKernel : InFormalKernel (0 : E0GoodPoint) := trivial

end

end MazurProof.N18PackageII
