import FLT.Assumptions.MazurProof.N13AbelFiberTwoModel
import FLT.Assumptions.MazurProof.N13Mumford

/-!
# The six N13 cusps on the special fibre

The good characteristic-two model has three hyperelliptic base points and
two sheets over each of them.  The six rational cusps reduce to these six
points bijectively.  This file records that correspondence as an explicit
equivalence.

The proof uses only the structural fact that every element of `F₂` is zero
or one.  It does not enumerate divisors or Jacobian representatives.
-/

namespace MazurProof.N13SpecialCuspReduction

noncomputable section

open N13AbelFiberTwoModel

abbrev Cusp13 : Type :=
  N13Mumford.Cusp13

abbrev SpecialCurvePoint : Type :=
  N13AbelFiberTwoModel.CurvePoint

/-- Coordinates of a rational cusp on the good special fibre.  The affine
coordinate change is `Y = 2y + x³ + x + 1`; this explains the reversal of
the two sheets over `x = 1`. -/
def cuspCoordinate : Cusp13 → BasePoint × K
  | .infinityPlus => (Sum.inr (), 0)
  | .infinityMinus => (Sum.inr (), 1)
  | .zeroPlus => (Sum.inl 0, 0)
  | .zeroMinus => (Sum.inl 0, 1)
  | .negOnePlus => (Sum.inl 1, 1)
  | .negOneMinus => (Sum.inl 1, 0)

/-- Recover the named rational cusp from its special base point and sheet. -/
def cuspOfCoordinate : BasePoint × K → Cusp13
  | (Sum.inr _, y) =>
      if y = 0 then .infinityPlus else .infinityMinus
  | (Sum.inl x, y) =>
      if x = 0 then
        if y = 0 then .zeroPlus else .zeroMinus
      else
        if y = 0 then .negOneMinus else .negOnePlus

theorem cuspOfCoordinate_cuspCoordinate
    (c : Cusp13) :
    cuspOfCoordinate (cuspCoordinate c) = c := by
  cases c <;> simp [cuspCoordinate, cuspOfCoordinate]

theorem cuspCoordinate_cuspOfCoordinate
    (z : BasePoint × K) :
    cuspCoordinate (cuspOfCoordinate z) = z := by
  rcases z with ⟨b, y⟩
  have hy : y = 0 ∨ y = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one y (ZMod.pow_card y)
  rcases b with x | u
  · have hx : x = 0 ∨ x = 1 :=
      N13GoodModelTwo.fixedTwo_eq_zero_or_one x (ZMod.pow_card x)
    rcases hx with rfl | rfl <;>
      rcases hy with rfl | rfl <;>
      simp [cuspCoordinate, cuspOfCoordinate]
  · cases u
    rcases hy with rfl | rfl <;>
      simp [cuspCoordinate, cuspOfCoordinate]

/-- The six named cusps are exactly the three special base points times
the two sheets. -/
def cuspCoordinateEquiv : Cusp13 ≃ BasePoint × K where
  toFun := cuspCoordinate
  invFun := cuspOfCoordinate
  left_inv := cuspOfCoordinate_cuspCoordinate
  right_inv := cuspCoordinate_cuspOfCoordinate

/-- Reduction of the six rational cusps identifies them bijectively with
all points of the good characteristic-two curve. -/
def specialCuspEquiv : Cusp13 ≃ SpecialCurvePoint :=
  cuspCoordinateEquiv.trans curvePointEquiv.symm

@[simp] theorem curvePointEquiv_specialCuspEquiv
    (c : Cusp13) :
    curvePointEquiv (specialCuspEquiv c) =
      cuspCoordinate c := by
  simp [specialCuspEquiv, cuspCoordinateEquiv]

theorem specialCuspEquiv_surjective :
    Function.Surjective specialCuspEquiv :=
  specialCuspEquiv.surjective

end

end MazurProof.N13SpecialCuspReduction
