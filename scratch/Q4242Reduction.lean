import Mathlib

set_option autoImplicit false

noncomputable section

namespace N15Reduction

open WeierstrassCurve

/-- The good integral model used at the prime 2. -/
def E0 (R : Type*) [CommRing R] : WeierstrassCurve R :=
  ⟨1, 1, 1, -5, 2⟩

lemma E0_discriminant (R : Type*) [CommRing R] :
    (E0 R).Δ = (225 : R) := by
  simp [E0, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

instance : (E0 (ZMod 2)).IsElliptic := by
  refine ⟨?_⟩
  have h225 : (225 : ZMod 2) = 1 := by norm_num
  rw [E0_discriminant, h225]
  exact isUnit_one

/-- Direct finite computation: the group of points of the good reduction has exponent four. -/
theorem E0_F2_exponent_four
    (P : WeierstrassCurve.Affine.Point (E0 (ZMod 2))) :
    4 • P = 0 := by
  cases P with
  | zero => simp
  | some x y h =>
      fin_cases x <;> fin_cases y <;> native_decide

end N15Reduction
