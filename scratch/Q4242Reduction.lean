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
  rw [E0_discriminant]
  convert isUnit_one using 1
  norm_num

/-- Direct finite computation: the group of points of the good reduction has exponent four. -/
theorem E0_F2_exponent_four (P : (E0 (ZMod 2)).Point) :
    4 • P = 0 := by
  cases P with
  | zero => simp
  | some x y h =>
      fin_cases x <;> fin_cases y <;> native_decide

end N15Reduction
