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
  have h225 : (225 : ZMod 2) = 1 := by native_decide
  rw [E0_discriminant, h225]
  exact isUnit_one

abbrev Pt2 := WeierstrassCurve.Affine.Point (E0 (ZMod 2))

def R00 : Pt2 := .mk (x := 0) (y := 0) (by native_decide)
def R01 : Pt2 := .mk (x := 0) (y := 1) (by native_decide)
def R11 : Pt2 := .mk (x := 1) (y := 1) (by native_decide)

lemma R00_coords : R00 = WeierstrassCurve.Affine.Point.mk (W' := E0 (ZMod 2))
    (x := 0) (y := 0) (by native_decide) := by rfl
lemma R01_coords : R01 = WeierstrassCurve.Affine.Point.mk (W' := E0 (ZMod 2))
    (x := 0) (y := 1) (by native_decide) := by rfl
lemma R11_coords : R11 = WeierstrassCurve.Affine.Point.mk (W' := E0 (ZMod 2))
    (x := 1) (y := 1) (by native_decide) := by rfl

lemma Pt2_exhaust (P : Pt2) : P = 0 ∨ P = R00 ∨ P = R01 ∨ P = R11 := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
      fin_cases x <;> fin_cases y
      · right; left
        rw [R00_coords]
        apply WeierstrassCurve.Affine.Point.some.inj
        exact ⟨rfl, rfl⟩
      · right; right; left
        rw [R01_coords]
        apply WeierstrassCurve.Affine.Point.some.inj
        exact ⟨rfl, rfl⟩
      · exfalso
        have heq := h.1
        native_decide at heq
      · right; right; right
        rw [R11_coords]
        apply WeierstrassCurve.Affine.Point.some.inj
        exact ⟨rfl, rfl⟩

lemma four_R00 : 4 • R00 = 0 := by native_decide
lemma four_R01 : 4 • R01 = 0 := by native_decide
lemma four_R11 : 4 • R11 = 0 := by native_decide

/-- Direct finite computation: the group of points of the good reduction has exponent four. -/
theorem E0_F2_exponent_four (P : Pt2) : 4 • P = 0 := by
  rcases Pt2_exhaust P with rfl | rfl | rfl | rfl
  · simp
  · exact four_R00
  · exact four_R01
  · exact four_R11

end N15Reduction
