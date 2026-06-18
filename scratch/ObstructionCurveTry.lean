import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open scoped WeierstrassCurve.Affine

namespace ObstructionCurveTry

def E20 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := 4
  a₆ := 4

lemma E20_delta : E20.Δ = (-6400 : ℚ) := by
  norm_num [E20, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : E20.IsElliptic where
  isUnit := by
    rw [E20_delta]
    norm_num

lemma eq_m1_0 : WeierstrassCurve.Affine.Equation E20 (-1 : ℚ) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_0_2 : WeierstrassCurve.Affine.Equation E20 (0 : ℚ) 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_0_m2 : WeierstrassCurve.Affine.Equation E20 (0 : ℚ) (-2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_4_10 : WeierstrassCurve.Affine.Equation E20 (4 : ℚ) 10 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_4_m10 : WeierstrassCurve.Affine.Equation E20 (4 : ℚ) (-10) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

noncomputable def Pm1_0 : WeierstrassCurve.Affine.Point E20 :=
  WeierstrassCurve.Affine.Point.mk eq_m1_0
noncomputable def P0_2 : WeierstrassCurve.Affine.Point E20 :=
  WeierstrassCurve.Affine.Point.mk eq_0_2
noncomputable def P0_m2 : WeierstrassCurve.Affine.Point E20 :=
  WeierstrassCurve.Affine.Point.mk eq_0_m2
noncomputable def P4_10 : WeierstrassCurve.Affine.Point E20 :=
  WeierstrassCurve.Affine.Point.mk eq_4_10
noncomputable def P4_m10 : WeierstrassCurve.Affine.Point E20 :=
  WeierstrassCurve.Affine.Point.mk eq_4_m10

#check WeierstrassCurve.Affine.Point.add_of_X_ne
#check WeierstrassCurve.Affine.Point.add_of_Y_eq
#check WeierstrassCurve.Affine.Point.add_self_of_Y_ne

example : P0_2 + P0_m2 = 0 := by
  unfold P0_2 P0_m2
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ = 0
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
  norm_num [E20, WeierstrassCurve.Affine.negY]

example : P0_2 + P0_2 = P0_m2 := by
  unfold P0_2 P0_m2
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ =
    WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne]
  · norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY]
  · norm_num [E20, WeierstrassCurve.Affine.negY]

end ObstructionCurveTry
