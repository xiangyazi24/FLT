import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The `N = 10` obstruction curve

This file records basic verified data about the elliptic curve with LMFDB label
`20.a4`, Cremona label `20a1`.  The LMFDB coefficients are `[0, 1, 0, 4, 4]`,
so the model is

`y^2 = x^3 + x^2 + 4x + 4`.

The rank-zero/completeness certificate is left as a separate arithmetic input.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.ObstructionCurve

/-- The obstruction curve `20.a4`, Cremona label `20a1`. -/
def E20 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := 4
  a₆ := 4

lemma E20_delta : E20.Δ = (-6400 : ℚ) := by
  norm_num [E20, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E20_isElliptic : E20.IsElliptic where
  isUnit := by
    rw [E20_delta]
    norm_num

abbrev E20Point : Type :=
  WeierstrassCurve.Affine.Point E20

def E20IntEquation (x y : ℤ) : Prop :=
  y ^ 2 = x ^ 3 + x ^ 2 + 4 * x + 4

def integerAffinePointsInBox : List (ℤ × ℤ) :=
  [(-1, 0), (0, -2), (0, 2), (4, -10), (4, 10)]

lemma integerAffinePointsInBox_complete {x y : ℤ}
    (hx_low : -10 ≤ x) (hx_high : x ≤ 10)
    (hy_low : -10 ≤ y) (hy_high : y ≤ 10)
    (hxy : E20IntEquation x y) :
    (x, y) ∈ integerAffinePointsInBox := by
  interval_cases x <;> interval_cases y
  all_goals norm_num [E20IntEquation] at hxy
  all_goals norm_num [integerAffinePointsInBox]

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

noncomputable def Pm1_0 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_m1_0

noncomputable def P0_2 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_0_2

noncomputable def P0_m2 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_0_m2

noncomputable def P4_10 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_4_10

noncomputable def P4_m10 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_4_m10

/-- The six visible rational points on `E20`, indexed in cyclic order. -/
noncomputable def knownPoint : Fin 6 → E20Point
  | 0 => 0
  | 1 => P4_10
  | 2 => P0_2
  | 3 => Pm1_0
  | 4 => P0_m2
  | 5 => P4_m10

/-- Addition table for the six visible points, using the indices of `knownPoint`. -/
def knownAddIndex (i j : Fin 6) : Fin 6 :=
  i + j

lemma add_P0_2_P0_m2 : P0_2 + P0_m2 = 0 := by
  unfold P0_2 P0_m2
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ = 0
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
  norm_num [E20, WeierstrassCurve.Affine.negY]

lemma add_P0_2_P0_2 : P0_2 + P0_2 = P0_m2 := by
  unfold P0_2 P0_m2
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ =
    WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne]
  · norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY]
  · norm_num [E20, WeierstrassCurve.Affine.negY]

lemma add_Pm1_0_self : Pm1_0 + Pm1_0 = 0 := by
  unfold Pm1_0
  change WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _ +
      WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _ = 0
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
  norm_num [E20, WeierstrassCurve.Affine.negY]

lemma add_P0_m2_P0_m2 : P0_m2 + P0_m2 = P0_2 := by
  unfold P0_m2 P0_2
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ +
      WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ =
    WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne]
  · norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY]
  · norm_num [E20, WeierstrassCurve.Affine.negY]

lemma add_P4_10_P4_m10 : P4_10 + P4_m10 = 0 := by
  unfold P4_10 P4_m10
  change WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ = 0
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
  norm_num [E20, WeierstrassCurve.Affine.negY]

lemma add_P4_10_self : P4_10 + P4_10 = P0_2 := by
  unfold P4_10 P0_2
  change WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ =
    WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne]
  · norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY]
  · norm_num [E20, WeierstrassCurve.Affine.negY]

lemma add_P4_m10_self : P4_m10 + P4_m10 = P0_m2 := by
  unfold P4_m10 P0_m2
  change WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ =
    WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne]
  · norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY]
  · norm_num [E20, WeierstrassCurve.Affine.negY]

lemma add_Pm1_0_P0_2 : Pm1_0 + P0_2 = P4_m10 := by
  unfold Pm1_0 P0_2 P4_m10
  change WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _ +
      WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ =
    WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_Pm1_0_P4_10 : Pm1_0 + P4_10 = P0_m2 := by
  unfold Pm1_0 P4_10 P0_m2
  change WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ =
    WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_Pm1_0_P4_m10 : Pm1_0 + P4_m10 = P0_2 := by
  unfold Pm1_0 P4_m10 P0_2
  change WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ =
    WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_Pm1_0_P0_m2 : Pm1_0 + P0_m2 = P4_10 := by
  unfold Pm1_0 P0_m2 P4_10
  change WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _ +
      WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ =
    WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P0_2_P4_10 : P0_2 + P4_10 = Pm1_0 := by
  unfold P0_2 P4_10 Pm1_0
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ =
    WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P0_2_P4_m10 : P0_2 + P4_m10 = P4_10 := by
  unfold P0_2 P4_m10 P4_10
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ =
    WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P0_m2_P4_10 : P0_m2 + P4_10 = P4_m10 := by
  unfold P0_m2 P4_10 P4_m10
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ =
    WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P0_m2_P4_m10 : P0_m2 + P4_m10 = Pm1_0 := by
  unfold P0_m2 P4_m10 Pm1_0
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ =
    WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

/-- The six visible points are closed under addition, with the explicit addition table above. -/
theorem knownPoint_add_table (i j : Fin 6) :
    knownPoint (knownAddIndex i j) = knownPoint i + knownPoint j := by
  fin_cases i <;> fin_cases j <;>
    simp [knownAddIndex, knownPoint, add_Pm1_0_self, add_P0_2_P0_m2,
      add_P0_2_P0_2, add_P0_m2_P0_m2, add_P4_10_P4_m10, add_P4_10_self,
      add_P4_m10_self, add_Pm1_0_P0_2, add_Pm1_0_P4_10, add_Pm1_0_P4_m10,
      add_Pm1_0_P0_m2, add_P0_2_P4_10, add_P0_2_P4_m10, add_P0_m2_P4_10,
      add_P0_m2_P4_m10, add_comm]

/--
The visible points form a finite subgroup candidate under addition.  Completeness
of this list as all rational points is the rank-zero certificate and is not
proved here.
-/
def knownPointSet : Set E20Point :=
  Set.range knownPoint

theorem knownPointSet_add_closed {P Q : E20Point}
    (hP : P ∈ knownPointSet) (hQ : Q ∈ knownPointSet) :
    P + Q ∈ knownPointSet := by
  rcases hP with ⟨i, rfl⟩
  rcases hQ with ⟨j, rfl⟩
  exact ⟨knownAddIndex i j, knownPoint_add_table i j⟩

/-- Arithmetic input left for the later certificate: the visible six points are all rational points. -/
axiom E20_rational_points_complete (P : E20Point) : P ∈ knownPointSet

end MazurProof.ObstructionCurve
