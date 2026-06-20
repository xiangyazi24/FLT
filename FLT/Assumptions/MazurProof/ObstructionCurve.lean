import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import scratch.ObstructionComplete
import scratch.TateZ2xZ10Reduction

/-!
# The `N = 10` obstruction curve

This file records basic verified data about the elliptic curve

`y^2 = x^3 + x^2 + 4x + 4`.

It is shifted to `E0 : y^2 = X^3 - 2X^2 + 5X`, then related by the explicit
2-isogeny coordinates to the already-proved `20a4` obstruction
`w^2 = u^3 + u^2 - u`.
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

/-- The shifted model `X = x + 1`: `y² = X³ - 2X² + 5X`. -/
def E0 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -2
  a₃ := 0
  a₄ := 5
  a₆ := 0

/-- The variable change taking `E20` to `E0`. -/
def shiftE20 : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := -1
  s := 0
  t := 0

lemma shiftE20_smul : shiftE20 • E20 = E0 := by
  ext <;> norm_num [shiftE20, E20, E0, WeierstrassCurve.variableChange_def]

abbrev E20Point : Type :=
  WeierstrassCurve.Affine.Point E20

noncomputable def shiftE20PointAddEquiv :
    E20Point ≃+ WeierstrassCurve.Affine.Point (shiftE20 • E20) :=
  Scratch.TateZ2xZ10Reduction.variableChangePointAddEquiv E20 shiftE20

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

lemma add_P4_10_Pm1_0 : P4_10 + Pm1_0 = P0_m2 := by
  simpa [add_comm] using add_Pm1_0_P4_10

lemma add_P4_m10_Pm1_0 : P4_m10 + Pm1_0 = P0_2 := by
  simpa [add_comm] using add_Pm1_0_P4_m10

lemma add_P0_2_Pm1_0 : P0_2 + Pm1_0 = P4_m10 := by
  simpa [add_comm] using add_Pm1_0_P0_2

lemma add_P0_m2_Pm1_0 : P0_m2 + Pm1_0 = P4_10 := by
  simpa [add_comm] using add_Pm1_0_P0_m2

lemma add_P0_2_P4_10 : P0_2 + P4_10 = Pm1_0 := by
  unfold P0_2 P4_10 Pm1_0
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ =
    WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P4_10_P0_2 : P4_10 + P0_2 = Pm1_0 := by
  simpa [add_comm] using add_P0_2_P4_10

lemma add_P0_2_P4_m10 : P0_2 + P4_m10 = P4_10 := by
  unfold P0_2 P4_m10 P4_10
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ =
    WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P4_m10_P0_2 : P4_m10 + P0_2 = P4_10 := by
  simpa [add_comm] using add_P0_2_P4_m10

lemma add_P0_m2_P4_10 : P0_m2 + P4_10 = P4_m10 := by
  unfold P0_m2 P4_10 P4_m10
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 _ =
    WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P4_10_P0_m2 : P4_10 + P0_m2 = P4_m10 := by
  simpa [add_comm] using add_P0_m2_P4_10

lemma add_P0_m2_P4_m10 : P0_m2 + P4_m10 = Pm1_0 := by
  unfold P0_m2 P4_m10 Pm1_0
  change WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) _ +
      WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) _ =
    WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  norm_num [E20, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY]

lemma add_P4_m10_P0_m2 : P4_m10 + P0_m2 = Pm1_0 := by
  simpa [add_comm] using add_P0_m2_P4_m10

lemma add_P0_m2_P0_2 : P0_m2 + P0_2 = 0 := by
  simpa [add_comm] using add_P0_2_P0_m2

lemma add_P4_m10_P4_10 : P4_m10 + P4_10 = 0 := by
  simpa [add_comm] using add_P4_10_P4_m10

/-- The six visible points are closed under addition, with the explicit addition table above. -/
theorem knownPoint_add_table (i j : Fin 6) :
    knownPoint (knownAddIndex i j) = knownPoint i + knownPoint j := by
  fin_cases i <;> fin_cases j <;>
    simp [knownAddIndex, knownPoint, add_Pm1_0_self, add_P0_2_P0_m2,
      add_P0_2_P0_2, add_P0_m2_P0_m2, add_P4_10_P4_m10, add_P4_10_self,
      add_P4_m10_self, add_Pm1_0_P0_2, add_Pm1_0_P4_10, add_Pm1_0_P4_m10,
      add_Pm1_0_P0_m2, add_P4_10_Pm1_0, add_P4_m10_Pm1_0, add_P0_2_Pm1_0,
      add_P0_m2_Pm1_0, add_P0_2_P4_10, add_P4_10_P0_2, add_P0_2_P4_m10,
      add_P4_m10_P0_2, add_P0_m2_P4_10, add_P4_10_P0_m2, add_P0_m2_P4_m10,
      add_P4_m10_P0_m2, add_P0_m2_P0_2, add_P4_m10_P4_10]

lemma phi_lands
    {X y : ℚ}
    (hX : X ≠ 0)
    (hE : y ^ 2 = X ^ 3 - 2 * X ^ 2 + 5 * X) :
    let u := y ^ 2 / (4 * X ^ 2)
    let w := y * (5 - X ^ 2) / (8 * X ^ 2)
    w ^ 2 = u ^ 3 + u ^ 2 - u := by
  dsimp
  field_simp [hX]
  rw [hE]
  ring

lemma E0_affine_classification {X y : ℚ}
    (hE : y ^ 2 = X ^ 3 - 2 * X ^ 2 + 5 * X) :
    (X = 0 ∧ y = 0) ∨
      (X = 1 ∧ y = 2) ∨
      (X = 1 ∧ y = -2) ∨
      (X = 5 ∧ y = 10) ∨
      (X = 5 ∧ y = -10) := by
  by_cases hX : X = 0
  · left
    refine ⟨hX, ?_⟩
    subst X
    have hy2 : y ^ 2 = 0 := by nlinarith
    exact sq_eq_zero_iff.mp hy2
  · set u : ℚ := y ^ 2 / (4 * X ^ 2)
    set w : ℚ := y * (5 - X ^ 2) / (8 * X ^ 2)
    have hC : w ^ 2 = u ^ 3 + u ^ 2 - u := by
      subst u
      subst w
      exact phi_lands hX hE
    have hu_cases := _root_.obstruction_20a4 u w hC
    rcases hu_cases with hu | hu | hu
    · exfalso
      subst u
      field_simp [hX] at hu
      have hXsq_pos : 0 < X ^ 2 := sq_pos_of_ne_zero hX
      nlinarith [sq_nonneg y]
    · exfalso
      subst u
      field_simp [hX] at hu
      have hy2 : y ^ 2 = 0 := by nlinarith
      have hprod : X * (X ^ 2 - 2 * X + 5) = 0 := by nlinarith
      have hquad : X ^ 2 - 2 * X + 5 = 0 := by
        rcases mul_eq_zero.mp hprod with h0 | hq
        · exact False.elim (hX h0)
        · exact hq
      nlinarith [sq_nonneg (X - 1)]
    · right
      subst u
      field_simp [hX] at hu
      have hy2 : y ^ 2 = 4 * X ^ 2 := by nlinarith
      have hX_cases : X = 1 ∨ X = 5 := by
        have hprod : X * (X ^ 2 - 6 * X + 5) = 0 := by nlinarith
        have hquad : X ^ 2 - 6 * X + 5 = 0 := by
          rcases mul_eq_zero.mp hprod with h0 | hq
          · exact False.elim (hX h0)
          · exact hq
        have hf : (X - 1) * (X - 5) = 0 := by nlinarith
        rcases mul_eq_zero.mp hf with h1 | h5
        · left
          nlinarith
        · right
          nlinarith
      rcases hX_cases with hX1 | hX5
      · have hy2_four : y ^ 2 = (2 : ℚ) ^ 2 := by
          rw [hX1] at hy2
          norm_num at hy2 ⊢
          exact hy2
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2_four with hy | hy
        · left
          exact ⟨hX1, hy⟩
        · right
          left
          exact ⟨hX1, hy⟩
      · have hy2_hundred : y ^ 2 = (10 : ℚ) ^ 2 := by
          rw [hX5] at hy2
          norm_num at hy2 ⊢
          exact hy2
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2_hundred with hy | hy
        · right
          right
          left
          exact ⟨hX5, hy⟩
        · right
          right
          right
          exact ⟨hX5, hy⟩

/--
The visible points form a finite subgroup under addition.  Completeness of this
list as all rational points is proved below from the explicit 2-isogeny to the
already-discharged `20a4` obstruction.
-/
def knownPointSet : Set E20Point :=
  Set.range knownPoint

theorem knownPointSet_add_closed {P Q : E20Point}
    (hP : P ∈ knownPointSet) (hQ : Q ∈ knownPointSet) :
    P + Q ∈ knownPointSet := by
  rcases hP with ⟨i, rfl⟩
  rcases hQ with ⟨j, rfl⟩
  exact ⟨knownAddIndex i j, knownPoint_add_table i j⟩

private lemma knownPointSet_zero : (0 : E20Point) ∈ knownPointSet :=
  ⟨0, rfl⟩

private lemma knownPointSet_some_m1_0
    {h : WeierstrassCurve.Affine.Nonsingular E20 (-1 : ℚ) 0} :
    (WeierstrassCurve.Affine.Point.some (-1 : ℚ) 0 h : E20Point) ∈ knownPointSet := by
  refine ⟨3, ?_⟩
  unfold knownPoint Pm1_0
  unfold WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

private lemma knownPointSet_some_0_2
    {h : WeierstrassCurve.Affine.Nonsingular E20 (0 : ℚ) 2} :
    (WeierstrassCurve.Affine.Point.some (0 : ℚ) 2 h : E20Point) ∈ knownPointSet := by
  refine ⟨2, ?_⟩
  unfold knownPoint P0_2
  unfold WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

private lemma knownPointSet_some_0_m2
    {h : WeierstrassCurve.Affine.Nonsingular E20 (0 : ℚ) (-2)} :
    (WeierstrassCurve.Affine.Point.some (0 : ℚ) (-2) h : E20Point) ∈ knownPointSet := by
  refine ⟨4, ?_⟩
  unfold knownPoint P0_m2
  unfold WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

private lemma knownPointSet_some_4_10
    {h : WeierstrassCurve.Affine.Nonsingular E20 (4 : ℚ) 10} :
    (WeierstrassCurve.Affine.Point.some (4 : ℚ) 10 h : E20Point) ∈ knownPointSet := by
  refine ⟨1, ?_⟩
  unfold knownPoint P4_10
  unfold WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

private lemma knownPointSet_some_4_m10
    {h : WeierstrassCurve.Affine.Nonsingular E20 (4 : ℚ) (-10)} :
    (WeierstrassCurve.Affine.Point.some (4 : ℚ) (-10) h : E20Point) ∈ knownPointSet := by
  refine ⟨5, ?_⟩
  unfold knownPoint P4_m10
  unfold WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

theorem E20_rational_points_complete (P : E20Point) : P ∈ knownPointSet := by
  cases P with
  | zero =>
      exact knownPointSet_zero
  | some x y h =>
      have hE20 : y ^ 2 = x ^ 3 + x ^ 2 + 4 * x + 4 := by
        have hEq : WeierstrassCurve.Affine.Equation E20 x y := h.left
        rw [WeierstrassCurve.Affine.equation_iff] at hEq
        simpa [E20] using hEq
      have hE0 : y ^ 2 = (x + 1) ^ 3 - 2 * (x + 1) ^ 2 + 5 * (x + 1) := by
        rw [hE20]
        ring
      rcases E0_affine_classification hE0 with h00 | h12 | h1m2 | h510 | h5m10
      · rcases h00 with ⟨hX, hy⟩
        have hx : x = -1 := by linarith
        subst x
        subst y
        exact knownPointSet_some_m1_0
      · rcases h12 with ⟨hX, hy⟩
        have hx : x = 0 := by linarith
        subst x
        subst y
        exact knownPointSet_some_0_2
      · rcases h1m2 with ⟨hX, hy⟩
        have hx : x = 0 := by linarith
        subst x
        subst y
        exact knownPointSet_some_0_m2
      · rcases h510 with ⟨hX, hy⟩
        have hx : x = 4 := by linarith
        subst x
        subst y
        exact knownPointSet_some_4_10
      · rcases h5m10 with ⟨hX, hy⟩
        have hx : x = 4 := by linarith
        subst x
        subst y
        exact knownPointSet_some_4_m10

end MazurProof.ObstructionCurve
