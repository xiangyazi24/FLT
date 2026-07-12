import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Point transport under a Weierstrass variable change

This is the field-generic point-level counterpart of Mathlib's curve-level
variable-change action.
-/

namespace MazurProof.N18RouteC.VariableChangePoints

noncomputable section

variable {F : Type*} [Field F]

local instance : DecidableEq F := Classical.decEq F

/-- The transformed `X`-coordinate under a Weierstrass variable change.  This is
the inverse coordinate map from old coordinates on `W` to new coordinates on
`C • W`.
-/
def variableChangePointX (C : WeierstrassCurve.VariableChange F) (x : F) : F :=
  (C.u⁻¹ : F) ^ 2 * (x - C.r)

/-- The transformed `Y`-coordinate under a Weierstrass variable change. -/
def variableChangePointY (C : WeierstrassCurve.VariableChange F) (x y : F) : F :=
  (C.u⁻¹ : F) ^ 3 * (y - C.s * (x - C.r) - C.t)

/-- The old `x`-coordinate recovered from new coordinates. -/
def variableChangePointInvX (C : WeierstrassCurve.VariableChange F) (X : F) : F :=
  (C.u : F) ^ 2 * X + C.r

/-- The old `y`-coordinate recovered from new coordinates. -/
def variableChangePointInvY (C : WeierstrassCurve.VariableChange F) (X Y : F) : F :=
  (C.u : F) ^ 3 * Y + (C.u : F) ^ 2 * C.s * X + C.t

lemma variableChangePoint_equation
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) {x y : F}
    (h : WeierstrassCurve.Affine.Equation W x y) :
    WeierstrassCurve.Affine.Equation (C • W)
      (variableChangePointX C x) (variableChangePointY C x y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointX variableChangePointY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  simp only [Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  linear_combination h

lemma variableChangePointInv_equation
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) {X Y : F}
    (h : WeierstrassCurve.Affine.Equation (C • W) X Y) :
    WeierstrassCurve.Affine.Equation W
      (variableChangePointInvX C X) (variableChangePointInvY C X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointInvX variableChangePointInvY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆] at h
  simp only [Units.val_inv_eq_inv_val] at h
  field_simp [C.u.ne_zero] at h
  linear_combination h

lemma variableChangePointInvX_pointX
    (C : WeierstrassCurve.VariableChange F) (x : F) :
    variableChangePointInvX C (variableChangePointX C x) = x := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointInvY_pointY
    (C : WeierstrassCurve.VariableChange F) (x y : F) :
    variableChangePointInvY C (variableChangePointX C x) (variableChangePointY C x y) = y := by
  simp [variableChangePointInvY, variableChangePointX, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_invX
    (C : WeierstrassCurve.VariableChange F) (X : F) :
    variableChangePointX C (variableChangePointInvX C X) = X := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointY_invY
    (C : WeierstrassCurve.VariableChange F) (X Y : F) :
    variableChangePointY C (variableChangePointInvX C X)
      (variableChangePointInvY C X Y) = Y := by
  simp [variableChangePointInvX, variableChangePointInvY, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_eq_iff
    (C : WeierstrassCurve.VariableChange F) {x₁ x₂ : F} :
    variableChangePointX C x₁ = variableChangePointX C x₂ ↔ x₁ = x₂ := by
  unfold variableChangePointX
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linear_combination h
  · intro h
    simp [h]

lemma variableChangePointY_eq_iff
    (C : WeierstrassCurve.VariableChange F) (x : F) {y₁ y₂ : F} :
    variableChangePointY C x y₁ = variableChangePointY C x y₂ ↔ y₁ = y₂ := by
  unfold variableChangePointY
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linear_combination h
  · intro h
    simp [h]

lemma variableChangePointY_negY
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) (x y : F) :
    variableChangePointY C x (WeierstrassCurve.Affine.negY W x y) =
      WeierstrassCurve.Affine.negY (C • W)
        (variableChangePointX C x) (variableChangePointY C x y) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_slope_of_X_ne
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : F) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne]
  · unfold variableChangePointX variableChangePointY
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero, sub_ne_zero.mpr hx]
    ring
  · exact fun h => hx ((variableChangePointX_eq_iff C).mp h)

lemma variableChange_slope_of_Y_ne
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ ≠ WeierstrassCurve.Affine.negY W x₂ y₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : F) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  have hy_eq : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
  have hy_self : y₁ ≠ WeierstrassCurve.Affine.negY W x₁ y₁ := by
    intro h
    apply hy
    rw [← hx, ← hy_eq]
    exact h
  have hden : x₁ * W.a₁ + W.a₃ + y₁ * 2 ≠ 0 := by
    intro hden
    apply hy_self
    rw [WeierstrassCurve.Affine.negY]
    linear_combination hden
  have hmul :
      (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have htarget_hx :
      variableChangePointX C x₁ = variableChangePointX C x₂ := by
    simp [hx]
  have htarget_hy :
      variableChangePointY C x₁ y₁ ≠
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
    intro h
    apply hy
    rw [← hx]
    apply (variableChangePointY_eq_iff C x₁).mp
    rw [h]
    rw [hx, variableChangePointY_negY]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne htarget_hx htarget_hy]
  unfold variableChangePointX variableChangePointY
  simp [WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  rw [← sub_eq_zero]
  ring_nf
  convert
    (show C.s *
        (1 - (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹) = 0 by
      rw [hmul]
      ring) using 1
  ring

lemma variableChange_slope
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : F) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  by_cases hx : x₁ = x₂
  · exact variableChange_slope_of_Y_ne W C h₁ h₂ hx (fun hy => hxy ⟨hx, hy⟩)
  · exact variableChange_slope_of_X_ne W C hx

lemma variableChange_nonvertical
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    ¬(variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂)) := by
  rintro ⟨hx', hy'⟩
  apply hxy
  have hx : x₁ = x₂ := (variableChangePointX_eq_iff C).mp hx'
  refine ⟨hx, ?_⟩
  rw [← hx]
  apply (variableChangePointY_eq_iff C x₁).mp
  rw [hy', hx, ← variableChangePointY_negY]

lemma variableChange_vertical
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂) :
    variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
  rcases hxy with ⟨hx, hy⟩
  constructor
  · simp [hx]
  · rw [hy, ← variableChangePointY_negY, hx]

lemma variableChange_addX
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    (x₁ x₂ ℓ : F) :
    variableChangePointX C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ) =
      WeierstrassCurve.Affine.addX (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        ((C.u⁻¹ : F) * (ℓ - C.s)) := by
  simp [variableChangePointX, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_addY
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    (x₁ x₂ y₁ ℓ : F) :
    variableChangePointY C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ)
        (WeierstrassCurve.Affine.addY W x₁ x₂ y₁ ℓ) =
      WeierstrassCurve.Affine.addY (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) ((C.u⁻¹ : F) * (ℓ - C.s)) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

noncomputable def variableChangePointMap
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point W → WeierstrassCurve.Affine.Point (C • W)
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some x y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointX C x) (variableChangePointY C x y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePoint_equation W C h.left))

noncomputable def variableChangePointMapInv
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point (C • W) → WeierstrassCurve.Affine.Point W
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some X Y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointInvX C X) (variableChangePointInvY C X Y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePointInv_equation W C h.left))

@[simp] lemma variableChangePointMap_zero
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    variableChangePointMap W C 0 = 0 :=
  rfl

lemma variableChangePointMap_leftInverse
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    Function.LeftInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointInvX_pointX, variableChangePointInvY_pointY]

lemma variableChangePointMap_rightInverse
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    Function.RightInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some X Y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointX_invX, variableChangePointY_invY]

noncomputable def variableChangePointEquiv
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point W ≃ WeierstrassCurve.Affine.Point (C • W) where
  toFun := variableChangePointMap W C
  invFun := variableChangePointMapInv W C
  left_inv := variableChangePointMap_leftInverse W C
  right_inv := variableChangePointMap_rightInverse W C

lemma variableChangePointMap_neg
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F)
    (P : WeierstrassCurve.Affine.Point W) :
    variableChangePointMap W C (-P) = -variableChangePointMap W C P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [variableChangePointMap, WeierstrassCurve.Affine.Point.neg_some]
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, variableChangePointY_negY W C x y⟩

lemma variableChangePointMap_add
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F)
    (P Q : WeierstrassCurve.Affine.Point W) :
    variableChangePointMap W C (P + Q) =
      variableChangePointMap W C P + variableChangePointMap W C Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂
      · have htarget := variableChange_vertical W C hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq htarget.left htarget.right]
      · have htarget := variableChange_nonvertical W C hxy
        have hslope := variableChange_slope W C h₁.left h₂.left hxy
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_some htarget]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · change
            variableChangePointX C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addX W C x₁ x₂
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)
        · change
            variableChangePointY C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂))
                (WeierstrassCurve.Affine.addY W x₁ x₂ y₁
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (variableChangePointY C x₁ y₁)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addY W C x₁ x₂ y₁
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)

noncomputable def variableChangePointAddEquiv
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point (C • W) :=
  AddEquiv.mk (variableChangePointEquiv W C) (variableChangePointMap_add W C)

end

end MazurProof.N18RouteC.VariableChangePoints
