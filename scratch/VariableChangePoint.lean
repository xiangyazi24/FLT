import Mathlib

open WeierstrassCurve

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : Affine F) [W.IsElliptic]
variable (r s t : F)

private abbrev vc : VariableChange F := ⟨1, r, s, t⟩
private abbrev W' : Affine F := vc r s t • W

private theorem equation_vc (x y : F) :
    W.Equation x y ↔ (W' W r s t).Equation (x - r) (y - s * (x - r) - t) := by
  simp only [equation_iff, W', vc, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, inv_one, one_pow, Units.val_one, one_mul]
  constructor <;> intro h <;> linear_combination h

private theorem nonsingular_vc {x y : F} (h : W.Nonsingular x y) :
    (W' W r s t).Nonsingular (x - r) (y - s * (x - r) - t) :=
  equation_iff_nonsingular.mp ((equation_vc W r s t x y).mp h.1)

private theorem negY_vc (x y : F) :
    (W' W r s t).negY (x - r) (y - s * (x - r) - t) =
    W.negY x y - s * (x - r) - t := by
  simp only [negY, W', vc, variableChange_a₁, variableChange_a₃, inv_one, one_pow,
    Units.val_one, one_mul]
  ring

private theorem addX_vc (x₁ x₂ ℓ : F) :
    (W' W r s t).addX (x₁ - r) (x₂ - r) (ℓ - s) = W.addX x₁ x₂ ℓ - r := by
  simp only [addX, W', vc, variableChange_a₁, variableChange_a₂, inv_one, one_pow,
    Units.val_one, one_mul]
  ring

private theorem addY_vc (x₁ x₂ y₁ ℓ : F) :
    (W' W r s t).addY (x₁ - r) (x₂ - r) (y₁ - s * (x₁ - r) - t) (ℓ - s) =
    W.addY x₁ x₂ y₁ ℓ - s * (W.addX x₁ x₂ ℓ - r) - t := by
  simp only [addY, negY, negAddY, addX, W', vc, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, inv_one, one_pow, Units.val_one, one_mul]
  ring

private theorem slope_vc_of_X_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    (W' W r s t).slope (x₁ - r) (x₂ - r)
      (y₁ - s * (x₁ - r) - t) (y₂ - s * (x₂ - r) - t) =
    W.slope x₁ x₂ y₁ y₂ - s := by
  have hx' : x₁ - r ≠ x₂ - r := by
    intro h; exact hx (show x₁ = x₂ by linear_combination h)
  rw [slope_of_X_ne hx', slope_of_X_ne hx]
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  field_simp [hd]
  ring

private theorem slope_vc_of_Y_ne {x₁ y₁ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₁ y₂)
    (hy : y₁ ≠ W.negY x₁ y₂) :
    (W' W r s t).slope (x₁ - r) (x₁ - r)
      (y₁ - s * (x₁ - r) - t) (y₂ - s * (x₁ - r) - t) =
    W.slope x₁ x₁ y₁ y₂ - s := by
  have heq : y₁ = y₂ := (Y_eq_of_X_eq h₁.1 h₂.1 rfl).resolve_right hy
  have hne : y₁ ≠ W.negY x₁ y₁ := by
    rwa [show W.negY x₁ y₁ = W.negY x₁ y₂ from by rw [heq]]
  have hy' : y₁ - s * (x₁ - r) - t ≠
      (W' W r s t).negY (x₁ - r) (y₂ - s * (x₁ - r) - t) := by
    rw [negY_vc]; intro h
    exact hy (show y₁ = W.negY x₁ y₂ by
      simp only [negY] at h ⊢; linear_combination h)
  rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy]
  simp only [negY, W', vc, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, inv_one, one_pow, Units.val_one, one_mul]
  have hd : y₁ - (-y₁ - W.a₁ * x₁ - W.a₃) ≠ 0 := by
    intro h; exact hne (show y₁ = W.negY x₁ y₁ by
      simp only [negY]; linear_combination h)
  ring_nf at hd ⊢
  field_simp [hd]
  ring

private theorem slope_vc {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    (W' W r s t).slope (x₁ - r) (x₂ - r)
      (y₁ - s * (x₁ - r) - t) (y₂ - s * (x₂ - r) - t) =
    W.slope x₁ x₂ y₁ y₂ - s := by
  by_cases hx : x₁ = x₂
  · subst hx
    exact slope_vc_of_Y_ne W r s t h₁ h₂ (fun h => hxy ⟨rfl, h⟩)
  · exact slope_vc_of_X_ne W r s t hx

/-! ### The point map -/

private noncomputable def vcPointFun :
    W.Point → (W' W r s t).Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (nonsingular_vc W r s t h)

@[simp]
private theorem vcPointFun_zero :
    vcPointFun W r s t (0 : W.Point) = 0 := rfl

@[simp]
private theorem vcPointFun_some {x y : F} (h : W.Nonsingular x y) :
    vcPointFun W r s t (.some x y h) =
    Point.some (x - r) (y - s * (x - r) - t) (nonsingular_vc W r s t h) := rfl

private theorem vcPointFun_add (P Q : W.Point) :
    vcPointFun W r s t (P + Q) =
    vcPointFun W r s t P + vcPointFun W r s t Q := by
  match P, Q with
  | .zero, _ => rfl
  | _, .zero => show vcPointFun W r s t (_ + 0) = vcPointFun W r s t _ + vcPointFun W r s t 0
                rw [add_zero, vcPointFun_zero, add_zero]
  | Point.some x₁ y₁ h₁, Point.some x₂ y₂ h₂ =>
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2, vcPointFun_zero]
      simp only [vcPointFun_some]
      exact (Point.add_of_Y_eq (show x₁ - r = x₂ - r from by rw [hxy.1])
        (show y₁ - s * (x₁ - r) - t =
          (W' W r s t).negY (x₂ - r) (y₂ - s * (x₂ - r) - t) from by
          rw [negY_vc, hxy.2, hxy.1])).symm
    · have hxy' : ¬(x₁ - r = x₂ - r ∧
          y₁ - s * (x₁ - r) - t =
            (W' W r s t).negY (x₂ - r) (y₂ - s * (x₂ - r) - t)) := by
        intro ⟨hx', hy'⟩
        have hx : x₁ = x₂ := by linear_combination hx'
        subst hx
        rw [negY_vc] at hy'
        exact hxy ⟨rfl, show y₁ = W.negY x₁ y₂ by
          simp only [negY] at hy' ⊢; linear_combination hy'⟩
      simp only [Point.add_some hxy, vcPointFun_some, Point.add_some hxy',
        Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [slope_vc W r s t h₁ h₂ hxy, addX_vc]
      · rw [slope_vc W r s t h₁ h₂ hxy, addY_vc]

/-- The injective `AddMonoidHom` from `W.Point` to `(C • W).Point`
for a u=1 variable change `C = ⟨1, r, s, t⟩`. -/
noncomputable def variableChangePoint :
    W.Point →+ (W' W r s t).Point where
  toFun := vcPointFun W r s t
  map_zero' := rfl
  map_add' := vcPointFun_add W r s t

theorem variableChangePoint_injective :
    Function.Injective (variableChangePoint W r s t) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) heq
  · rfl
  · simp only [variableChangePoint, AddMonoidHom.coe_mk, ZeroHom.coe_mk, vcPointFun] at heq
    exact absurd heq.symm (Point.some_ne_zero _)
  · simp only [variableChangePoint, AddMonoidHom.coe_mk, ZeroHom.coe_mk, vcPointFun] at heq
    exact absurd heq (Point.some_ne_zero _)
  · simp only [variableChangePoint, AddMonoidHom.coe_mk, ZeroHom.coe_mk, vcPointFun,
      Point.some.injEq] at heq
    rw [Point.some.injEq]
    have hx : x₁ = x₂ := by linear_combination heq.1
    subst hx; exact ⟨rfl, by linear_combination heq.2⟩

end WeierstrassCurve.Affine
