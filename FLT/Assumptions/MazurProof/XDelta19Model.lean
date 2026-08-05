import Mathlib
import FLT.Assumptions.MazurProof.TateOriginDivision

/-!
# The elliptic intermediate quotient at level nineteen

The order-three diamond quotient used in the order-nineteen argument has
minimal equation

`v² + v = u³ + u² + u`.

For the arithmetic descent it is convenient to use the integral short model

`Y² = X³ + (2X+4)²`,

obtained from the minimal model by `X=4u` and `Y=8v+4`.  This file records
the two models and the explicit degree-three isogeny pair used below.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.XDelta19Model

open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

/-! ## Minimal and integral short models -/

/-- The minimal genus-one quotient, Cremona label `19a3`. -/
def minimalCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 1
  a₄ := 1
  a₆ := 0

/-- The affine equation of the minimal genus-one quotient. -/
def OnMinimal (u v : ℚ) : Prop :=
  v ^ 2 + v = u ^ 3 + u ^ 2 + u

/-- The minimal model has discriminant `-19`. -/
theorem minimalCurve_delta : minimalCurve.Δ = (-19 : ℚ) := by
  norm_num [minimalCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The minimal model is nonsingular. -/
instance minimalCurve_isElliptic : minimalCurve.IsElliptic where
  isUnit := by
    rw [minimalCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed minimal equation. -/
@[simp] theorem minimalCurve_equation_iff (u v : ℚ) :
    WeierstrassCurve.Affine.Equation minimalCurve u v ↔ OnMinimal u v := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [minimalCurve, OnMinimal]

/-- The integral short model used for the three-isogeny descent. -/
def shortCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 4
  a₃ := 0
  a₄ := 16
  a₆ := 16

/-- The affine equation of the integral short model. -/
def OnShort (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + (2 * x + 4) ^ 2

/-- The short model has nonzero discriminant. -/
theorem shortCurve_delta : shortCurve.Δ = (-77824 : ℚ) := by
  norm_num [shortCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The integral short model is nonsingular. -/
instance shortCurve_isElliptic : shortCurve.IsElliptic where
  isUnit := by
    rw [shortCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed short equation. -/
@[simp] theorem shortCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation shortCurve x y ↔ OnShort x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortCurve, OnShort]
  ring_nf

/-- The coordinate change from the minimal model to the short model. -/
theorem minimal_to_short {u v : ℚ} (h : OnMinimal u v) :
    OnShort (4 * u) (8 * v + 4) := by
  unfold OnMinimal at h
  unfold OnShort
  linear_combination 64 * h

/-- The inverse coordinate change from the short model to the minimal
model. -/
theorem short_to_minimal {x y : ℚ} (h : OnShort x y) :
    OnMinimal (x / 4) ((y - 4) / 8) := by
  unfold OnShort at h
  unfold OnMinimal
  linear_combination h / 64

/-- Rational-point classification on the short model implies the required
classification on the minimal model. -/
theorem minimal_x_eq_zero_of_short_x_eq_zero
    (hshort : ∀ x y : ℚ, OnShort x y → x = 0)
    {u v : ℚ} (h : OnMinimal u v) :
    u = 0 := by
  have hx : 4 * u = 0 :=
    hshort (4 * u) (8 * v + 4) (minimal_to_short h)
  linarith

/-! ## The first degree-three isogeny -/

/-- The scaled Vélu quotient of the short model. -/
def dualCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -108
  a₃ := 0
  a₄ := -8208
  a₆ := -155952

/-- The affine equation of the scaled Vélu quotient. -/
def OnDual (s t : ℚ) : Prop :=
  t ^ 2 = s ^ 3 - 3 * (6 * s + 228) ^ 2

/-- The scaled Vélu quotient has nonzero discriminant. -/
theorem dualCurve_delta : dualCurve.Δ = (-14930550042624 : ℚ) := by
  norm_num [dualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The scaled Vélu quotient is nonsingular. -/
instance dualCurve_isElliptic : dualCurve.IsElliptic where
  isUnit := by
    rw [dualCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed dual equation. -/
@[simp] theorem dualCurve_equation_iff (s t : ℚ) :
    WeierstrassCurve.Affine.Equation dualCurve s t ↔ OnDual s t := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [dualCurve, OnDual]
  ring_nf

/-- Horizontal coordinate of the degree-three Vélu map. -/
def threeIsogenyX (x : ℚ) : ℚ :=
  (9 * x ^ 3 + 48 * x ^ 2 + 288 * x + 576) / x ^ 2

/-- Vertical coordinate of the degree-three Vélu map. -/
def threeIsogenyY (x y : ℚ) : ℚ :=
  (27 * x ^ 3 * y - 864 * x * y - 3456 * y) / x ^ 3

/-- The degree-three Vélu map carries the short curve to its scaled
quotient. -/
theorem threeIsogeny_on_curve {x y : ℚ} (hx : x ≠ 0)
    (h : OnShort x y) :
    OnDual (threeIsogenyX x) (threeIsogenyY x y) := by
  unfold OnShort at h
  unfold OnDual threeIsogenyX threeIsogenyY
  field_simp [hx]
  simp_rw [h]
  ring

/-- Horizontal coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyX (s : ℚ) : ℚ :=
  (s ^ 3 - 144 * s ^ 2 - 16416 * s - 623808) / (81 * s ^ 2)

/-- Vertical coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyY (s t : ℚ) : ℚ :=
  (s ^ 3 * t + 16416 * s * t + 1247616 * t) / (729 * s ^ 3)

/-- The dual degree-three isogeny carries the scaled quotient back to the
short curve. -/
theorem dualThreeIsogeny_on_curve {s t : ℚ} (hs : s ≠ 0)
    (h : OnDual s t) :
    OnShort (dualThreeIsogenyX s) (dualThreeIsogenyY s t) := by
  unfold OnDual at h
  unfold OnShort dualThreeIsogenyX dualThreeIsogenyY
  field_simp [hs]
  simp_rw [h]
  ring

/-! ## Bundled point maps -/

/-- Rational points on the integral short model. -/
abbrev ShortPoint := Point shortCurve

/-- Rational points on the scaled Vélu quotient. -/
abbrev DualPoint := Point dualCurve

/-- A rational affine point on the scaled quotient cannot have first
coordinate zero. -/
theorem dual_x_ne_zero_of_on_curve {s t : ℚ}
    (h : OnDual s t) : s ≠ 0 := by
  intro hs
  rw [hs] at h
  norm_num [OnDual] at h
  nlinarith [sq_nonneg t]

/-- The bundled dual degree-three isogeny. -/
noncomputable def dualThreeIsogenyPoint : DualPoint → ShortPoint
  | .zero => .zero
  | .some s _t h =>
      if hs : s = 0 then .zero
      else Point.mk
        (shortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (dualCurve_equation_iff _ _ |>.1 h.1))

/-- The bundled dual isogeny fixes the point at infinity. -/
@[simp] theorem dualThreeIsogenyPoint_zero :
    dualThreeIsogenyPoint 0 = 0 := rfl

/-- The bundled dual isogeny is given by the displayed affine formulas away
from the empty exceptional divisor. -/
theorem dualThreeIsogenyPoint_some_of_x_ne_zero {s t : ℚ}
    (h : Nonsingular dualCurve s t) (hs : s ≠ 0) :
    dualThreeIsogenyPoint (.some s t h) =
      Point.mk
        (shortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (dualCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualThreeIsogenyPoint, hs]

/-! ## Visible rational three-torsion -/

/-- Every affine short-model point with first coordinate zero is killed by
three. -/
theorem three_nsmul_of_x_zero {x y : ℚ}
    (h : Nonsingular shortCurve x y) (hx : x = 0) :
    3 • (Point.some x y h : Point shortCurve) = 0 := by
  apply (TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval
    shortCurve h).mpr
  rw [shortCurve.ΨSq_ofNat 3]
  simp [show ¬ Even (3 : ℕ) by decide,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, shortCurve, hx]
  norm_num

/-- Nonsingularity of the positive visible flex. -/
theorem shortT_nonsingular : Nonsingular shortCurve (0 : ℚ) 4 :=
  equation_iff_nonsingular.mp <|
    (shortCurve_equation_iff 0 4).mpr (by norm_num [OnShort])

/-- Nonsingularity of the negative visible flex. -/
theorem shortTNeg_nonsingular : Nonsingular shortCurve (0 : ℚ) (-4) :=
  equation_iff_nonsingular.mp <|
    (shortCurve_equation_iff 0 (-4)).mpr (by norm_num [OnShort])

/-- The positive flex on the short model. -/
def shortT : Point shortCurve :=
  Point.some 0 4 shortT_nonsingular

/-- The negative flex on the short model. -/
def shortTNeg : Point shortCurve :=
  Point.some 0 (-4) shortTNeg_nonsingular

/-- The positive visible flex is killed by three. -/
theorem three_nsmul_shortT : 3 • shortT = 0 := by
  exact three_nsmul_of_x_zero shortT_nonsingular rfl

/-- The negative visible flex is the group inverse of the positive flex. -/
theorem shortTNeg_eq_neg : shortTNeg = -shortT := by
  rw [shortTNeg, shortT, Point.neg_some, Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY, shortCurve]

/-- The two visible affine flexes are distinct. -/
theorem shortT_ne_shortTNeg : shortT ≠ shortTNeg := by
  intro h
  rw [shortT, shortTNeg, Point.some.injEq] at h
  norm_num at h

end

end MazurProof.XDelta19Model
