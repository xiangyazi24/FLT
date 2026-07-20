import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import FLT.Assumptions.MazurProof.N18RouteC_VariableChangePoints
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.CyclicExclusion20

/-!
# Vélu 2-isogeny construction

Explicit Vélu formulas for degree-2 isogenies of elliptic curves over ℚ,
replacing `exists_rational_two_isogeny_quotient`.

## Strategy

Work in short Weierstrass form y² = x³ + Ax + B with 2-torsion Q = (r, 0).
Vélu formulas:
- E' : y² = x³ + A'x + B', A' = A - 5t, B' = B - 7rt, t = 3r² + A
- φ(x,y) = (x + t/(x-r), y·((x-r)²-t)/(x-r)²)
- η = (-2r, 0) ∈ E'[2]

For general Weierstrass, reduce to short form via `VariableChangePointAddEquiv`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.VeluTwoIsogeny

noncomputable section

local instance : DecidableEq ℚ := Classical.decEq ℚ

open WeierstrassCurve.Affine (Equation Nonsingular Point equation_iff_nonsingular
  equation_iff negY slope addX addY)

/-! ## Short Weierstrass definitions -/

def shortWS (A B : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := 0; a₃ := 0; a₄ := A; a₆ := B

def veluT (A r : ℚ) : ℚ := 3 * r ^ 2 + A

def veluQuotCurve (A B r : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := 0; a₃ := 0
  a₄ := A - 5 * veluT A r
  a₆ := B - 7 * r * veluT A r

/-! ## Equation lemmas -/

lemma shortWS_equation {A B x y : ℚ} :
    Equation (shortWS A B) x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  simp only [equation_iff, shortWS]; constructor <;> intro h <;> linarith

lemma veluQuotCurve_equation {A B r x y : ℚ} :
    Equation (veluQuotCurve A B r) x y ↔
    y ^ 2 = x ^ 3 + (A - 5 * veluT A r) * x + (B - 7 * r * veluT A r) := by
  simp only [equation_iff, veluQuotCurve]; constructor <;> intro h <;> linarith

/-! ## Well-definedness -/

lemma velu_equation {A B r x y : ℚ}
    (hcurve : Equation (shortWS A B) x y)
    (htors : r ^ 3 + A * r + B = 0)
    (hx : x ≠ r) :
    Equation (veluQuotCurve A B r)
      (x + veluT A r / (x - r))
      (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) := by
  rw [veluQuotCurve_equation]
  have hcurve' := shortWS_equation.mp hcurve
  have hd : x - r ≠ 0 := sub_ne_zero.mpr hx
  unfold veluT
  field_simp
  linear_combination
    (A ^ 2 + 4 * A * r ^ 2 + 4 * A * r * x - 2 * A * x ^ 2 +
     4 * r ^ 4 + 8 * r ^ 3 * x - 4 * r * x ^ 3 + x ^ 4) * hcurve' +
    (A ^ 2 + 4 * A * r ^ 2 + 4 * A * r * x - 2 * A * x ^ 2 +
     3 * r ^ 4 + 12 * r ^ 3 * x - 6 * r ^ 2 * x ^ 2) * htors

/-! ## IsElliptic instances -/

lemma shortWS_Δ (A B : ℚ) :
    (shortWS A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp [shortWS, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma shortWS_Δ_factor {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    (shortWS A B).Δ = -16 * (A + 3 * r ^ 2) ^ 2 * (4 * A + 3 * r ^ 2) := by
  rw [shortWS_Δ]
  have hB : B = -r ^ 3 - A * r := by linarith
  rw [hB]; ring

lemma veluQuotCurve_Δ_factor {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    (veluQuotCurve A B r).Δ = 256 * (A + 3 * r ^ 2) * (4 * A + 3 * r ^ 2) ^ 2 := by
  simp only [veluQuotCurve, veluT, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hB : B = -r ^ 3 - A * r := by linarith
  rw [hB]; ring

lemma veluQuotCurve_isElliptic {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hE : (shortWS A B).IsElliptic) :
    (veluQuotCurve A B r).IsElliptic := by
  have hΔ := hE.isUnit
  rw [shortWS_Δ_factor htors] at hΔ
  have hne := isUnit_iff_ne_zero.mp hΔ
  have h1 : A + 3 * r ^ 2 ≠ 0 := by intro h; apply hne; simp [h]
  have h2 : 4 * A + 3 * r ^ 2 ≠ 0 := by intro h; apply hne; simp [h]
  constructor
  rw [veluQuotCurve_Δ_factor htors]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (256 : ℚ) ≠ 0) h1)
    (pow_ne_zero 2 h2)).isUnit

/-! ## The Vélu point map -/

def veluMapPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (shortWS A B) → Point (veluQuotCurve A B r)
  | .zero => .zero
  | .some x y h =>
    if hx : x = r then .zero
    else
      .some (x + veluT A r / (x - r))
        (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2)
        (equation_iff_nonsingular.mp (velu_equation h.left htors hx))

@[simp] lemma veluMapPoint_zero {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    veluMapPoint htors (0 : Point (shortWS A B)) = 0 := rfl

/-! ## Kernel -/

lemma torsion_point_on_curve {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    Nonsingular (shortWS A B) r 0 :=
  equation_iff_nonsingular.mp (shortWS_equation.mpr (by nlinarith))

def torsionPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    Point (shortWS A B) :=
  .some r 0 (torsion_point_on_curve htors)

@[simp] lemma veluMapPoint_torsion {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    veluMapPoint htors (torsionPoint htors) = 0 := by
  show veluMapPoint htors (torsionPoint htors) = Point.zero
  unfold veluMapPoint torsionPoint; simp

lemma veluMapPoint_eq_zero_iff {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P : Point (shortWS A B)) :
    veluMapPoint htors P = 0 ↔
      P = 0 ∨ P = torsionPoint htors := by
  constructor
  · intro h
    match P with
    | .zero => exact Or.inl rfl
    | .some x y hns =>
      unfold veluMapPoint at h
      by_cases hx : x = r
      · right
        have hcurve := shortWS_equation.mp hns.left
        rw [hx] at hcurve
        have hy2 : y ^ 2 = 0 := by linarith
        have hy : y = 0 := by nlinarith [sq_nonneg y]
        subst hx; subst hy
        simp [torsionPoint]
      · simp only [hx, dite_false] at h
        exact absurd h (Point.some_ne_zero _)
  · rintro (rfl | rfl)
    · exact veluMapPoint_zero
    · exact veluMapPoint_torsion

/-! ## Homomorphism -/

lemma veluMapPoint_add {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P Q : Point (shortWS A B)) :
    veluMapPoint htors (P + Q) =
      veluMapPoint htors P + veluMapPoint htors Q := by
  sorry

def veluMapHom {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (shortWS A B) →+ Point (veluQuotCurve A B r) where
  toFun := veluMapPoint htors
  map_zero' := veluMapPoint_zero
  map_add' := veluMapPoint_add

/-! ## η = (-2r, 0) on E' -/

lemma eta_on_curve {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    Equation (veluQuotCurve A B r) (-2 * r) 0 := by
  rw [veluQuotCurve_equation]
  unfold veluT
  nlinarith

lemma eta_nonsingular {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Nonsingular (veluQuotCurve A B r) (-2 * r) 0 :=
  equation_iff_nonsingular.mp (eta_on_curve htors)

def etaPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (veluQuotCurve A B r) :=
  .some (-2 * r) 0 (eta_nonsingular htors)

lemma etaPoint_add_self {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    etaPoint htors + etaPoint htors = 0 := by
  exact Point.add_self_of_Y_eq (by simp [negY, veluQuotCurve])

lemma etaPoint_ne_zero {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    etaPoint htors ≠ 0 :=
  Point.some_ne_zero _

lemma etaPoint_order {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    addOrderOf (etaPoint htors) = 2 := by
  exact addOrderOf_eq_prime (by rw [two_nsmul]; exact etaPoint_add_self htors)
    (etaPoint_ne_zero htors)

/-! ## Dual isogeny

The dual φ̂ : E' → E is the Vélu map from E' with kernel ⟨η⟩ = ⟨(-2r,0)⟩,
composed with the isomorphism C • E ≃ E'' where C = (2, 0, 0, 0).
The Vélu quotient E'/(η) has coefficients (16A, 64B) = C • (shortWS A B). -/

def dualMapHom {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (veluQuotCurve A B r) →+ Point (shortWS A B) where
  toFun := sorry
  map_zero' := sorry
  map_add' := sorry

/-! ## Properties -/

lemma dual_comp_phi {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P : Point (shortWS A B)) :
    dualMapHom htors (veluMapHom htors P) = 2 • P := by
  sorry

lemma dual_eta_eq_zero {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    dualMapHom htors (etaPoint htors) = 0 := by
  sorry

/-! ## General Weierstrass → Short WS reduction -/

section GeneralToShort

variable (E : WeierstrassCurve ℚ)

def toShortWSChange : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := -(E.a₁ ^ 2 + 4 * E.a₂) / 12
  s := -E.a₁ / 2
  t := -(E.a₃ + (-(E.a₁ ^ 2 + 4 * E.a₂) / 12) * E.a₁) / 2

lemma toShortWSChange_isShortWS :
    (toShortWSChange E • E).a₁ = 0 ∧
    (toShortWSChange E • E).a₂ = 0 ∧
    (toShortWSChange E • E).a₃ = 0 := by
  simp only [toShortWSChange, WeierstrassCurve.variableChange_def]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

end GeneralToShort

/-! ## Main theorem -/

theorem exists_rational_two_isogeny_quotient_proved
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {Q : (E⁄ℚ).Point} (hQ : addOrderOf Q = 2) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (phi : (E⁄ℚ).Point →+ (E'⁄ℚ).Point)
      (dual : (E'⁄ℚ).Point →+ (E⁄ℚ).Point)
      (eta : (E'⁄ℚ).Point),
      addOrderOf eta = 2 ∧
      (∀ R, phi R = 0 ↔ R = 0 ∨ R = Q) ∧
      (∀ R, dual (phi R) = 2 • R) ∧ dual eta = 0 := by
  sorry

end
end MazurProof.VeluTwoIsogeny
