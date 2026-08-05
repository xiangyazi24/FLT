import FLT.Assumptions.MazurProof.XDelta19Model

/-!
# The degree-three isogeny identity at level nineteen

This file bundles the forward Vélu map from the short model

`y² = x³ + (2x+4)²`

to its scaled quotient and verifies directly that the dual map composed
with the forward map is multiplication by three.  The verification uses
the affine chord-and-tangent formulas, including the exceptional
three-torsion fibre `x=0`.
-/

namespace MazurProof.XDelta19Isogeny

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.XDelta19Model
open Polynomial

noncomputable section

/-! ## Bundling the forward isogeny -/

/-- Away from the kernel, the horizontal coordinate of the forward
three-isogeny is nonzero. -/
theorem threeIsogenyX_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnShort x y) :
    threeIsogenyX x ≠ 0 :=
  dual_x_ne_zero_of_on_curve (threeIsogeny_on_curve hx h)

/-- The bundled forward degree-three isogeny.  Its exceptional affine
fibre is exactly the visible kernel with first coordinate zero. -/
noncomputable def threeIsogenyPoint : ShortPoint → DualPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else Point.mk
        (dualCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx
            (shortCurve_equation_iff _ _ |>.1 h.1))

/-- The forward isogeny fixes the point at infinity. -/
@[simp] theorem threeIsogenyPoint_zero :
    threeIsogenyPoint 0 = 0 := rfl

/-- Away from its kernel, the bundled forward map is given by the
displayed Vélu formulas. -/
theorem threeIsogenyPoint_some_of_x_ne_zero {x y : ℚ}
    (h : Nonsingular shortCurve x y) (hx : x ≠ 0) :
    threeIsogenyPoint (.some x y h) =
      Point.mk
        (dualCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx
            (shortCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [threeIsogenyPoint, hx]

/-! ## Explicit tripling coordinates -/

/-- Negation on the short model changes only the sign of the vertical
coordinate. -/
@[simp] theorem shortCurve_negY (x y : ℚ) :
    negY shortCurve x y = -y := by
  simp [negY, shortCurve]

/-- The short Weierstrass cubic has no rational root. -/
private theorem shortCubic_ne_zero (x : ℚ) :
    x ^ 3 + 4 * x ^ 2 + 16 * x + 16 ≠ 0 := by
  intro h
  let p : ℤ[X] := X ^ 3 + C 4 * X ^ 2 + C 16 * X + C 16
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval x p = 0 := by
    simp [p, aeval_def]
    norm_cast
  obtain ⟨z, hx, _hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  rw [hx] at h
  have hz : z ^ 3 + 4 * z ^ 2 + 16 * z + 16 = 0 := by
    have hzcast :
        ((z ^ 3 + 4 * z ^ 2 + 16 * z + 16 : ℤ) : ℚ) = 0 := by
      push_cast
      exact h
    exact_mod_cast hzcast
  have hzmod : (z : ZMod 5) ^ 3 + 4 * (z : ZMod 5) ^ 2 +
      16 * (z : ZMod 5) + 16 = 0 := by
    have hz' := congrArg (fun n : ℤ => (n : ZMod 5)) hz
    push_cast at hz'
    exact hz'
  exact (by decide : ∀ u : ZMod 5,
    u ^ 3 + 4 * u ^ 2 + 16 * u + 16 ≠ 0) (z : ZMod 5) hzmod

/-- An affine rational point on the short model never has zero vertical
coordinate. -/
private theorem short_y_ne_zero {x y : ℚ} (h : OnShort x y) :
    y ≠ 0 := by
  intro hy
  apply shortCubic_ne_zero x
  unfold OnShort at h
  rw [hy] at h
  norm_num at h
  linear_combination -h

/-- The tangent slope at an affine point of the short model. -/
private def shortTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 + 8 * x + 16) / (2 * y)

/-- Horizontal coordinate of twice an affine point. -/
private def shortDoubleX (x y : ℚ) : ℚ :=
  shortTangent x y ^ 2 - 4 - 2 * x

/-- Vertical coordinate of twice an affine point. -/
private def shortDoubleY (x y : ℚ) : ℚ :=
  -(shortTangent x y * (shortDoubleX x y - x) + y)

/-- Slope of the line from twice a point back to the original point. -/
private def shortTripleSlope (x y : ℚ) : ℚ :=
  (shortDoubleY x y - y) / (shortDoubleX x y - x)

/-- Horizontal coordinate of three times an affine point. -/
private def shortTripleX (x y : ℚ) : ℚ :=
  shortTripleSlope x y ^ 2 - 4 - shortDoubleX x y - x

/-- Vertical coordinate of three times an affine point. -/
private def shortTripleY (x y : ℚ) : ℚ :=
  -(shortTripleSlope x y *
      (shortTripleX x y - shortDoubleX x y) + shortDoubleY x y)

/-- The library tangent slope agrees with the displayed rational
function. -/
private theorem shortCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    slope shortCurve x x y y = shortTangent x y := by
  have hneg : y ≠ negY shortCurve x y := by
    rw [shortCurve_negY]
    intro h
    apply hy
    linarith
  rw [slope_of_Y_ne rfl hneg]
  simp [shortCurve, shortTangent, negY]
  ring

/-- The library addition formula gives the displayed doubling
horizontal coordinate. -/
private theorem shortCurve_addX_tangent (x y : ℚ) :
    addX shortCurve x x (shortTangent x y) =
      shortDoubleX x y := by
  simp [shortCurve, shortDoubleX]
  ring

/-- The library addition formula gives the displayed doubling vertical
coordinate. -/
private theorem shortCurve_addY_tangent (x y : ℚ) :
    addY shortCurve x x y (shortTangent x y) =
      shortDoubleY x y := by
  unfold addY negAddY negY addX shortCurve shortDoubleY shortDoubleX
  ring

/-- The secant slope used for tripling agrees with the displayed
rational function. -/
private theorem shortCurve_slope_double {x y : ℚ}
    (hxx : shortDoubleX x y ≠ x) :
    slope shortCurve (shortDoubleX x y) x (shortDoubleY x y) y =
      shortTripleSlope x y := by
  rw [slope_of_X_ne hxx]
  rfl

/-- The library secant formula gives the displayed tripling horizontal
coordinate. -/
private theorem shortCurve_addX_double (x y : ℚ) :
    addX shortCurve (shortDoubleX x y) x (shortTripleSlope x y) =
      shortTripleX x y := by
  simp [shortCurve, shortTripleX]

/-- The library secant formula gives the displayed tripling vertical
coordinate. -/
private theorem shortCurve_addY_double (x y : ℚ) :
    addY shortCurve (shortDoubleX x y) x (shortDoubleY x y)
        (shortTripleSlope x y) =
      shortTripleY x y := by
  unfold addY negAddY negY addX shortCurve shortTripleY shortTripleX
  ring

/-- The denominator separating a point from its double is the numerator
of the forward isogeny's horizontal coordinate. -/
private theorem shortDoubleX_sub_identity {x y : ℚ} (hy : y ≠ 0)
    (h : OnShort x y) :
    4 * y ^ 2 * (shortDoubleX x y - x) =
      -x * (3 * x ^ 3 + 16 * x ^ 2 + 96 * x + 192) := by
  unfold shortDoubleX shortTangent
  unfold OnShort at h
  field_simp [hy]
  rw [h]
  ring

/-- Away from the visible three-torsion kernel, a point is distinct from
its double. -/
private theorem shortDoubleX_ne_self {x y : ℚ} (hx : x ≠ 0)
    (h : OnShort x y) :
    shortDoubleX x y ≠ x := by
  have hy := short_y_ne_zero h
  have hid := shortDoubleX_sub_identity hy h
  have hphi := threeIsogenyX_ne_zero hx h
  have hnum : 3 * x ^ 3 + 16 * x ^ 2 + 96 * x + 192 ≠ 0 := by
    intro hnum
    apply hphi
    unfold threeIsogenyX
    rw [show 9 * x ^ 3 + 48 * x ^ 2 + 288 * x + 576 =
      3 * (3 * x ^ 3 + 16 * x ^ 2 + 96 * x + 192) by ring]
    rw [hnum]
    simp
  intro heq
  rw [heq, sub_self, mul_zero] at hid
  exact (mul_ne_zero (neg_ne_zero.mpr hx) hnum) hid.symm

/-! ## The dual-forward composition -/

/-- The horizontal coordinate of the dual-forward composition is the
horizontal coordinate obtained from the chord-and-tangent tripling
formula. -/
private theorem dual_three_comp_x {x y : ℚ} (hx : x ≠ 0)
    (h : OnShort x y) :
    dualThreeIsogenyX (threeIsogenyX x) = shortTripleX x y := by
  have hy := short_y_ne_zero h
  have hxx := shortDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyX shortTripleX shortTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX shortDoubleY shortDoubleX shortTangent
  unfold OnShort at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [h, hy4, hy6, hy8]
  ring

/-- The vertical coordinate of the dual-forward composition is the
vertical coordinate obtained from the chord-and-tangent tripling
formula. -/
private theorem dual_three_comp_y {x y : ℚ} (hx : x ≠ 0)
    (h : OnShort x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      shortTripleY x y := by
  have hy := short_y_ne_zero h
  have hxx := shortDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyY shortTripleY shortTripleX shortTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX threeIsogenyY shortDoubleY shortDoubleX shortTangent
  unfold OnShort at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  have hy10 : y ^ 10 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 5 := by
    calc
      y ^ 10 = (y ^ 2) ^ 5 := by ring
      _ = _ := by rw [h]
  have hy12 : y ^ 12 = (x ^ 3 + (2 * x + 4) ^ 2) ^ 6 := by
    calc
      y ^ 12 = (y ^ 2) ^ 6 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [hy4, hy6, hy8, hy10, hy12]
  ring

set_option maxHeartbeats 0 in
/-- The explicit dual isogeny composed with the explicit forward isogeny
is multiplication by three on every rational point of the short model. -/
theorem dual_comp_threeIsogenyPoint (P : ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      have hcurve : OnShort x y :=
        (shortCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hzero :
            threeIsogenyPoint
              (Point.some x y h : ShortPoint) = (0 : DualPoint) := by
          simp only [threeIsogenyPoint]
          rw [dif_pos hx]
          change (0 : DualPoint) = (0 : DualPoint)
          rfl
        rw [hzero, dualThreeIsogenyPoint_zero]
        exact (three_nsmul_of_x_zero h hx).symm
      · rw [threeIsogenyPoint_some_of_x_ne_zero h hx]
        have hphi := threeIsogenyX_ne_zero hx hcurve
        change dualThreeIsogenyPoint
            (.some (threeIsogenyX x) (threeIsogenyY x y) _) = _
        rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi]
        have hy := short_y_ne_zero hcurve
        have hneg : y ≠ negY shortCurve x y := by
          rw [shortCurve_negY]
          intro heq
          apply hy
          linarith
        have hxx := shortDoubleX_ne_self hx hcurve
        rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
          two_nsmul]
        rw [Point.add_self_of_Y_ne hneg]
        rw [Point.add_of_X_ne (by
          rw [shortCurve_slope_self hy, shortCurve_addX_tangent]
          exact hxx)]
        change Point.some
            (dualThreeIsogenyX (threeIsogenyX x))
            (dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y)) _ = _
        rw [Point.some.injEq]
        constructor
        · rw [shortCurve_slope_self hy, shortCurve_addX_tangent,
            shortCurve_addY_tangent, shortCurve_slope_double hxx,
            shortCurve_addX_double]
          exact dual_three_comp_x hx hcurve
        · rw [shortCurve_slope_self hy, shortCurve_addX_tangent,
            shortCurve_addY_tangent, shortCurve_slope_double hxx,
            shortCurve_addY_double]
          exact dual_three_comp_y hx hcurve

end

end MazurProof.XDelta19Isogeny
