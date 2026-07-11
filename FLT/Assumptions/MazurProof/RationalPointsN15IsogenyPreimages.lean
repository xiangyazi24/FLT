import FLT.Assumptions.MazurProof.RationalPointsN15Isogeny

/-!
# Explicit preimages for the order-15 two-isogeny

These formulae prove the kernel direction of the two classical descent maps.
An affine non-kernel point whose first coordinate is a rational square lies
in the image of the corresponding degree-two map.  The exceptional points
are handled by the total maps in `RationalPointsN15Isogeny`.
-/

namespace MazurProof.RationalPointsN15IsogenyPreimages

open RationalPointsN15Descent
open RationalPointsN15Isogeny
open WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

def dualPreimageX (r y : ℚ) : ℚ := 17 + 2 * r ^ 2 - 2 * y / r

def dualPreimageY (r y : ℚ) : ℚ :=
  2 * r * dualPreimageX r y

def forwardPreimageX (r y : ℚ) : ℚ :=
  (r ^ 2 - 17 - y / r) / 2

def forwardPreimageY (r y : ℚ) : ℚ :=
  r * forwardPreimageX r y

/-- A square first coordinate on the original curve gives an explicit
preimage under the dual isogeny. -/
theorem exists_dualPoint_preimage_of_x_eq_sq {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular fullTwoCurve x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ Q : IsogenousPoint,
      dualPoint Q = WeierstrassCurve.Affine.Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve : y ^ 2 = x ^ 3 + 17 * x ^ 2 + 16 * x :=
    (fullTwoEquation_cubic x y).mp ((fullTwoCurve_equation_iff x y).mp h.1)
  have hcurveR : y ^ 2 = r ^ 6 + 17 * r ^ 4 + 16 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let qx := dualPreimageX r y
  let qy := dualPreimageY r y
  have hprod :
      qx * (17 + 2 * r ^ 2 + 2 * y / r) = 225 := by
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    linear_combination -4 * hcurveR
  have hqx : qx ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hprod
    norm_num at hprod
  have hnum : 225 - qx ^ 2 = 4 * qx * y / r := by
    rw [← hprod]
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    ring
  have hqeq : IsogenousEquation qx qy := by
    unfold IsogenousEquation
    dsimp [qx, qy, dualPreimageX, dualPreimageY]
    field_simp [hr0]
    linear_combination
      4 * (-2 * r ^ 3 - 17 * r + 2 * y) * hcurveR
  have hqns : WeierstrassCurve.Affine.Nonsingular isogenousCurve qx qy :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((isogenousCurve_equation_iff qx qy).mpr hqeq)
  let Q : IsogenousPoint :=
    WeierstrassCurve.Affine.Point.some qx qy hqns
  refine ⟨Q, ?_⟩
  dsimp [Q]
  rw [dualPoint_some_of_x_ne_zero hqns hqx]
  change WeierstrassCurve.Affine.Point.some (dualX qx qy) (dualY qx qy) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (2 * r * qx) ^ 2 / qx ^ 2 / 4 = x
    rw [hr]
    field_simp [hqx]
    ring
  · change (2 * r * qx) * (225 - qx ^ 2) / qx ^ 2 / 8 = y
    rw [hnum]
    field_simp [hqx, hr0]
    ring

/-- A square first coordinate on the isogenous curve gives an explicit
preimage under the forward isogeny. -/
theorem exists_forwardPoint_preimage_of_x_eq_sq {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular isogenousCurve x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ P : FullTwoPoint,
      forwardPoint P = WeierstrassCurve.Affine.Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve : y ^ 2 = x ^ 3 - 34 * x ^ 2 + 225 * x :=
    (isogenousEquation_cubic x y).mp
      ((isogenousCurve_equation_iff x y).mp h.1)
  have hcurveR : y ^ 2 = r ^ 6 - 34 * r ^ 4 + 225 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := forwardPreimageX r y
  let py := forwardPreimageY r y
  have hprod :
      px * ((r ^ 2 - 17 + y / r) / 2) = 16 := by
    dsimp [px, forwardPreimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    norm_num at hprod
  have hnum : 16 - px ^ 2 = px * y / r := by
    rw [← hprod]
    dsimp [px, forwardPreimageX]
    field_simp [hr0]
    ring
  have hpeq : FullTwoEquation px py := by
    unfold FullTwoEquation
    dsimp [px, py, forwardPreimageX, forwardPreimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 + 17 * r + y) * hcurveR
  have hpns : WeierstrassCurve.Affine.Nonsingular fullTwoCurve px py :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((fullTwoCurve_equation_iff px py).mpr hpeq)
  let P : FullTwoPoint := WeierstrassCurve.Affine.Point.some px py hpns
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [forwardPoint_some_of_x_ne_zero hpns hpx]
  change WeierstrassCurve.Affine.Point.some (forwardX px py) (forwardY px py) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (r * px) ^ 2 / px ^ 2 = x
    rw [hr]
    field_simp [hpx]
  · change (r * px) * (16 - px ^ 2) / px ^ 2 = y
    rw [hnum]
    field_simp [hpx, hr0]

end MazurProof.RationalPointsN15IsogenyPreimages
