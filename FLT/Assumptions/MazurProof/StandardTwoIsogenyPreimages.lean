import FLT.Assumptions.MazurProof.VeluTwoIsogeny

/-!
# Square-coordinate preimages for the standard two-isogeny

For the standard isogeny

`E : y² = x(x² + ax + b) → E' : y² = x(x² - 2ax + a² - 4b)`,

an affine target point with nonzero square first coordinate has an explicit
rational preimage.  This is the coefficient-generic form of the preimage
calculation previously specialized to the order-15 curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.StandardTwoIsogenyPreimages

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny.StandardTwoIsogeny

noncomputable section

/-- The first coordinate of the source preimage associated with a square
target coordinate `x=r²`. -/
def preimageX (a r y : ℚ) : ℚ :=
  (r ^ 2 - a - y / r) / 2

/-- The second coordinate of the source preimage. -/
def preimageY (a r y : ℚ) : ℚ :=
  r * preimageX a r y

/-- A nonzero square first coordinate on the target of the standard
two-isogeny gives an explicit rational source preimage. -/
theorem exists_pointMap_preimage_of_x_eq_sq
    {a b x y r : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b)) x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ P : Point (curve a b),
      pointMap P = Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve :
      y ^ 2 = x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b)) :=
    curve_equation.mp h.left
  have hcurveR :
      y ^ 2 =
        r ^ 6 - 2 * a * r ^ 4 + (a ^ 2 - 4 * b) * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := preimageX a r y
  let py := preimageY a r y
  have hprod :
      px * ((r ^ 2 - a + y / r) / 2) = b := by
    dsimp [px, preimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    exact (b_ne_zero a b) hprod.symm
  have hnum : b - px ^ 2 = px * y / r := by
    rw [← hprod]
    dsimp [px, preimageX]
    field_simp [hr0]
    ring
  have hpeq : Equation (curve a b) px py := by
    rw [curve_equation]
    dsimp [px, py, preimageX, preimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 + a * r + y) * hcurveR
  have hpns : Nonsingular (curve a b) px py :=
    equation_iff_nonsingular.mp hpeq
  let P : Point (curve a b) := Point.some px py hpns
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [pointMap_some hpns hpx]
  rw [Point.some.injEq]
  constructor
  · change (r * px) ^ 2 / px ^ 2 = x
    rw [hr]
    field_simp [hpx]
  · change (r * px) * (b - px ^ 2) / px ^ 2 = y
    rw [hnum]
    field_simp [hpx, hr0]

end

end MazurProof.StandardTwoIsogenyPreimages
