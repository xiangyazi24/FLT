import Mathlib
import FLT.EllipticCurve.Torsion

/-!
# Discharge layer for the `ZMod 2 × ZMod 16` bridge

The repo's `E_N16` curve is not the cyclic modular curve `X_1(16)`.
The forward bridge is therefore discharged ex falso: an injection
`ZMod 2 × ZMod 16 → E(ℚ)` already gives a rational point of exact order `16`,
and the cyclic `X_1(16)` obstruction rules that out.
-/

open scoped WeierstrassCurve.Affine

namespace Scratch.DischargeN16

noncomputable section

/-- Bruin--Najman/Rabarison affine model for `X_1(16)`. -/
def X1_16Equation (u v : ℚ) : Prop :=
  v ^ 2 - (u ^ 3 + u ^ 2 - u + 1) * v + u ^ 2 = 0

/-- Affine cusps on the `X_1(16)` model used by the Tate-normal-form map. -/
def X1_16AffineCusp (u v : ℚ) : Prop :=
  (u = 0 ∧ (v = 0 ∨ v = 1)) ∨
    (u = -1 ∧ v = 1) ∨
      (u = 1 ∧ v = 1)

/--
The pure group-theory extraction from an injective `ZMod 2 × ZMod 16`.
-/
theorem order16_of_injective_Z2xZ16
    {G : Type*} [AddMonoid G]
    (f : (ZMod 2 × ZMod 16) →+ G) (hf : Function.Injective f) :
    addOrderOf (f ((0 : ZMod 2), (1 : ZMod 16))) = 16 := by
  classical
  let p0 : ZMod 2 × ZMod 16 := ((0 : ZMod 2), (1 : ZMod 16))
  have hp0_order : addOrderOf p0 = 16 := by
    simp [p0, Prod.addOrderOf_mk]
  simpa [p0] using addOrderOf_injective f hf p0 |>.trans hp0_order

/--
Exact order `16` gives a non-cuspidal rational point on the cyclic modular
curve `X_1(16)`.

This is the Tate-normal-form/Kubert bridge: normalize the point to `(0,0)`,
impose the order-16 Tate condition, and identify the resulting parameters with
the affine `X_1(16)` model.
-/
theorem order16_gives_X1_16_noncusp
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hP : addOrderOf P = 16) :
    ∃ u v : ℚ,
      X1_16Equation u v ∧
        ¬ X1_16AffineCusp u v := by
  sorry

/--
All affine rational points on this `X_1(16)` model are cuspidal.
-/
theorem X1_16_rational_points_affine_cuspidal
    {u v : ℚ}
    (h : X1_16Equation u v) :
    X1_16AffineCusp u v := by
  -- genus-2 X1(16) rank-0 rational-points seam — deep, needs hyperelliptic
  -- Jacobian/Chabauty infra absent from Mathlib.
  sorry

theorem no_order16_point_over_Q
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hP : addOrderOf P = 16) :
    False := by
  rcases order16_gives_X1_16_noncusp E P hP with
    ⟨u, v, hX, hnoncusp⟩
  exact hnoncusp (X1_16_rational_points_affine_cuspidal hX)

/--
Existing bridge target, discharged ex falso.  No point on the repo curve is
constructed; the `ZMod 2 × ZMod 16` hypothesis is contradictory.
-/
theorem Z2xZ16_gives_non_degenerate_N16_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      w ^ 2 = u ^ 3 - u ^ 2 - u ∧
        ¬ (u = -1 ∨ u = 0 ∨ u = 1) := by
  rcases hE with ⟨f, hf⟩
  have hP : addOrderOf (f ((0 : ZMod 2), (1 : ZMod 16))) = 16 :=
    order16_of_injective_Z2xZ16 f hf
  exact False.elim
    (no_order16_point_over_Q E (f ((0 : ZMod 2), (1 : ZMod 16))) hP)

end

end Scratch.DischargeN16
