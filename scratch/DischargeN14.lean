import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.TateZ2xZ10Reduction

/-!
# Discharge layer for the `ZMod 2 × ZMod 14` bridge

The repo's `E_N14` curve is not the cyclic modular curve `X_1(14)`.
The forward bridge is therefore discharged ex falso: an injection
`ZMod 2 × ZMod 14 → E(ℚ)` already gives a rational point of exact order `14`,
and the cyclic `X_1(14)` obstruction rules that out.
-/

open scoped WeierstrassCurve.Affine

namespace Scratch.DischargeN14

open Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The cyclic modular curve model `X_1(14) = 14a4`. -/
def X14Equation (t s : ℚ) : Prop :=
  s ^ 2 + t * s + s = t ^ 3 - t

def X14DegenerateParameter (t : ℚ) : Prop :=
  t = -1 ∨ t = 0 ∨ t = 1

/-- Denominator in Kubert's `X_1(14)` parametrization. -/
def D14 (t : ℚ) : ℚ :=
  (t + 1) * (t ^ 3 - 2 * t ^ 2 - t + 1)

/-- Kubert/Morain `a`-coefficient on `X_1(14)`. -/
def kubertA14 (t s : ℚ) : ℚ :=
  (t ^ 4 - s * t ^ 3 + (2 * s - 4) * t ^ 2 - s * t + 1) / D14 t

/-- Kubert/Morain `b`-coefficient on `X_1(14)`. -/
def kubertB14 (t s : ℚ) : ℚ :=
  (-t ^ 7 + 2 * t ^ 6 + (2 * s - 1) * t ^ 5 - (2 * s + 1) * t ^ 4
      - 2 * (s - 1) * t ^ 3 + (3 * s - 1) * t ^ 2 - s * t) / (D14 t) ^ 2

/-- Repo Tate convention: `Y^2 + (1-c)XY - bY = X^3 - bX^2`. -/
def tateB14 (t s : ℚ) : ℚ :=
  -kubertB14 t s

/-- Repo Tate convention: `Y^2 + (1-c)XY - bY = X^3 - bX^2`. -/
def tateC14 (t s : ℚ) : ℚ :=
  1 - kubertA14 t s

private lemma tate_origin_nonsingular14
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

private def tateOriginPoint14 (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular14 b c)

/-- Exact order `14` for the origin on repo Tate normal form. -/
def tateOrder14Condition (b c : ℚ) : Prop :=
  ∃ hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
    letI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := hEll
    addOrderOf (tateOriginPoint14 b c) = 14

/--
The pure group-theory extraction from an injective `ZMod 2 × ZMod 14`.
-/
theorem order14_of_injective_Z2xZ14
    {G : Type*} [AddMonoid G]
    (f : (ZMod 2 × ZMod 14) →+ G) (hf : Function.Injective f) :
    addOrderOf (f ((0 : ZMod 2), (1 : ZMod 14))) = 14 := by
  classical
  let p0 : ZMod 2 × ZMod 14 := ((0 : ZMod 2), (1 : ZMod 14))
  have hp0_order : addOrderOf p0 = 14 := by
    simp [p0, Prod.addOrderOf_mk]
  simpa [p0] using addOrderOf_injective f hf p0 |>.trans hp0_order

/--
The cyclic `X_1(14)` obstruction.

Mathematically this is the standard route:
an exact order-14 rational point gives a non-cuspidal rational point on
`X_1(14) : s^2 + ts + s = t^3 - t`; the curve is Cremona `14a4`, rank zero,
and all rational points are cuspidal, i.e. `t ∈ {-1,0,1}`.
-/
theorem order14_point_obstructed_by_X14_rank_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : (E⁄ℚ).Point)
    (hR : addOrderOf R = 14) :
    False := by
  -- This is the single remaining arithmetic-geometry wall: formalize the
  -- Tate/Kubert map to `X_1(14)` and the rank-zero rational-point enumeration
  -- on `14a4`.
  sorry

theorem no_order14_point_over_Q
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : (E⁄ℚ).Point)
    (hR : addOrderOf R = 14) :
    False :=
  order14_point_obstructed_by_X14_rank_zero E R hR

/--
Existing bridge target, discharged ex falso.  No point on the repo curve is
constructed; the `ZMod 2 × ZMod 14` hypothesis is contradictory.
-/
theorem Z2xZ14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      w ^ 2 = u ^ 3 + u ^ 2 - 2 * u ∧
        ¬ (u = -2 ∨ u = 0 ∨ u = 1) := by
  rcases hE with ⟨f, hf⟩
  have hR : addOrderOf (f ((0 : ZMod 2), (1 : ZMod 14))) = 14 :=
    order14_of_injective_Z2xZ14 f hf
  exact False.elim (no_order14_point_over_Q E (f ((0 : ZMod 2), (1 : ZMod 14))) hR)

end

end Scratch.DischargeN14
