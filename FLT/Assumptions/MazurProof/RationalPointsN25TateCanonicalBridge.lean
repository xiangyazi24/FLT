import FLT.Assumptions.MazurProof.RationalPointsN25QuotientAction
import FLT.Assumptions.MazurProof.TateOrder25Factor

/-!
# Algebraic bridge from the order-25 Tate locus to the canonical model

The primitive Tate obstruction is an affine plane curve in parameters `b,c`,
whereas the available geometric model is a quadric-cubic complete intersection
in projective three-space.  This file begins the explicit bridge between those
models.

The main construction below clears the denominator in the existing plane
sextic lift.  For any plane triple `(x,z,w)`, write `D` for the coefficient of
`y` in the canonical cubic and `N` for its constant term.  The homogeneous
quadruple `(xD,-N,zD,wD)` then lies on the cubic identically, while its quadric
value is exactly the plane sextic.  Thus any future polynomial map from the
Tate parameters to the plane sextic will lift without division.

This file does not assert the missing source-to-plane map or the rational-point
classification.  Those require explicit numerators on `F25 = 0` together with
nonvanishing certificates excluding the five cusps.
-/

namespace MazurProof.RationalPointsN25TateCanonicalBridge

open RationalPointsN25CanonicalPoints
open RationalPointsN25QuotientAction

noncomputable section

/-! ## Elementary source-locus denominator -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- A primitive order-25 Tate point cannot lie on `c = 0`: after that
specialization, the stored primitive division polynomial is exactly `b^25`. -/
theorem c_ne_zero_of_primitive25
    {b c : ℚ} (hb : b ≠ 0)
    (h25 : TateOrder25Factor.F25 b c = 0) :
    c ≠ 0 := by
  intro hc
  subst c
  have hb25 : b ^ 25 = 0 := by
    simpa [TateOrder25Factor.F25] using h25
  exact (pow_ne_zero 25 hb) hb25

/-! ## Denominator-free lift of the eliminated plane model -/

/-- Polynomial homogeneous lift of a plane triple to the canonical ambient
four-space.  The factors `D` and `N` are the denominator and numerator of the
existing rational recovery formula `y = -N / D`. -/
def homogeneousPlaneLift25 (x z w : ℚ) : Coordinates25 :=
  let D := projectionDenominator25 x z w
  let N := projectionNumerator25 x z w
  ⟨x * D, -N, z * D, w * D⟩

/-- The canonical cubic vanishes identically on the denominator-free plane
lift, without assuming that the projection denominator is nonzero. -/
theorem homogeneousPlaneLift25_cubic (x z w : ℚ) :
    canonicalCubic25
        (homogeneousPlaneLift25 x z w).x
        (homogeneousPlaneLift25 x z w).y
        (homogeneousPlaneLift25 x z w).z
        (homogeneousPlaneLift25 x z w).w = 0 := by
  simp [homogeneousPlaneLift25, canonicalCubic25,
    projectionDenominator25, projectionNumerator25]
  ring

/-- The quadric pullback along the denominator-free plane lift is exactly the
stored plane sextic.  Consequently a plane-sextic point lifts to the full
canonical complete intersection without any field division. -/
theorem homogeneousPlaneLift25_quadric (x z w : ℚ) :
    canonicalQuadric25
        (homogeneousPlaneLift25 x z w).x
        (homogeneousPlaneLift25 x z w).y
        (homogeneousPlaneLift25 x z w).z
        (homogeneousPlaneLift25 x z w).w =
      canonicalPlaneSextic25 x z w := by
  simp [homogeneousPlaneLift25, canonicalQuadric25,
    canonicalPlaneSextic25, projectionDenominator25,
    projectionNumerator25]
  ring

/-- A zero of the plane sextic maps to a point of the canonical quadric-cubic
intersection.  This conclusion is affine-coordinate equality; proving that
the resulting homogeneous quadruple is nonzero remains a separate source-side
nonvanishing obligation. -/
theorem homogeneousPlaneLift25_onCanonical
    {x z w : ℚ} (hS : canonicalPlaneSextic25 x z w = 0) :
    OnCanonical25 (homogeneousPlaneLift25 x z w) := by
  constructor
  · rw [homogeneousPlaneLift25_quadric, hS]
  · exact homogeneousPlaneLift25_cubic x z w

/-! ## Noncuspidality criterion for the eventual source map -/

/-- A homogeneous canonical coordinate vector whose first three coordinates
are nonzero cannot represent any of the five listed cusps: every cusp
representative has a zero among `x,y,z`.  The statement is purely projective
and does not require the canonical equations or a condition on `w`. -/
theorem not_isCusp25_of_xyz_ne_zero
    {p : Coordinates25}
    (hx : p.x ≠ 0) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    ¬ IsCusp25 p := by
  intro hp
  rw [isCusp25_iff] at hp
  rcases hp with hp | hp | hp | hp | hp
  · rcases hp with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hx (by simpa [cusp25A] using hpx)
  · rcases hp with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hx (by simpa [cusp25B] using hpx)
  · rcases hp with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hz (by simpa [cusp25C] using hpz)
  · rcases hp with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hx (by simpa [cusp25D] using hpx)
  · rcases hp with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hy (by simpa [cusp25E] using hpy)

/-- The denominator-free lift is noncuspidal as soon as `x,z` and the two
elimination factors `D,N` are nonzero.  No condition on the plane coordinate
`w` is needed because the first three lifted coordinates already exclude all
five cusp classes. -/
theorem homogeneousPlaneLift25_not_isCusp
    {x z w : ℚ}
    (hx : x ≠ 0) (hz : z ≠ 0)
    (hD : projectionDenominator25 x z w ≠ 0)
    (hN : projectionNumerator25 x z w ≠ 0) :
    ¬ IsCusp25 (homogeneousPlaneLift25 x z w) := by
  apply not_isCusp25_of_xyz_ne_zero
  · simpa [homogeneousPlaneLift25] using mul_ne_zero hx hD
  · simpa [homogeneousPlaneLift25] using neg_ne_zero.mpr hN
  · simpa [homogeneousPlaneLift25] using mul_ne_zero hz hD

end

end MazurProof.RationalPointsN25TateCanonicalBridge
