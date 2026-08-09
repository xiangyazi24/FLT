import FLT.Assumptions.MazurProof.RationalPointsN25QuotientAction
import FLT.Assumptions.MazurProof.TateOrder25ParameterAction

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

The file also records the exact degree-six quotient map from the official
LMFDB singular plane model of `X_{\pm 1}(25)` (label `25.300.12.j.1`) to the
stored genus-four canonical model.  Its quadric and cubic pullbacks are literal
multiples of the degree-eleven source equation.  This closes the target half of
the comparison: the remaining model-identification problem is the birational
map from the Tate equation `F25(b,c)=0` to this degree-eleven plane model.

No rational-point classification is asserted here.  The eventual Tate bridge
will additionally need nonvanishing certificates excluding the five cusps.
-/

namespace MazurProof.RationalPointsN25TateCanonicalBridge

open RationalPointsN25CanonicalPoints
open RationalPointsN25QuotientAction

noncomputable section

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

/-! ## The explicit quotient of the LMFDB `X_{\pm 1}(25)` plane model

The source coordinates below are ordered as `[C:W:S]`, matching the LMFDB
projection from its genus-twelve canonical model.  Solving the canonical
quadrics on the chart `S = 1`, substituting the published linear quotient map,
and clearing its common denominator gives the four homogeneous sextics below.
The two pullback identities are independent `ring` certificates, so subsequent
formal arguments do not depend on that elimination computation.
-/

/-- The homogeneous degree-eleven singular plane model of `X_{\pm 1}(25)` used
by LMFDB label `25.300.12.j.1`, in source coordinates `[C:W:S]`. -/
def lmfdbX1Plane25 (C W S : ℚ) : ℚ :=
  -(C ^ 5 * S ^ 3 * W ^ 3) + C ^ 4 * S ^ 6 * W -
    2 * C ^ 4 * S ^ 5 * W ^ 2 + C ^ 4 * S ^ 4 * W ^ 3 -
    3 * C ^ 4 * S ^ 3 * W ^ 4 - C ^ 4 * S ^ 2 * W ^ 5 +
    C ^ 4 * S * W ^ 6 + C ^ 3 * S ^ 8 - C ^ 3 * S ^ 7 * W +
    2 * C ^ 3 * S ^ 6 * W ^ 2 - C ^ 3 * S ^ 5 * W ^ 3 -
    C ^ 3 * S ^ 4 * W ^ 4 + C ^ 3 * S ^ 3 * W ^ 5 -
    2 * C ^ 3 * S ^ 2 * W ^ 6 + 3 * C ^ 3 * S * W ^ 7 +
    C ^ 3 * W ^ 8 + 2 * C ^ 2 * S ^ 7 * W ^ 2 -
    2 * C ^ 2 * S ^ 6 * W ^ 3 + 2 * C ^ 2 * S ^ 5 * W ^ 4 -
    4 * C ^ 2 * S ^ 4 * W ^ 5 + 2 * C ^ 2 * S ^ 3 * W ^ 6 +
    2 * C ^ 2 * S * W ^ 8 + 2 * C ^ 2 * W ^ 9 +
    C * S ^ 6 * W ^ 4 - C * S ^ 5 * W ^ 5 - C * S ^ 4 * W ^ 6 -
    2 * C * S ^ 3 * W ^ 7 + C * S ^ 2 * W ^ 8 + C * W ^ 10 -
    S ^ 3 * W ^ 8

/-- First homogeneous coordinate of the degree-two quotient from the LMFDB
`X_{\pm 1}(25)` plane model to the genus-four canonical model. -/
def lmfdbQuotientX25 (C W S : ℚ) : ℚ :=
  -(C ^ 3 * S ^ 2 * W) + C ^ 3 * S * W ^ 2 - C ^ 2 * S ^ 4 +
    C ^ 2 * S ^ 3 * W - C ^ 2 * S ^ 2 * W ^ 2 +
    C ^ 2 * S * W ^ 3 + C ^ 2 * W ^ 4 - C * S ^ 3 * W ^ 2 +
    C * S ^ 2 * W ^ 3 - C * S * W ^ 4 + C * W ^ 5

/-- Second homogeneous coordinate of the degree-two quotient from the LMFDB
`X_{\pm 1}(25)` plane model to the genus-four canonical model. -/
def lmfdbQuotientY25 (C W S : ℚ) : ℚ :=
  -(C ^ 3 * S ^ 2 * W) + C ^ 2 * S ^ 3 * W - C ^ 2 * S * W ^ 3 +
    2 * C * S ^ 2 * W ^ 3 - C * S * W ^ 4 - C * W ^ 5 +
    S * W ^ 5 - W ^ 6

/-- Third homogeneous coordinate of the degree-two quotient from the LMFDB
`X_{\pm 1}(25)` plane model to the genus-four canonical model. -/
def lmfdbQuotientZ25 (C W S : ℚ) : ℚ :=
  -(C ^ 2 * S ^ 4) - C ^ 2 * S ^ 2 * W ^ 2 + C ^ 2 * S * W ^ 3 -
    C * S ^ 3 * W ^ 2 + C * S * W ^ 4 + C * W ^ 5 + W ^ 6

/-- Fourth homogeneous coordinate of the degree-two quotient from the LMFDB
`X_{\pm 1}(25)` plane model to the genus-four canonical model. -/
def lmfdbQuotientW25 (C W S : ℚ) : ℚ :=
  -(C ^ 3 * S ^ 2 * W) - C ^ 2 * S ^ 4 + C ^ 2 * S ^ 3 * W +
    C ^ 2 * W ^ 4 - 2 * C * S ^ 3 * W ^ 2 +
    2 * C * S ^ 2 * W ^ 3 + C * W ^ 5 - S ^ 2 * W ^ 4 +
    S * W ^ 5

/-- The four degree-six quotient coordinates packaged in the canonical ambient
coordinate structure. -/
def lmfdbQuotientCoordinates25 (C W S : ℚ) : Coordinates25 :=
  ⟨lmfdbQuotientX25 C W S, lmfdbQuotientY25 C W S,
    lmfdbQuotientZ25 C W S, lmfdbQuotientW25 C W S⟩

/-- Degree-six cofactor left after pulling back the canonical cubic along the
LMFDB quotient coordinates. -/
def lmfdbQuotientCubicCofactor25 (C W S : ℚ) : ℚ :=
  C ^ 4 * S ^ 2 - C ^ 4 * S * W - C ^ 3 * S ^ 3 +
    C ^ 3 * S ^ 2 * W - C ^ 3 * W ^ 3 - C ^ 2 * S ^ 3 * W -
    C ^ 2 * S ^ 2 * W ^ 2 + 3 * C ^ 2 * S * W ^ 3 -
    2 * C * S ^ 2 * W ^ 3 + C * S * W ^ 4 + 2 * C * W ^ 5 -
    S * W ^ 5 + W ^ 6

set_option maxHeartbeats 1000000 in
/-- The canonical quadric pulls back to `-C` times the degree-eleven source
equation.  This is an unconditional polynomial identity in three variables. -/
theorem lmfdbQuotientCoordinates25_quadric (C W S : ℚ) :
    canonicalQuadric25
        (lmfdbQuotientCoordinates25 C W S).x
        (lmfdbQuotientCoordinates25 C W S).y
        (lmfdbQuotientCoordinates25 C W S).z
        (lmfdbQuotientCoordinates25 C W S).w =
      -C * lmfdbX1Plane25 C W S := by
  simp only [lmfdbQuotientCoordinates25, lmfdbQuotientX25,
    lmfdbQuotientY25, lmfdbQuotientZ25, lmfdbQuotientW25,
    lmfdbX1Plane25, canonicalQuadric25]
  ring

set_option maxHeartbeats 2000000 in
/-- The canonical cubic pulls back to the source equation times the displayed
degree-seven cofactor `-W * H₆`.  This is an unconditional polynomial
identity and therefore remains valid at every exceptional chart point. -/
theorem lmfdbQuotientCoordinates25_cubic (C W S : ℚ) :
    canonicalCubic25
        (lmfdbQuotientCoordinates25 C W S).x
        (lmfdbQuotientCoordinates25 C W S).y
        (lmfdbQuotientCoordinates25 C W S).z
        (lmfdbQuotientCoordinates25 C W S).w =
      -(W * lmfdbQuotientCubicCofactor25 C W S *
        lmfdbX1Plane25 C W S) := by
  simp only [lmfdbQuotientCoordinates25, lmfdbQuotientX25,
    lmfdbQuotientY25, lmfdbQuotientZ25, lmfdbQuotientW25,
    lmfdbQuotientCubicCofactor25, lmfdbX1Plane25, canonicalCubic25]
  ring

/-- Every zero of the LMFDB `X_{\pm 1}(25)` plane equation maps to the stored
canonical quadric-cubic intersection.  Nonzeroness of the four homogeneous
coordinates is deliberately kept as a separate source-side obligation. -/
theorem lmfdbQuotientCoordinates25_onCanonical
    {C W S : ℚ} (hsource : lmfdbX1Plane25 C W S = 0) :
    OnCanonical25 (lmfdbQuotientCoordinates25 C W S) := by
  constructor
  · rw [lmfdbQuotientCoordinates25_quadric, hsource, mul_zero]
  · rw [lmfdbQuotientCoordinates25_cubic, hsource]
    ring

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
