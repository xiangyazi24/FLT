import FLT.Assumptions.MazurProof.RationalPointsN25SutherlandBridge
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientAction

/-!
# Canonical quotient map from Sutherland's level-25 source model

This file gives an explicit polynomial map from Sutherland's optimized affine
model of `X₁(25)` to the stored genus-four canonical model of its diamond
quotient.  The map was recovered exactly from the degree-nine adjoint space of
the projective plane closure.  Pullback by the diamond involution `⟨7⟩` has a
four-dimensional invariant subspace; the residual diamond action identifies
that subspace with the order-five action already formalized on the canonical
model.

Only the resulting polynomial data enter the formal proof.  The quadric and
cubic pullbacks below are literal multiples of Sutherland's plane equation,
verified by `ring`.  Composing with the preceding Tate-to-Sutherland bridge
therefore gives a fully explicit map from every primitive order-25 Tate
solution to the canonical complete intersection.

The separate remaining source-side obligation is to prove that the resulting
homogeneous vector is nonzero and is not one of the five canonical cusps.
-/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints
open RationalPointsN25QuotientAction
open RationalPointsN25SutherlandBridge
open TateOrder25Factor

/-! ## Polynomial canonical coordinates on the optimized affine source -/

/-- The degree-seven factor in the first canonical coordinate.  The full
coordinate is `-(y-1)²` times this adjoint polynomial. -/
def sutherlandCanonicalXCore25 (x y : ℚ) : ℚ :=
  x ^ 5 * y ^ 2 - 2 * x ^ 4 * y ^ 3 + x ^ 3 * y ^ 4 - x ^ 5 * y +
    x ^ 4 * y ^ 2 + x ^ 3 * y ^ 3 - x ^ 2 * y ^ 4 + x ^ 4 * y -
    2 * x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 - x ^ 2 * y ^ 2 + x * y ^ 3 +
    2 * x ^ 2 * y - 2 * x * y ^ 2 - 2 * x ^ 2 + 3 * x * y - y ^ 2 -
    2 * x + 2 * y - 1

/-- First homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalX25 (x y : ℚ) : ℚ :=
  -(y - 1) ^ 2 * sutherlandCanonicalXCore25 x y

/-- Second homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalY25 (x y : ℚ) : ℚ :=
  -(x ^ 5 * y ^ 4 - 2 * x ^ 4 * y ^ 5 + x ^ 3 * y ^ 6 + x ^ 6 * y ^ 2 -
    8 * x ^ 5 * y ^ 3 + 13 * x ^ 4 * y ^ 4 - 6 * x ^ 3 * y ^ 5 +
    6 * x ^ 5 * y ^ 2 - 10 * x ^ 4 * y ^ 3 + 2 * x ^ 3 * y ^ 4 +
    2 * x ^ 2 * y ^ 5 - 2 * x ^ 5 * y + 4 * x ^ 4 * y ^ 2 -
    5 * x ^ 3 * y ^ 3 + 4 * x ^ 2 * y ^ 4 - x * y ^ 5 - 2 * x ^ 4 * y +
    12 * x ^ 3 * y ^ 2 - 10 * x ^ 2 * y ^ 3 - 6 * x ^ 3 * y +
    3 * x ^ 2 * y ^ 2 + 3 * x * y ^ 3 + x ^ 3 + x ^ 2 * y -
    2 * x * y ^ 2 + y ^ 3 - 3 * y ^ 2 + 3 * y - 1)

/-- Third homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalZ25 (x y : ℚ) : ℚ :=
  x ^ 5 * y ^ 4 - 2 * x ^ 4 * y ^ 5 + x ^ 3 * y ^ 6 -
    5 * x ^ 5 * y ^ 3 + 10 * x ^ 4 * y ^ 4 - 5 * x ^ 3 * y ^ 5 +
    x ^ 6 * y + 3 * x ^ 5 * y ^ 2 - 8 * x ^ 4 * y ^ 3 +
    3 * x ^ 3 * y ^ 4 + x ^ 2 * y ^ 5 - 2 * x ^ 5 * y +
    4 * x ^ 4 * y ^ 2 - 4 * x ^ 3 * y ^ 3 + 2 * x ^ 2 * y ^ 4 +
    5 * x ^ 3 * y ^ 2 - 3 * x ^ 2 * y ^ 3 - 2 * x * y ^ 4 - x ^ 4 -
    2 * x ^ 3 * y + 3 * x * y ^ 3 + x ^ 3 - x ^ 2 * y + y ^ 3 +
    x ^ 2 - x * y - 3 * y ^ 2 + 3 * y - 1

/-- The degree-eight factor in the fourth canonical coordinate.  The full
coordinate is `(x-y+1)` times this adjoint polynomial. -/
def sutherlandCanonicalWCore25 (x y : ℚ) : ℚ :=
  x ^ 5 * y ^ 3 - 2 * x ^ 4 * y ^ 4 + x ^ 3 * y ^ 5 -
    2 * x ^ 5 * y ^ 2 + 3 * x ^ 4 * y ^ 3 - x ^ 2 * y ^ 5 + x ^ 5 * y -
    3 * x ^ 3 * y ^ 3 + 2 * x ^ 2 * y ^ 4 - 2 * x ^ 3 * y ^ 2 +
    2 * x ^ 2 * y ^ 3 + 3 * x ^ 3 * y - x ^ 2 * y ^ 2 -
    2 * x * y ^ 3 - x ^ 3 - x ^ 2 * y + 2 * x * y ^ 2 + y ^ 2 -
    2 * y + 1

/-- Fourth homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalW25 (x y : ℚ) : ℚ :=
  (x - y + 1) * sutherlandCanonicalWCore25 x y

/-- The four degree-nine adjoint coordinates packaged as a point in the
ambient canonical four-space. -/
def sutherlandCanonicalCoordinates25 (x y : ℚ) : Coordinates25 :=
  ⟨sutherlandCanonicalX25 x y, sutherlandCanonicalY25 x y,
    sutherlandCanonicalZ25 x y, sutherlandCanonicalW25 x y⟩

/-! ## Exact pullback of the canonical equations -/

/-- Degree-six cofactor in the pullback of the canonical quadric. -/
def sutherlandCanonicalQuadricCofactor25 (x y : ℚ) : ℚ :=
  (x - 1) *
    (2 * x ^ 3 * y ^ 2 - 3 * x ^ 2 * y ^ 3 + x * y ^ 4 -
      3 * x ^ 3 * y + 5 * x ^ 2 * y ^ 2 - 2 * x * y ^ 3 + x ^ 3 -
      2 * x ^ 2 * y + x * y ^ 2 + x ^ 2 - 2 * x * y + y ^ 2 +
      2 * x - 2 * y + 1)

set_option maxHeartbeats 2000000 in
/-- Pulling back the target canonical quadric gives Sutherland's source
equation times the displayed degree-six cofactor. -/
theorem sutherlandCanonicalCoordinates25_quadric (x y : ℚ) :
    canonicalQuadric25
        (sutherlandCanonicalCoordinates25 x y).x
        (sutherlandCanonicalCoordinates25 x y).y
        (sutherlandCanonicalCoordinates25 x y).z
        (sutherlandCanonicalCoordinates25 x y).w =
      sutherlandCanonicalQuadricCofactor25 x y *
        sutherlandX1Plane25 x y := by
  simp only [sutherlandCanonicalCoordinates25, sutherlandCanonicalX25,
    sutherlandCanonicalXCore25, sutherlandCanonicalY25,
    sutherlandCanonicalZ25, sutherlandCanonicalW25,
    sutherlandCanonicalWCore25, sutherlandCanonicalQuadricCofactor25,
    sutherlandX1Plane25, canonicalQuadric25]
  ring

/-- Degree-fifteen cofactor in the pullback of the canonical cubic.  Keeping
this literal polynomial makes the model comparison independently checkable by
the kernel rather than relying on the external adjoint-space computation. -/
def sutherlandCanonicalCubicCofactor25 (x y : ℚ) : ℚ :=
  -x ^ 10 * y ^ 5 + 3 * x ^ 10 * y ^ 4 - 3 * x ^ 10 * y ^ 3 +
    x ^ 10 * y ^ 2 + 6 * x ^ 9 * y ^ 6 - 19 * x ^ 9 * y ^ 5 +
    22 * x ^ 9 * y ^ 4 - 14 * x ^ 9 * y ^ 3 + 7 * x ^ 9 * y ^ 2 -
    2 * x ^ 9 * y - 13 * x ^ 8 * y ^ 7 + 35 * x ^ 8 * y ^ 6 -
    20 * x ^ 8 * y ^ 5 - 12 * x ^ 8 * y ^ 4 + 15 * x ^ 8 * y ^ 3 -
    7 * x ^ 8 * y ^ 2 + x ^ 8 * y + 13 * x ^ 7 * y ^ 8 -
    18 * x ^ 7 * y ^ 7 - 53 * x ^ 7 * y ^ 6 + 123 * x ^ 7 * y ^ 5 -
    97 * x ^ 7 * y ^ 4 + 48 * x ^ 7 * y ^ 3 - 14 * x ^ 7 * y ^ 2 +
    x ^ 7 - 6 * x ^ 6 * y ^ 9 - 11 * x ^ 6 * y ^ 8 +
    103 * x ^ 6 * y ^ 7 - 172 * x ^ 6 * y ^ 6 + 152 * x ^ 6 * y ^ 5 -
    150 * x ^ 6 * y ^ 4 + 131 * x ^ 6 * y ^ 3 - 68 * x ^ 6 * y ^ 2 +
    20 * x ^ 6 * y - 2 * x ^ 6 + x ^ 5 * y ^ 10 + 13 * x ^ 5 * y ^ 9 -
    58 * x ^ 5 * y ^ 8 + 85 * x ^ 5 * y ^ 7 - 112 * x ^ 5 * y ^ 6 +
    208 * x ^ 5 * y ^ 5 - 237 * x ^ 5 * y ^ 4 + 152 * x ^ 5 * y ^ 3 -
    71 * x ^ 5 * y ^ 2 + 24 * x ^ 5 * y - 4 * x ^ 5 -
    3 * x ^ 4 * y ^ 10 + 8 * x ^ 4 * y ^ 9 - 9 * x ^ 4 * y ^ 8 +
    37 * x ^ 4 * y ^ 7 - 101 * x ^ 4 * y ^ 6 + 110 * x ^ 4 * y ^ 5 -
    78 * x ^ 4 * y ^ 4 + 77 * x ^ 4 * y ^ 3 - 61 * x ^ 4 * y ^ 2 +
    25 * x ^ 4 * y - 5 * x ^ 4 + x ^ 3 * y ^ 10 - 2 * x ^ 3 * y ^ 9 -
    6 * x ^ 3 * y ^ 7 + 34 * x ^ 3 * y ^ 6 - 47 * x ^ 3 * y ^ 5 +
    27 * x ^ 3 * y ^ 4 - 20 * x ^ 3 * y ^ 3 + 21 * x ^ 3 * y ^ 2 -
    9 * x ^ 3 * y + x ^ 3 - 2 * x ^ 2 * y ^ 9 + 10 * x ^ 2 * y ^ 8 -
    27 * x ^ 2 * y ^ 7 + 52 * x ^ 2 * y ^ 6 - 84 * x ^ 2 * y ^ 5 +
    112 * x ^ 2 * y ^ 4 - 105 * x ^ 2 * y ^ 3 + 62 * x ^ 2 * y ^ 2 -
    22 * x ^ 2 * y + 4 * x ^ 2 + 2 * x * y ^ 8 - 11 * x * y ^ 7 +
    31 * x * y ^ 6 - 59 * x * y ^ 5 + 80 * x * y ^ 4 -
    77 * x * y ^ 3 + 51 * x * y ^ 2 - 21 * x * y + 4 * x - y ^ 7 +
    6 * y ^ 6 - 16 * y ^ 5 + 25 * y ^ 4 - 25 * y ^ 3 + 16 * y ^ 2 -
    6 * y + 1

set_option maxHeartbeats 4000000 in
/-- Pulling back the target canonical cubic gives Sutherland's source
equation times the displayed degree-fifteen cofactor. -/
theorem sutherlandCanonicalCoordinates25_cubic (x y : ℚ) :
    canonicalCubic25
        (sutherlandCanonicalCoordinates25 x y).x
        (sutherlandCanonicalCoordinates25 x y).y
        (sutherlandCanonicalCoordinates25 x y).z
        (sutherlandCanonicalCoordinates25 x y).w =
      sutherlandCanonicalCubicCofactor25 x y *
        sutherlandX1Plane25 x y := by
  simp only [sutherlandCanonicalCoordinates25, sutherlandCanonicalX25,
    sutherlandCanonicalXCore25, sutherlandCanonicalY25,
    sutherlandCanonicalZ25, sutherlandCanonicalW25,
    sutherlandCanonicalWCore25, sutherlandCanonicalCubicCofactor25,
    sutherlandX1Plane25, canonicalCubic25]
  ring

/-- Every affine point of Sutherland's optimized source equation maps to the
stored canonical quadric-cubic complete intersection.  Nonzeroness of the
homogeneous coordinate vector is intentionally handled separately. -/
theorem sutherlandCanonicalCoordinates25_onCanonical
    {x y : ℚ} (hsource : sutherlandX1Plane25 x y = 0) :
    OnCanonical25 (sutherlandCanonicalCoordinates25 x y) := by
  constructor
  · rw [sutherlandCanonicalCoordinates25_quadric, hsource, mul_zero]
  · rw [sutherlandCanonicalCoordinates25_cubic, hsource, mul_zero]

/-! ## Composition with the primitive Tate locus -/

/-- The optimized Sutherland `x` coordinate attached to a Tate pair. -/
def tateSutherlandXCoordinate25 (b c : ℚ) : ℚ :=
  tateToSutherlandXNum25 b c / tateToSutherlandCommon25 b c

/-- The optimized Sutherland `y` coordinate attached to a Tate pair. -/
def tateSutherlandYCoordinate25 (b c : ℚ) : ℚ :=
  tateToSutherlandCommon25 b c * (b - c) /
    tateToSutherlandYDen25 b c

/-- The raw source equation on its diagonal consists only of the two boundary
factors `t⁴(t-1)¹⁷`.  This specialization excludes `r=s` on the primitive
raw Tate chart. -/
theorem sutherlandRawX1Plane25_diagonal (t : ℚ) :
    sutherlandRawX1Plane25 t t = t ^ 4 * (t - 1) ^ 17 := by
  simp only [sutherlandRawX1Plane25]
  ring

/-- The optimized second coordinate is nonzero on every primitive Tate
solution: its numerator factors are the two already certified source-chart
units and its denominator is the second optimization unit. -/
theorem tateSutherlandYCoordinate25_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    tateSutherlandYCoordinate25 b c ≠ 0 := by
  have hc := tateC_ne_zero_of_F25 hb hF
  have hd : b - c ≠ 0 := by
    simpa [TateNFDivision.F5] using h5
  have hK := tateToSutherlandCommon_ne_zero hF hc hd
  have hB := tateToSutherlandYDen_ne_zero hF hc hd
  exact div_ne_zero (mul_ne_zero hK hd) hB

/-- The optimized second coordinate is not one on the primitive Tate locus.
If it were one, the raw optimization formula would force either `s=1` or
`r=s`; the diagonal specialization excludes the latter as well. -/
theorem tateSutherlandYCoordinate25_ne_one
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    tateSutherlandYCoordinate25 b c ≠ 1 := by
  have hc := tateC_ne_zero_of_F25 hb hF
  have hd : b - c ≠ 0 := by
    simpa [TateNFDivision.F5] using h5
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hraw : sutherlandRawX1Plane25 r s = 0 :=
    sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hr1 : r ≠ 1 := tateR_ne_one hc hd
  have hs0 : s ≠ 0 := div_ne_zero (pow_ne_zero 2 hc) hd
  have hs1 : s ≠ 1 := sutherlandS_ne_one_on_raw hraw hr1
  have hBraw : s ^ 2 - s - r + 1 ≠ 0 :=
    sutherlandYDen_ne_zero_on_raw hraw hs0 hs1
  have hB := tateToSutherlandYDen_ne_zero hF hc hd
  have hyEq :
      (r * s - 2 * r + 1) / (s ^ 2 - s - r + 1) =
        tateSutherlandYCoordinate25 b c := by
    simpa [r, s, tateSutherlandYCoordinate25] using
      (tateToSutherlandY_eq_raw hc hd hB)
  intro hy1
  have hquot : (r * s - 2 * r + 1) / (s ^ 2 - s - r + 1) = 1 := by
    rw [hyEq, hy1]
  have hnum : r * s - 2 * r + 1 = s ^ 2 - s - r + 1 := by
    exact (div_eq_one_iff_eq hBraw).mp hquot
  have hfactor : (s - 1) * (r - s) = 0 := by
    calc
      (s - 1) * (r - s) =
          (r * s - 2 * r + 1) - (s ^ 2 - s - r + 1) := by ring
      _ = 0 := sub_eq_zero.mpr hnum
  rcases mul_eq_zero.mp hfactor with hs | hrs
  · exact hs1 (sub_eq_zero.mp hs)
  · have hrs' : r = s := sub_eq_zero.mp hrs
    rw [hrs'] at hraw
    rw [sutherlandRawX1Plane25_diagonal] at hraw
    rcases mul_eq_zero.mp hraw with hs | hs
    · exact hs0 ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hs)
    · exact hs1 (sub_eq_zero.mp
        ((pow_eq_zero_iff (by norm_num : (17 : ℕ) ≠ 0)).mp hs))

/-- The canonical quotient coordinates evaluated at the explicit optimized
Sutherland coordinates of a Tate pair `(b,c)`. -/
def tateCanonicalCoordinates25 (b c : ℚ) : Coordinates25 :=
  sutherlandCanonicalCoordinates25
    (tateSutherlandXCoordinate25 b c)
    (tateSutherlandYCoordinate25 b c)

/-- Every primitive order-25 Tate solution maps to the canonical complete
intersection.  The assumptions are precisely the nonzero Tate parameter, the
proper-order-five exclusion, and the primitive factor equation. -/
theorem tateCanonicalCoordinates25_onCanonical
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    OnCanonical25 (tateCanonicalCoordinates25 b c) := by
  apply sutherlandCanonicalCoordinates25_onCanonical
  simpa [tateSutherlandXCoordinate25, tateSutherlandYCoordinate25] using
    (tateToSutherland_on_plane hb h5 hF)

end MazurProof.RationalPointsN25CanonicalSourceBridge
