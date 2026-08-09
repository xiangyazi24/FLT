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

/-! ## Affine base-point exclusion -/

/-- The monic degree-ten factor in the resultant of the first and fourth
adjoint cores with respect to the source coordinate `x`. -/
def sutherlandBasePointFiber25 (y : ℚ) : ℚ :=
  y ^ 10 - 4 * y ^ 9 + 5 * y ^ 8 + 6 * y ^ 7 - 26 * y ^ 6 +
    24 * y ^ 5 + 15 * y ^ 4 - 50 * y ^ 3 + 45 * y ^ 2 - 20 * y + 5

/-- Integral polynomial underlying the base-point fibre obstruction. -/
noncomputable def sutherlandBasePointFiberPoly25 : Polynomial ℤ :=
  Polynomial.X ^ 10 - 4 * Polynomial.X ^ 9 + 5 * Polynomial.X ^ 8 +
    6 * Polynomial.X ^ 7 - 26 * Polynomial.X ^ 6 + 24 * Polynomial.X ^ 5 +
    15 * Polynomial.X ^ 4 - 50 * Polynomial.X ^ 3 + 45 * Polynomial.X ^ 2 -
    20 * Polynomial.X + 5

/-- The integral base-point fibre polynomial is monic. -/
theorem sutherlandBasePointFiberPoly25_monic :
    sutherlandBasePointFiberPoly25.Monic := by
  unfold sutherlandBasePointFiberPoly25
  monicity!

/-- The base-point fibre polynomial has no root modulo two. -/
theorem sutherlandBasePointFiberPoly25_no_root_mod2 (z : ZMod 2) :
    Polynomial.aeval z sutherlandBasePointFiberPoly25 ≠ 0 := by
  fin_cases z <;>
    simp [sutherlandBasePointFiberPoly25, Polynomial.aeval_def] <;> decide

/-- Consequently the base-point fibre polynomial has no rational root.  A
rational root of a monic integral polynomial would be integral, and reduction
of that integer modulo two contradicts the preceding exhaustive check. -/
theorem sutherlandBasePointFiber25_ne_zero (y : ℚ) :
    sutherlandBasePointFiber25 y ≠ 0 := by
  intro hy
  have hroot : Polynomial.aeval y sutherlandBasePointFiberPoly25 = 0 := by
    norm_num [sutherlandBasePointFiberPoly25, sutherlandBasePointFiber25,
      Polynomial.aeval_def]
    exact hy
  obtain ⟨z, hz, _⟩ :=
    exists_integer_of_is_root_of_monic
      sutherlandBasePointFiberPoly25_monic hroot
  have hint : Polynomial.aeval z sutherlandBasePointFiberPoly25 = 0 := by
    have h :
        Polynomial.aeval (algebraMap ℤ ℚ z)
            sutherlandBasePointFiberPoly25 = 0 := hz ▸ hroot
    rw [Polynomial.aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ)
      (h.trans (map_zero (algebraMap ℤ ℚ)).symm)
  have hmod :
      Polynomial.aeval (algebraMap ℤ (ZMod 2) z)
          sutherlandBasePointFiberPoly25 = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, hint, map_zero]
  exact sutherlandBasePointFiberPoly25_no_root_mod2 _ hmod

/-- Bezout coefficient multiplying the first adjoint core in the exact
base-point resultant identity. -/
def sutherlandBasePointBezoutX25 (x y : ℚ) : ℚ :=
  -x ^ 4 * y ^ 17 + 13 * x ^ 4 * y ^ 16 - 74 * x ^ 4 * y ^ 15 +
    236 * x ^ 4 * y ^ 14 - 427 * x ^ 4 * y ^ 13 +
    294 * x ^ 4 * y ^ 12 + 508 * x ^ 4 * y ^ 11 -
    1514 * x ^ 4 * y ^ 10 + 1413 * x ^ 4 * y ^ 9 +
    300 * x ^ 4 * y ^ 8 - 2214 * x ^ 4 * y ^ 7 +
    2699 * x ^ 4 * y ^ 6 - 1853 * x ^ 4 * y ^ 5 +
    812 * x ^ 4 * y ^ 4 - 224 * x ^ 4 * y ^ 3 + 34 * x ^ 4 * y ^ 2 -
    2 * x ^ 4 * y + x ^ 3 * y ^ 18 - 12 * x ^ 3 * y ^ 17 +
    61 * x ^ 3 * y ^ 16 - 165 * x ^ 3 * y ^ 15 +
    223 * x ^ 3 * y ^ 14 - 20 * x ^ 3 * y ^ 13 -
    388 * x ^ 3 * y ^ 12 + 365 * x ^ 3 * y ^ 11 +
    480 * x ^ 3 * y ^ 10 - 1137 * x ^ 3 * y ^ 9 +
    416 * x ^ 3 * y ^ 8 + 891 * x ^ 3 * y ^ 7 -
    1271 * x ^ 3 * y ^ 6 + 770 * x ^ 3 * y ^ 5 -
    239 * x ^ 3 * y ^ 4 + 18 * x ^ 3 * y ^ 3 + 10 * x ^ 3 * y ^ 2 -
    2 * x ^ 3 * y - x ^ 2 * y ^ 18 + 13 * x ^ 2 * y ^ 17 -
    70 * x ^ 2 * y ^ 16 + 193 * x ^ 2 * y ^ 15 -
    223 * x ^ 2 * y ^ 14 - 237 * x ^ 2 * y ^ 13 +
    1219 * x ^ 2 * y ^ 12 - 1549 * x ^ 2 * y ^ 11 -
    188 * x ^ 2 * y ^ 10 + 2833 * x ^ 2 * y ^ 9 -
    3029 * x ^ 2 * y ^ 8 + 112 * x ^ 2 * y ^ 7 +
    2756 * x ^ 2 * y ^ 6 - 3265 * x ^ 2 * y ^ 5 +
    2098 * x ^ 2 * y ^ 4 - 855 * x ^ 2 * y ^ 3 +
    222 * x ^ 2 * y ^ 2 - 33 * x ^ 2 * y + 2 * x ^ 2 -
    3 * x * y ^ 16 + 34 * x * y ^ 15 - 168 * x * y ^ 14 +
    458 * x * y ^ 13 - 660 * x * y ^ 12 + 136 * x * y ^ 11 +
    1350 * x * y ^ 10 - 2502 * x * y ^ 9 + 1479 * x * y ^ 8 +
    1182 * x * y ^ 7 - 2814 * x * y ^ 6 + 2353 * x * y ^ 5 -
    1091 * x * y ^ 4 + 264 * x * y ^ 3 - 7 * x * y ^ 2 -
    12 * x * y + 2 * x - 4 * y ^ 14 + 38 * y ^ 13 - 163 * y ^ 12 +
    397 * y ^ 11 - 548 * y ^ 10 + 283 * y ^ 9 + 316 * y ^ 8 -
    519 * y ^ 7 - 62 * y ^ 6 + 752 * y ^ 5 - 850 * y ^ 4 +
    511 * y ^ 3 - 185 * y ^ 2 + 37 * y - 3

/-- Bezout coefficient multiplying the fourth adjoint core in the exact
base-point resultant identity. -/
def sutherlandBasePointBezoutW25 (x y : ℚ) : ℚ :=
  x ^ 4 * y ^ 16 - 12 * x ^ 4 * y ^ 15 + 62 * x ^ 4 * y ^ 14 -
    174 * x ^ 4 * y ^ 13 + 253 * x ^ 4 * y ^ 12 -
    41 * x ^ 4 * y ^ 11 - 549 * x ^ 4 * y ^ 10 +
    965 * x ^ 4 * y ^ 9 - 448 * x ^ 4 * y ^ 8 -
    748 * x ^ 4 * y ^ 7 + 1466 * x ^ 4 * y ^ 6 -
    1233 * x ^ 4 * y ^ 5 + 620 * x ^ 4 * y ^ 4 -
    192 * x ^ 4 * y ^ 3 + 32 * x ^ 4 * y ^ 2 - 2 * x ^ 4 * y -
    x ^ 3 * y ^ 17 + 11 * x ^ 3 * y ^ 16 - 50 * x ^ 3 * y ^ 15 +
    114 * x ^ 3 * y ^ 14 - 98 * x ^ 3 * y ^ 13 -
    129 * x ^ 3 * y ^ 12 + 382 * x ^ 3 * y ^ 11 -
    113 * x ^ 3 * y ^ 10 - 682 * x ^ 3 * y ^ 9 +
    915 * x ^ 3 * y ^ 8 - 6 * x ^ 3 * y ^ 7 - 954 * x ^ 3 * y ^ 6 +
    1008 * x ^ 3 * y ^ 5 - 537 * x ^ 3 * y ^ 4 +
    160 * x ^ 3 * y ^ 3 - 20 * x ^ 3 * y ^ 2 + x ^ 2 * y ^ 17 -
    12 * x ^ 2 * y ^ 16 + 61 * x ^ 2 * y ^ 15 -
    168 * x ^ 2 * y ^ 14 + 242 * x ^ 2 * y ^ 13 -
    56 * x ^ 2 * y ^ 12 - 448 * x ^ 2 * y ^ 11 +
    789 * x ^ 2 * y ^ 10 - 398 * x ^ 2 * y ^ 9 -
    408 * x ^ 2 * y ^ 8 + 821 * x ^ 2 * y ^ 7 -
    745 * x ^ 2 * y ^ 6 + 527 * x ^ 2 * y ^ 5 -
    304 * x ^ 2 * y ^ 4 + 132 * x ^ 2 * y ^ 3 -
    39 * x ^ 2 * y ^ 2 + 5 * x ^ 2 * y - x * y ^ 16 +
    14 * x * y ^ 15 - 84 * x * y ^ 14 + 287 * x * y ^ 13 -
    595 * x * y ^ 12 + 662 * x * y ^ 11 + 25 * x * y ^ 10 -
    1332 * x * y ^ 9 + 2018 * x * y ^ 8 - 990 * x * y ^ 7 -
    1046 * x * y ^ 6 + 2267 * x * y ^ 5 - 1970 * x * y ^ 4 +
    1021 * x * y ^ 3 - 330 * x * y ^ 2 + 59 * x * y - 4 * x +
    y ^ 15 - 13 * y ^ 14 + 73 * y ^ 13 - 232 * y ^ 12 +
    436 * y ^ 11 - 405 * y ^ 10 - 113 * y ^ 9 + 716 * y ^ 8 -
    450 * y ^ 7 - 811 * y ^ 6 + 1858 * y ^ 5 - 1790 * y ^ 4 +
    1036 * y ^ 3 - 380 * y ^ 2 + 82 * y - 8

set_option maxHeartbeats 2000000 in
/-- Exact Bezout identity for the first and fourth adjoint cores.  It is the
kernel-checked resultant certificate used to exclude affine base points. -/
theorem sutherlandBasePoint_bezout_identity25 (x y : ℚ) :
    sutherlandBasePointBezoutX25 x y * sutherlandCanonicalXCore25 x y +
        sutherlandBasePointBezoutW25 x y * sutherlandCanonicalWCore25 x y =
      (y - 1) ^ 7 * sutherlandBasePointFiber25 y := by
  simp only [sutherlandBasePointBezoutX25, sutherlandCanonicalXCore25,
    sutherlandBasePointBezoutW25, sutherlandCanonicalWCore25,
    sutherlandBasePointFiber25]
  ring

/-- On the affine chart `y≠1`, the first and fourth canonical coordinates
cannot vanish simultaneously.  The first coordinate exposes its adjoint core;
the fourth either exposes its core or forces `x=y-1`, and both branches are
excluded by exact polynomial identities. -/
theorem sutherlandCanonicalXW_not_both_zero
    {x y : ℚ} (hy1 : y ≠ 1) :
    sutherlandCanonicalX25 x y ≠ 0 ∨ sutherlandCanonicalW25 x y ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hX, hW⟩
  have hySub : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
  have hXcore : sutherlandCanonicalXCore25 x y = 0 := by
    have hmul : (y - 1) ^ 2 * sutherlandCanonicalXCore25 x y = 0 := by
      rw [sutherlandCanonicalX25] at hX
      simpa only [neg_mul, neg_eq_zero] using hX
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hySub)
  have hWcases : x - y + 1 = 0 ∨ sutherlandCanonicalWCore25 x y = 0 := by
    have hWmul : (x - y + 1) * sutherlandCanonicalWCore25 x y = 0 := by
      simpa [sutherlandCanonicalW25] using hW
    exact mul_eq_zero.mp hWmul
  rcases hWcases with hlinear | hWcore
  · have hx : x = y - 1 := by linarith
    have hspecial :
        sutherlandCanonicalXCore25 (y - 1) y = (y - 1) ^ 5 := by
      simp only [sutherlandCanonicalXCore25]
      ring
    rw [hx] at hXcore
    rw [hspecial] at hXcore
    exact hySub ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hXcore)
  · have hbezout := sutherlandBasePoint_bezout_identity25 x y
    rw [hXcore, hWcore, mul_zero, mul_zero, zero_add] at hbezout
    have hfiber : sutherlandBasePointFiber25 y = 0 :=
      (mul_eq_zero.mp hbezout.symm).resolve_left (pow_ne_zero 7 hySub)
    exact sutherlandBasePointFiber25_ne_zero y hfiber

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

/-- The direct canonical coordinate vector is nonzero on every primitive Tate
solution.  The optimized `y` coordinate is not one, so the first/fourth
adjoint resultant guarantees that at least one of those coordinates survives. -/
theorem tateCanonicalCoordinates25_nonzero
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    NonzeroQuadruple
      (tateCanonicalCoordinates25 b c).x
      (tateCanonicalCoordinates25 b c).y
      (tateCanonicalCoordinates25 b c).z
      (tateCanonicalCoordinates25 b c).w := by
  have hy1 := tateSutherlandYCoordinate25_ne_one hb h5 hF
  have hxw := sutherlandCanonicalXW_not_both_zero
    (x := tateSutherlandXCoordinate25 b c) hy1
  rcases hxw with hx | hw
  · exact Or.inl (by simpa [tateCanonicalCoordinates25,
      sutherlandCanonicalCoordinates25] using hx)
  · exact Or.inr <| Or.inr <| Or.inr <| by
      simpa [tateCanonicalCoordinates25,
        sutherlandCanonicalCoordinates25] using hw

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
