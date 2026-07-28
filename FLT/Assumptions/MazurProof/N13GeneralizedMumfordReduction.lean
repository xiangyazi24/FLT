import FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral
import FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo
import Mathlib.Data.Set.Image
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Reduction of integral N13 Mumford graphs at two

The good integral equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

has the same coefficients after reduction from `ℤ₂` to `𝔽₂`.  Hence
coefficientwise reduction induces a canonical ring homomorphism between
the two affine coordinate rings.  This file proves that the homomorphism
preserves both coordinates and carries every generalized Mumford graph
ideal exactly to the corresponding special-fibre graph ideal.
-/

open Polynomial

namespace MazurProof.N13GeneralizedMumfordReduction

noncomputable section

abbrev R₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.R₂

abbrev K : Type :=
  N13GoodCoordinateRingTwo.K

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev SpecialRing : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- Coefficient reduction from the two-adic integers to `𝔽₂`. -/
def reduceBase : R₂ →+* K :=
  PadicInt.toZMod

/-- Coefficientwise reduction of polynomials in the `X` coordinate. -/
def reducePoly : R₂[X] →+* K[X] :=
  Polynomial.mapRingHom reduceBase

@[simp] theorem reducePoly_apply (p : R₂[X]) :
    reducePoly p = p.map reduceBase := rfl

@[simp] theorem reduce_hPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.hPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodCoordinateRingTwo.hPoly]

@[simp] theorem reduce_rhsPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.rhsPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.rhsPoly,
    N13GoodCoordinateRingTwo.rhsPoly]

theorem reduce_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly =
      N13GoodCoordinateRingTwo.curvePoly := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    N13GoodCoordinateRingTwo.curvePoly, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (reducePoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (reducePoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 + C N13GoodCoordinateRingTwo.hPoly * X -
        C N13GoodCoordinateRingTwo.rhsPoly
  rw [reduce_hPoly, reduce_rhsPoly]

private theorem special_curve_dvd :
    N13GoodCoordinateRingTwo.curvePoly ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly := by
  rw [reduce_curvePoly]

/-- Reduction on the affine coordinate ring of the good equation. -/
def reduceCoordinate : IntegralRing →+* SpecialRing :=
  AdjoinRoot.map reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_xClass (p : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GoodCoordinateRingTwo.xClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd p

@[simp] theorem reduce_yClass :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GoodCoordinateRingTwo.yClass := by
  exact AdjoinRoot.map_root
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_ySubClass (v : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GoodCoordinateRingTwo.ySubClass (reducePoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass,
    N13GoodCoordinateRingTwo.ySubClass]

/-- Reduction carries the integral graph ideal onto, rather than merely
into, the graph ideal with reduced coefficients. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reducePoly u) (reducePoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GoodCoordinateRingTwo.mumfordIdeal, Ideal.map_span,
    Set.image_pair, reduce_xClass, reduce_ySubClass]

end

end MazurProof.N13GeneralizedMumfordReduction
