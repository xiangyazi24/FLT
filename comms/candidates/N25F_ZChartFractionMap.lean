import FLT.Assumptions.MazurProof.N25F_ZChartWChartEquiv
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWChartNormalization

/-!
# The coordinate-rigid Z-chart map into the W-chart function field

The established normalization algebra over `F₂[z]` sends the polynomial
variable to the actual W-chart coordinate `qz`. Its torsion-freeness proves
`qz ≠ 0`. Scaling the universal W-chart point by this nonzero coordinate
then yields an algebra map from the actual Z-chart quotient to
`FractionRing W`, with the exact `X/Z`, `Y/Z`, and `W/Z` formulas.

This file claims neither injectivity nor extension to a boundary local ring.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_ZChartFractionMap

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoWChartNormalization
open N25F_ZChartWChartEquiv

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

private def affinePointEval {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A) : AffineChart pivot →ₐ[ZMod 2] A :=
  MvPolynomial.aeval (fun j => coordinates4ToFun P j.1)

private theorem affinePointEval_comp_dehomogenize
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A)
    (hp : coordinates4ToFun P pivot = 1) :
    (affinePointEval pivot P).toRingHom.comp (ambientDehomogenize pivot) =
      MvPolynomial.eval₂Hom (algebraMap (ZMod 2) A) (coordinates4ToFun P) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [affinePointEval, ambientDehomogenize]
  · intro j
    by_cases hj : j = pivot
    · subst j
      simp [affinePointEval, ambientDehomogenize, dehomogenizedVariable, hp]
    · simp [affinePointEval, ambientDehomogenize, dehomogenizedVariable, hj]

private theorem mappedAmbientPoint_eval
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (P : Coordinates4 A) :
    mappedAmbientPoint
        (MvPolynomial.eval₂Hom (algebraMap (ZMod 2) A) (coordinates4ToFun P)) =
      P := by
  cases P
  simp [mappedAmbientPoint, coordinates4ToFun]

private def chartPointEval {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A)
    (hp : coordinates4ToFun P pivot = 1)
    (hq : canonicalQuadric25CharTwo P = 0)
    (hc : canonicalCubic25CharTwo P = 0) : ChartQuotient pivot →ₐ[ZMod 2] A :=
  Ideal.Quotient.liftₐ (chartAffineEquationIdeal pivot) (affinePointEval pivot P)
    (by
      intro f hf
      have hker : chartAffineEquationIdeal pivot ≤
          RingHom.ker (affinePointEval pivot P).toRingHom := by
        rw [chartAffineEquationIdeal, chartAffineRelation_range]
        refine Ideal.span_le.2 ?_
        intro g hg
        rcases hg with rfl | rfl
        · change ((affinePointEval pivot P).toRingHom.comp
            (ambientDehomogenize pivot)) canonicalQuadricPolynomial25Two = 0
          rw [affinePointEval_comp_dehomogenize pivot P hp,
            map_canonicalQuadric, mappedAmbientPoint_eval]
          exact hq
        · change ((affinePointEval pivot P).toRingHom.comp
            (ambientDehomogenize pivot)) canonicalCubicPolynomial25Two = 0
          rw [affinePointEval_comp_dehomogenize pivot P hp,
            map_canonicalCubic, mappedAmbientPoint_eval]
          exact hc
      exact hker hf)

private theorem chartPointEval_chartMap_X
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A)
    (hp : coordinates4ToFun P pivot = 1)
    (hq : canonicalQuadric25CharTwo P = 0)
    (hc : canonicalCubic25CharTwo P = 0) (j : Fin 4) :
    chartPointEval pivot P hp hq hc (chartMap pivot (MvPolynomial.X j)) =
      coordinates4ToFun P j := by
  change ((affinePointEval pivot P).toRingHom.comp (ambientDehomogenize pivot))
    (MvPolynomial.X j) = _
  rw [affinePointEval_comp_dehomogenize pivot P hp]
  simp

/-- The normalization algebra sends its polynomial variable to the actual
`Z/W` coordinate of the fixed canonical chart. -/
theorem algebraMap_Rz_X :
    algebraMap (Polynomial (ZMod 2)) W Polynomial.X = qz := by
  change planeCoordinateRingToCanonicalWChart
    (AdjoinRoot.of planeSexticPolynomial Polynomial.X) = qz
  change planeCoordinateRingToCanonicalWChart planeZ = qz
  rw [planeCoordinateRingToCanonicalWChart_planeZ]
  simp [canonicalWChartZ, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize, dehomogenizedVariable, qz]

/-- The genuine nonvanishing of `Z/W` follows from the established
torsion-free normalization algebra over the polynomial ring `F₂[z]`. -/
theorem qz_ne_zero : (qz : W) ≠ 0 := by
  rw [← algebraMap_Rz_X]
  exact (map_ne_zero_iff (algebraMap (Polynomial (ZMod 2)) W)
    (FaithfulSMul.algebraMap_injective (Polynomial (ZMod 2)) W)).2 Polynomial.X_ne_zero

/-- The Z/W coordinate stays nonzero in the actual W-chart fraction field. -/
theorem fraction_qz_ne_zero : algebraMap W (FractionRing W) qz ≠ 0 :=
  (map_ne_zero_iff (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W))).2 qz_ne_zero

private theorem wChartPoint_eq :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

/-- The universal W-chart point, mapped to its fraction field and normalized
at Z. The denominator is the proved nonzero coordinate `qz`. -/
def zFractionPoint : Coordinates4 (FractionRing W) :=
  scaleCoordinates4 (algebraMap W (FractionRing W) qz)⁻¹
    (mapCoordinates4 (algebraMap W (FractionRing W)) (chartQuotientPoint 3))

@[simp]
theorem zFractionPoint_z : zFractionPoint.z = 1 := by
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ *
    algebraMap W (FractionRing W) qz = 1
  exact inv_mul_cancel₀ fraction_qz_ne_zero

private theorem zFractionPoint_quadric : canonicalQuadric25CharTwo zFractionPoint = 0 := by
  rw [zFractionPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem zFractionPoint_cubic : canonicalCubic25CharTwo zFractionPoint = 0 := by
  rw [zFractionPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

/-- The actual coordinate-rigid transition from the Z-chart ring to the
fraction field of the fixed W-chart ring. -/
def zChartToFraction : ZChartRing →ₐ[ZMod 2] FractionRing W :=
  chartPointEval 2 zFractionPoint
    (by simpa [coordinates4ToFun] using zFractionPoint_z)
    zFractionPoint_quadric zFractionPoint_cubic

@[simp]
theorem zChartToFraction_zY :
    zChartToFraction zY =
      algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qz := by
  rw [zChartToFraction, zY, chartPointEval_chartMap_X]
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ * algebraMap W (FractionRing W) qy = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem zChartToFraction_zX :
    zChartToFraction zX =
      algebraMap W (FractionRing W) qx / algebraMap W (FractionRing W) qz := by
  rw [zChartToFraction, zX, chartPointEval_chartMap_X]
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ * algebraMap W (FractionRing W) qx = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem zChartToFraction_zW :
    zChartToFraction zW = 1 / algebraMap W (FractionRing W) qz := by
  rw [zChartToFraction, zW, chartPointEval_chartMap_X]
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ * algebraMap W (FractionRing W) 1 = _
  rw [map_one, mul_one, one_div]

end MazurProof.N25F_ZChartFractionMap
