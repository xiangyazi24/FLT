import FLT.Assumptions.MazurProof.N25F_NonBoundaryPrincipalDivisor
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

/-!
# The coordinate-rigid X-chart map into the W-chart function field

Evaluation at the binary point `[1:1:0:1]` proves that the actual W-chart
coordinate `qx` is nonzero. Scaling the universal W-chart point by its X
coordinate then gives an algebra map from the actual X-chart quotient to
`FractionRing W`. This file claims neither injectivity nor an extension to
any boundary local ring.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_XChartFractionMap

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryChartArtin

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

/-- Evaluation of the actual W-chart quotient at the binary curve point
`[1:1:0:1]`, where the X-coordinate is one. -/
def binaryPointEval : W →ₐ[ZMod 2] ZMod 2 :=
  chartPointEval 3 ⟨1, 1, 0, 1⟩ rfl
    (by decide)
    (by decide)

@[simp]
theorem binaryPointEval_qx : binaryPointEval qx = 1 := by
  simp [binaryPointEval, chartPointEval, affinePointEval, qx, coordinates4ToFun]

/-- Nonvanishing of the actual X/W coordinate, witnessed by a binary point. -/
theorem qx_ne_zero : (qx : W) ≠ 0 := by
  intro h
  have heq := congrArg binaryPointEval h
  simpa using heq

/-- The X/W coordinate stays nonzero in the actual W-chart fraction field. -/
theorem fraction_qx_ne_zero : algebraMap W (FractionRing W) qx ≠ 0 :=
  (map_ne_zero_iff (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W))).2 qx_ne_zero

private theorem wChartPoint_eq :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

/-- The universal W-chart point, mapped to its fraction field and normalized
at X. The denominator is the proved nonzero coordinate `qx`. -/
def xFractionPoint : Coordinates4 (FractionRing W) :=
  scaleCoordinates4 (algebraMap W (FractionRing W) qx)⁻¹
    (mapCoordinates4 (algebraMap W (FractionRing W)) (chartQuotientPoint 3))

@[simp]
theorem xFractionPoint_x : xFractionPoint.x = 1 := by
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ *
    algebraMap W (FractionRing W) qx = 1
  exact inv_mul_cancel₀ fraction_qx_ne_zero

private theorem xFractionPoint_quadric : canonicalQuadric25CharTwo xFractionPoint = 0 := by
  rw [xFractionPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem xFractionPoint_cubic : canonicalCubic25CharTwo xFractionPoint = 0 := by
  rw [xFractionPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

/-- The actual coordinate-rigid transition from the X-chart ring to the
fraction field of the fixed W-chart ring. -/
def xChartToFraction : XChartRing →ₐ[ZMod 2] FractionRing W :=
  chartPointEval 0 xFractionPoint
    (by simpa [coordinates4ToFun] using xFractionPoint_x)
    xFractionPoint_quadric xFractionPoint_cubic

@[simp]
theorem xChartToFraction_xY :
    xChartToFraction xY =
      algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qx := by
  rw [xChartToFraction, xY, chartPointEval_chartMap_X]
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ * algebraMap W (FractionRing W) qy = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem xChartToFraction_xZ :
    xChartToFraction xZ =
      algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qx := by
  rw [xChartToFraction, xZ, chartPointEval_chartMap_X]
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ * algebraMap W (FractionRing W) qz = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem xChartToFraction_xW :
    xChartToFraction xW = 1 / algebraMap W (FractionRing W) qx := by
  rw [xChartToFraction, xW, chartPointEval_chartMap_X]
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ * algebraMap W (FractionRing W) 1 = _
  rw [map_one, mul_one, one_div]

end MazurProof.N25F_XChartFractionMap
