import FLT.Assumptions.MazurProof.N25F_YZLocalZUnit
import FLT.Assumptions.MazurProof.N25F_ZChartWChartEquiv
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation

-- Full-module imports make instance search slower than in dot's selective-import check.
set_option synthInstance.maxHeartbeats 200000

/-! The existing YZ-boundary local ring lies in the Y/Z chart overlap.
Normalize its actual Y-chart point by the proved unit Z/Y to obtain the
coordinate-rigid Z-chart algebra map, with exact coordinate formulas. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_YZOverlapMap

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open N25F_ZChartWChartEquiv N25F_YZLocalZUnit

/-- The actual X/Y coordinate, exposed here because its original name is private. -/
def yX : YChartRing := chartMap 1 (MvPolynomial.X 0)

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


private theorem yChartPoint_eq :
    chartQuotientPoint (1 : Fin 4) = (⟨yX, 1, yZ, yzW⟩ : Coordinates4 YChartRing) := by
  simp [chartQuotientPoint, mappedAmbientPoint, yX, yZ, yzW, chartMap_X_pivot]

/-- The unit realizing the actual germ of Z/Y. -/
def yzZUnit : YZLocalRingˣ := yzZGerm_isUnit.unit

@[simp]
theorem yzZUnit_val : (yzZUnit : YZLocalRing) = yzZGerm := yzZGerm_isUnit.unit_spec

/-- The actual local Y-chart point, normalized at its invertible Z coordinate. -/
def yzZPoint : Coordinates4 YZLocalRing :=
  scaleCoordinates4 (↑yzZUnit⁻¹ : YZLocalRing)
    (mapCoordinates4 (algebraMap YChartRing YZLocalRing) (chartQuotientPoint 1))

@[simp]
theorem yzZPoint_z : yzZPoint.z = 1 := by
  rw [yzZPoint, yChartPoint_eq]
  change (↑yzZUnit⁻¹ : YZLocalRing) * yzZGerm = 1
  exact Units.inv_mul_of_eq yzZUnit_val

private theorem yzZPoint_quadric : canonicalQuadric25CharTwo yzZPoint = 0 := by
  rw [yzZPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem yzZPoint_cubic : canonicalCubic25CharTwo yzZPoint = 0 := by
  rw [yzZPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

/-- The coordinate-rigid Z-chart map into the existing YZ-boundary local ring. -/
def zChartToYZLocal : ZChartRing →ₐ[ZMod 2] YZLocalRing :=
  chartPointEval 2 yzZPoint
    (by simpa [coordinates4ToFun] using yzZPoint_z)
    yzZPoint_quadric yzZPoint_cubic

@[simp]
theorem zChartToYZLocal_zX :
    zChartToYZLocal zX =
      (↑yzZUnit⁻¹ : YZLocalRing) * algebraMap YChartRing YZLocalRing yX := by
  rw [zChartToYZLocal, zX, chartPointEval_chartMap_X, yzZPoint, yChartPoint_eq]
  rfl

@[simp]
theorem zChartToYZLocal_zY :
    zChartToYZLocal zY = (↑yzZUnit⁻¹ : YZLocalRing) := by
  rw [zChartToYZLocal, zY, chartPointEval_chartMap_X, yzZPoint, yChartPoint_eq]
  change (↑yzZUnit⁻¹ : YZLocalRing) * algebraMap YChartRing YZLocalRing 1 = _
  rw [map_one, mul_one]

@[simp]
theorem zChartToYZLocal_zW :
    zChartToYZLocal zW = (↑yzZUnit⁻¹ : YZLocalRing) * yzWGerm := by
  rw [zChartToYZLocal, zW, chartPointEval_chartMap_X, yzZPoint, yChartPoint_eq]
  rfl

/-- The overlap map sends Y/Z to the inverse unit of the actual germ Z/Y. -/
theorem zChartToYZLocal_zY_isUnit : IsUnit (zChartToYZLocal zY) := by
  rw [zChartToYZLocal_zY]
  exact Units.isUnit _

end MazurProof.N25F_YZOverlapMap
