import FLT.Assumptions.MazurProof.N25F_NonBoundaryPrincipalDivisor
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

/-!
# An actual algebra equivalence between the Z and W charts

The binary linear transformation
`(X,Y,Z,W) ↦ (Y+Z+W, Y+Z, X, Z)` preserves the canonical quadric
and changes the canonical cubic by `X*Q`. Its inverse changes the cubic
by `Z*Q`. Evaluation in the actual chart quotients yields mutually inverse
algebra maps and transports the established W-chart Dedekind domain.

This equivalence is induced by an automorphism of the canonical model.
It is not the coordinate-rigid inclusion of the charts in one function field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_ZChartWChartEquiv

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

/-- The `X/Z` coordinate. The original Z-local file keeps this coordinate private. -/
def zX : ZChartRing := chartMap 2 (MvPolynomial.X 0)

/-- The `Y/Z` coordinate. The original Z-local file keeps this coordinate private. -/
def zY : ZChartRing := chartMap 2 (MvPolynomial.X 1)

private theorem two_eq_zero (A : Type*) [CommRing A] [Algebra (ZMod 2) A] :
    (2 : A) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap (ZMod 2) A) h

/-- The explicit binary linear change taking the Z chart to the W chart. -/
def linearTransform {A : Type*} [Add A] (P : Coordinates4 A) : Coordinates4 A :=
  ⟨P.y + P.z + P.w, P.y + P.z, P.x, P.z⟩

/-- The inverse binary linear coordinate change. -/
def inverseLinearTransform {A : Type*} [Add A] (P : Coordinates4 A) : Coordinates4 A :=
  ⟨P.z, P.y + P.w, P.w, P.x + P.y⟩

/-- The canonical quadric is fixed by the linear change. -/
theorem quadric_linearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalQuadric25CharTwo (linearTransform P) = canonicalQuadric25CharTwo P := by
  dsimp [canonicalQuadric25CharTwo, linearTransform]
  linear_combination
    (P.x*P.y + P.x*P.z + P.y*P.z + P.z^2) * two_eq_zero A

/-- The cubic changes by `X*Q`. -/
theorem cubic_linearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalCubic25CharTwo (linearTransform P) = canonicalCubic25CharTwo P +
      P.x * canonicalQuadric25CharTwo P := by
  dsimp [canonicalCubic25CharTwo, canonicalQuadric25CharTwo, linearTransform]
  linear_combination
    (-P.w*P.x^2 + P.w*P.y*P.z + P.w*P.z^2 + P.x*P.y*P.z +
      2*P.x*P.z^2 + P.y^2*P.z + 2*P.y*P.z^2 + P.z^3) * two_eq_zero A

/-- The inverse coordinate change also fixes the quadric. -/
theorem quadric_inverseLinearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalQuadric25CharTwo (inverseLinearTransform P) =
      canonicalQuadric25CharTwo P := by
  dsimp [canonicalQuadric25CharTwo, inverseLinearTransform]
  linear_combination (P.w^2 + 2*P.w*P.y) * two_eq_zero A

/-- The inverse coordinate change changes the cubic by `Z*Q`. -/
theorem cubic_inverseLinearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalCubic25CharTwo (inverseLinearTransform P) =
      canonicalCubic25CharTwo P + P.z * canonicalQuadric25CharTwo P := by
  dsimp [canonicalCubic25CharTwo, canonicalQuadric25CharTwo, inverseLinearTransform]
  linear_combination
    (P.w^2*P.x + P.w^2*P.y + P.w*P.x*P.y + P.w*P.y^2 +
      P.w*P.y*P.z - P.w*P.z^2) * two_eq_zero A

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

private theorem zChartPoint_eq :
    chartQuotientPoint (2 : Fin 4) = (⟨zX, zY, 1, zW⟩ : Coordinates4 ZChartRing) := by
  simp [chartQuotientPoint, mappedAmbientPoint, zX, zY, zW, chartMap_X_pivot]

private theorem wChartPoint_eq :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

/-- Pull back the W chart along the explicit canonical-model automorphism. -/
def wChartToZChart : W →ₐ[ZMod 2] ZChartRing :=
  chartPointEval 3 (linearTransform (chartQuotientPoint 2))
    (by simp [linearTransform, coordinates4ToFun, zChartPoint_eq])
    (by rw [quadric_linearTransform, chartQuotientPoint_quadric])
    (by rw [cubic_linearTransform, chartQuotientPoint_cubic,
      chartQuotientPoint_quadric, mul_zero, add_zero])

/-- Pull back the Z chart along the inverse canonical-model automorphism. -/
def zChartToWChart : ZChartRing →ₐ[ZMod 2] W :=
  chartPointEval 2 (inverseLinearTransform (chartQuotientPoint 3))
    (by simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq])
    (by rw [quadric_inverseLinearTransform, chartQuotientPoint_quadric])
    (by rw [cubic_inverseLinearTransform, chartQuotientPoint_cubic,
      chartQuotientPoint_quadric, mul_zero, add_zero])

@[simp]
theorem wChartToZChart_qx : wChartToZChart qx = zY + 1 + zW := by
  simp [wChartToZChart, qx, chartPointEval, affinePointEval,
    linearTransform, coordinates4ToFun, zChartPoint_eq]

@[simp]
theorem wChartToZChart_qy : wChartToZChart qy = zY + 1 := by
  simp [wChartToZChart, qy, chartPointEval, affinePointEval,
    linearTransform, coordinates4ToFun, zChartPoint_eq]

@[simp]
theorem wChartToZChart_qz : wChartToZChart qz = zX := by
  simp [wChartToZChart, qz, chartPointEval, affinePointEval,
    linearTransform, coordinates4ToFun, zChartPoint_eq]

@[simp]
theorem zChartToWChart_zX : zChartToWChart zX = qz := by
  rw [zChartToWChart, zX, chartPointEval_chartMap_X]
  simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq]

@[simp]
theorem zChartToWChart_zY : zChartToWChart zY = qy + 1 := by
  rw [zChartToWChart, zY, chartPointEval_chartMap_X]
  simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq]

@[simp]
theorem zChartToWChart_zW : zChartToWChart zW = qx + qy := by
  rw [zChartToWChart, zW, chartPointEval_chartMap_X]
  simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq]

private theorem chartAlgHom_ext {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (f g : ChartQuotient pivot →ₐ[ZMod 2] A)
    (h : ∀ j : OtherCoordinate pivot,
      f (chartMap pivot (MvPolynomial.X j.1)) =
        g (chartMap pivot (MvPolynomial.X j.1))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  ext j
  simpa [chartMap, ambientDehomogenize, dehomogenizedVariable, j.2] using h j

private theorem zChartToWChart_comp_wChartToZChart :
    zChartToWChart.comp wChartToZChart = AlgHom.id (ZMod 2) W := by
  apply chartAlgHom_ext 3
  rintro ⟨j, hj⟩
  fin_cases j
  · have hgen : chartMap 3 (MvPolynomial.X 0) = qx := by
      simp [chartMap, ambientDehomogenize, dehomogenizedVariable, qx]
    change zChartToWChart (wChartToZChart (chartMap 3 (MvPolynomial.X 0))) =
      chartMap 3 (MvPolynomial.X 0)
    rw [hgen]
    simp only [wChartToZChart_qx, map_add, map_one, zChartToWChart_zY,
      zChartToWChart_zW]
    linear_combination (qy + 1) * two_eq_zero W
  · have hgen : chartMap 3 (MvPolynomial.X 1) = qy := by
      simp [chartMap, ambientDehomogenize, dehomogenizedVariable, qy]
    change zChartToWChart (wChartToZChart (chartMap 3 (MvPolynomial.X 1))) =
      chartMap 3 (MvPolynomial.X 1)
    rw [hgen]
    simp only [wChartToZChart_qy, map_add, map_one, zChartToWChart_zY]
    linear_combination two_eq_zero W
  · have hgen : chartMap 3 (MvPolynomial.X 2) = qz := by
      simp [chartMap, ambientDehomogenize, dehomogenizedVariable, qz]
    change zChartToWChart (wChartToZChart (chartMap 3 (MvPolynomial.X 2))) =
      chartMap 3 (MvPolynomial.X 2)
    rw [hgen, wChartToZChart_qz, zChartToWChart_zX]
  · exact (hj rfl).elim

private theorem wChartToZChart_comp_zChartToWChart :
    wChartToZChart.comp zChartToWChart = AlgHom.id (ZMod 2) ZChartRing := by
  apply chartAlgHom_ext 2
  rintro ⟨j, hj⟩
  fin_cases j
  · change wChartToZChart (zChartToWChart zX) = zX
    rw [zChartToWChart_zX, wChartToZChart_qz]
  · change wChartToZChart (zChartToWChart zY) = zY
    simp only [zChartToWChart_zY, map_add, map_one, wChartToZChart_qy]
    linear_combination two_eq_zero ZChartRing
  · exact (hj rfl).elim
  · change wChartToZChart (zChartToWChart zW) = zW
    simp only [zChartToWChart_zW, map_add, wChartToZChart_qx,
      wChartToZChart_qy]
    linear_combination (zY + 1) * two_eq_zero ZChartRing

/-- An algebra equivalence of the two actual affine curve-chart quotients. -/
def zChartAlgEquivWChart : ZChartRing ≃ₐ[ZMod 2] W :=
  AlgEquiv.ofAlgHom zChartToWChart wChartToZChart
    zChartToWChart_comp_wChartToZChart wChartToZChart_comp_zChartToWChart

/-- The actual Z-chart ring is a domain, transported from the established
W-chart domain through the explicit algebra equivalence. -/
instance zChartRing_isDomain : IsDomain ZChartRing :=
  zChartAlgEquivWChart.toRingEquiv.toMulEquiv.isDomain W

/-- The actual Z-chart ring is Dedekind, transported from the established
W-chart Dedekind domain through the explicit algebra equivalence. -/
instance zChartRing_isDedekindDomain : IsDedekindDomain ZChartRing := by
  letI : IsNoetherianRing ZChartRing :=
    isNoetherianRing_of_ringEquiv W zChartAlgEquivWChart.symm.toRingEquiv
  letI : Ring.DimensionLEOne ZChartRing :=
    Ring.DimensionLEOne.of_ringEquiv zChartAlgEquivWChart.toRingEquiv
  letI : IsIntegrallyClosed ZChartRing :=
    IsIntegrallyClosed.of_equiv zChartAlgEquivWChart.symm.toRingEquiv
  exact { }

end MazurProof.N25F_ZChartWChartEquiv
