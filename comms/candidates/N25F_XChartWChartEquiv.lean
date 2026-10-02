import FLT.Assumptions.MazurProof.N25F_NonBoundaryPrincipalDivisor
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

/-!
# An actual algebra equivalence between the X and W charts

The binary linear transformation
`(X,Y,Z,W) ↦ (X+Y, X+Y+Z, Y+Z+W, X)` preserves the canonical quadric
and changes the canonical cubic by `(X+Y+Z+W)*Q`. Its inverse changes
the cubic by `(Z+W)*Q`. Evaluating these formulas on the actual chart
quotients gives mutually inverse algebra maps and transports the already
established domain structure from the W chart to the X chart.

This coordinate change is an automorphism of the canonical model. It is
not the coordinate-rigid inclusion of both charts into one function field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_XChartWChartEquiv

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryChartArtin

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

private theorem two_eq_zero (A : Type*) [CommRing A] [Algebra (ZMod 2) A] :
    (2 : A) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap (ZMod 2) A) h

/-- The explicit binary linear change taking the X chart to the W chart. -/
def linearTransform {A : Type*} [Add A] (P : Coordinates4 A) : Coordinates4 A :=
  ⟨P.x + P.y, P.x + P.y + P.z, P.y + P.z + P.w, P.x⟩

/-- The inverse binary linear coordinate change. -/
def inverseLinearTransform {A : Type*} [Add A] (P : Coordinates4 A) : Coordinates4 A :=
  ⟨P.w, P.x + P.w, P.x + P.y, P.y + P.z + P.w⟩

/-- The canonical quadric is fixed by the linear change. -/
theorem quadric_linearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalQuadric25CharTwo (linearTransform P) = canonicalQuadric25CharTwo P := by
  dsimp [canonicalQuadric25CharTwo, linearTransform]
  linear_combination
    (P.w*P.x + P.w*P.y + P.x^2 + 3*P.x*P.y + 2*P.x*P.z +
      P.y^2 + 2*P.y*P.z + P.z^2) * two_eq_zero A

/-- The cubic changes by the stated linear multiple of the quadric. -/
theorem cubic_linearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalCubic25CharTwo (linearTransform P) = canonicalCubic25CharTwo P +
      (P.x + P.y + P.z + P.w) * canonicalQuadric25CharTwo P := by
  dsimp [canonicalCubic25CharTwo, canonicalQuadric25CharTwo, linearTransform]
  linear_combination
    (-P.w^2*P.z + P.w*P.x^2 + 2*P.w*P.x*P.y - P.w*P.y*P.z -
      P.w*P.z^2 + P.x^3 + 4*P.x^2*P.y + 2*P.x^2*P.z +
      3*P.x*P.y^2 + 3*P.x*P.y*P.z + P.x*P.z^2) * two_eq_zero A

/-- The inverse coordinate change also fixes the quadric. -/
theorem quadric_inverseLinearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalQuadric25CharTwo (inverseLinearTransform P) =
      canonicalQuadric25CharTwo P := by
  dsimp [canonicalQuadric25CharTwo, inverseLinearTransform]
  linear_combination
    (P.w^2 + 2*P.w*P.x + 2*P.w*P.y + P.x^2 + P.x*P.y) * two_eq_zero A

/-- The inverse coordinate change changes the cubic by `(Z+W)*Q`. -/
theorem cubic_inverseLinearTransform {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (P : Coordinates4 A) :
    canonicalCubic25CharTwo (inverseLinearTransform P) =
      canonicalCubic25CharTwo P + (P.z + P.w) * canonicalQuadric25CharTwo P := by
  dsimp [canonicalCubic25CharTwo, canonicalQuadric25CharTwo, inverseLinearTransform]
  linear_combination
    (P.w^3 + 2*P.w^2*P.x + 3*P.w^2*P.y + P.w*P.x^2 +
      4*P.w*P.x*P.y + P.w*P.x*P.z + 2*P.w*P.y^2 + P.w*P.y*P.z -
      P.w*P.z^2 + P.x^2*P.y + P.x^2*P.z + 2*P.x*P.y^2 +
      2*P.x*P.y*P.z + P.y^3 + P.y^2*P.z) * two_eq_zero A

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

private theorem xChartPoint_eq :
    chartQuotientPoint (0 : Fin 4) = (⟨1, xY, xZ, xW⟩ : Coordinates4 XChartRing) := by
  simp [chartQuotientPoint, mappedAmbientPoint, xY, xZ, xW, chartMap_X_pivot]

private theorem wChartPoint_eq :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

/-- Pull back the W chart along the explicit canonical-model automorphism. -/
def wChartToXChart : W →ₐ[ZMod 2] XChartRing :=
  chartPointEval 3 (linearTransform (chartQuotientPoint 0))
    (by simp [linearTransform, coordinates4ToFun, xChartPoint_eq])
    (by rw [quadric_linearTransform, chartQuotientPoint_quadric])
    (by rw [cubic_linearTransform, chartQuotientPoint_cubic,
      chartQuotientPoint_quadric, mul_zero, add_zero])

/-- Pull back the X chart along the inverse canonical-model automorphism. -/
def xChartToWChart : XChartRing →ₐ[ZMod 2] W :=
  chartPointEval 0 (inverseLinearTransform (chartQuotientPoint 3))
    (by simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq])
    (by rw [quadric_inverseLinearTransform, chartQuotientPoint_quadric])
    (by rw [cubic_inverseLinearTransform, chartQuotientPoint_cubic,
      chartQuotientPoint_quadric, mul_zero, add_zero])

@[simp]
theorem wChartToXChart_qx : wChartToXChart qx = 1 + xY := by
  simp [wChartToXChart, qx, chartPointEval, affinePointEval,
    linearTransform, coordinates4ToFun, xChartPoint_eq]

@[simp]
theorem wChartToXChart_qy : wChartToXChart qy = 1 + xY + xZ := by
  simp [wChartToXChart, qy, chartPointEval, affinePointEval,
    linearTransform, coordinates4ToFun, xChartPoint_eq]

@[simp]
theorem wChartToXChart_qz : wChartToXChart qz = xY + xZ + xW := by
  simp [wChartToXChart, qz, chartPointEval, affinePointEval,
    linearTransform, coordinates4ToFun, xChartPoint_eq]

@[simp]
theorem xChartToWChart_xY : xChartToWChart xY = qx + 1 := by
  rw [xChartToWChart, xY, chartPointEval_chartMap_X]
  simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq]

@[simp]
theorem xChartToWChart_xZ : xChartToWChart xZ = qx + qy := by
  rw [xChartToWChart, xZ, chartPointEval_chartMap_X]
  simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq]

@[simp]
theorem xChartToWChart_xW : xChartToWChart xW = qy + qz + 1 := by
  rw [xChartToWChart, xW, chartPointEval_chartMap_X]
  simp [inverseLinearTransform, coordinates4ToFun, wChartPoint_eq]

private theorem chartAlgHom_ext {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (f g : ChartQuotient pivot →ₐ[ZMod 2] A)
    (h : ∀ j : OtherCoordinate pivot,
      f (chartMap pivot (MvPolynomial.X j.1)) =
        g (chartMap pivot (MvPolynomial.X j.1))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  ext j
  simpa [chartMap, ambientDehomogenize, dehomogenizedVariable, j.2] using h j

private theorem xChartToWChart_comp_wChartToXChart :
    xChartToWChart.comp wChartToXChart = AlgHom.id (ZMod 2) W := by
  apply chartAlgHom_ext 3
  rintro ⟨j, hj⟩
  fin_cases j
  · have hgen : chartMap 3 (MvPolynomial.X 0) = qx := by
      simp [chartMap, ambientDehomogenize, dehomogenizedVariable, qx]
    change xChartToWChart (wChartToXChart (chartMap 3 (MvPolynomial.X 0))) =
      chartMap 3 (MvPolynomial.X 0)
    rw [hgen]
    simp only [wChartToXChart_qx, map_add, map_one, xChartToWChart_xY]
    linear_combination two_eq_zero W
  · have hgen : chartMap 3 (MvPolynomial.X 1) = qy := by
      simp [chartMap, ambientDehomogenize, dehomogenizedVariable, qy]
    change xChartToWChart (wChartToXChart (chartMap 3 (MvPolynomial.X 1))) =
      chartMap 3 (MvPolynomial.X 1)
    rw [hgen]
    simp only [wChartToXChart_qy, map_add, map_one, xChartToWChart_xY,
      xChartToWChart_xZ]
    linear_combination (1 + qx) * two_eq_zero W
  · have hgen : chartMap 3 (MvPolynomial.X 2) = qz := by
      simp [chartMap, ambientDehomogenize, dehomogenizedVariable, qz]
    change xChartToWChart (wChartToXChart (chartMap 3 (MvPolynomial.X 2))) =
      chartMap 3 (MvPolynomial.X 2)
    rw [hgen]
    simp only [wChartToXChart_qz, map_add, map_one, xChartToWChart_xY,
      xChartToWChart_xZ, xChartToWChart_xW]
    linear_combination (1 + qx + qy) * two_eq_zero W
  · exact (hj rfl).elim

private theorem wChartToXChart_comp_xChartToWChart :
    wChartToXChart.comp xChartToWChart = AlgHom.id (ZMod 2) XChartRing := by
  apply chartAlgHom_ext 0
  rintro ⟨j, hj⟩
  fin_cases j
  · exact (hj rfl).elim
  · change wChartToXChart (xChartToWChart xY) = xY
    simp only [xChartToWChart_xY, map_add, map_one, wChartToXChart_qx]
    linear_combination two_eq_zero XChartRing
  · change wChartToXChart (xChartToWChart xZ) = xZ
    simp only [xChartToWChart_xZ, map_add, wChartToXChart_qx,
      wChartToXChart_qy]
    linear_combination (1 + xY) * two_eq_zero XChartRing
  · change wChartToXChart (xChartToWChart xW) = xW
    simp only [xChartToWChart_xW, map_add, map_one, wChartToXChart_qy,
      wChartToXChart_qz]
    linear_combination (1 + xY + xZ) * two_eq_zero XChartRing

/-- An algebra equivalence of the two actual affine curve-chart quotients. -/
def xChartAlgEquivWChart : XChartRing ≃ₐ[ZMod 2] W :=
  AlgEquiv.ofAlgHom xChartToWChart wChartToXChart
    xChartToWChart_comp_wChartToXChart wChartToXChart_comp_xChartToWChart

/-- The actual X-chart ring is a domain, transported from the established
W-chart domain through the explicit algebra equivalence. -/
instance xChartRing_isDomain : IsDomain XChartRing :=
  xChartAlgEquivWChart.toRingEquiv.toMulEquiv.isDomain W

end MazurProof.N25F_XChartWChartEquiv
