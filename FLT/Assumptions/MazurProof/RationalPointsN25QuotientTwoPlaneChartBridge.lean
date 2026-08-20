import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth

/-!
# Projection from the binary N25 canonical chart to the plane sextic

The affine canonical chart `w = 1` has the rational point `[0:0:0:1]`, so its
coordinate quotient is nontrivial and has characteristic two.  Evaluating the
irreducible plane relation at the universal chart coordinates produces zero;
the universal property of `AdjoinRoot` therefore gives the forward coordinate
ring map from the integral plane model to the canonical chart.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneChartBridge

open Polynomial
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientF2

private abbrev k := ZMod 2

/-- Evaluation at the canonical affine origin `[0:0:0:1]`. -/
def wChartOriginEvaluation : AffineChart 3 →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ ↦ 0)

theorem wChartOriginEvaluation_relation (r : Fin 2) :
    wChartOriginEvaluation (chartAffineRelation 3 r) = 0 := by
  fin_cases r
  · change wChartOriginEvaluation (chartAffineQuadric 3) = 0
    simp [wChartOriginEvaluation, chartAffineQuadric,
      ambientDehomogenize, dehomogenizedVariable,
      RationalPointsN25QuotientTwoConormal.canonicalQuadricPolynomial25Two]
  · change wChartOriginEvaluation (chartAffineCubic 3) = 0
    simp [wChartOriginEvaluation, chartAffineCubic,
      ambientDehomogenize, dehomogenizedVariable,
      RationalPointsN25QuotientTwoConormal.canonicalCubicPolynomial25Two]

theorem wChartAffineEquationIdeal_le_originKernel :
    chartAffineEquationIdeal 3 ≤ RingHom.ker wChartOriginEvaluation := by
  rw [chartAffineEquationIdeal, Ideal.span_le]
  rintro f ⟨r, rfl⟩
  exact wChartOriginEvaluation_relation r

theorem wChartAffineEquationIdeal_ne_top : chartAffineEquationIdeal 3 ≠ ⊤ := by
  intro htop
  have hker : RingHom.ker wChartOriginEvaluation = ⊤ := by
    apply top_unique
    simpa only [htop] using wChartAffineEquationIdeal_le_originKernel
  exact (RingHom.ker_ne_top wChartOriginEvaluation) hker

instance canonicalWChart_nontrivial : Nontrivial (ChartQuotient 3) :=
  Ideal.Quotient.nontrivial_iff.mpr wChartAffineEquationIdeal_ne_top

instance canonicalWChart_charP : CharP (ChartQuotient 3) 2 :=
  CharP.of_ringHom_of_ne_zero (algebraMap k (ChartQuotient 3)) 2 (by norm_num)

/-- The universal canonical point on the standard chart `w = 1`. -/
def canonicalWChartPoint : Coordinates4 (ChartQuotient 3) :=
  chartQuotientPoint 3

def canonicalWChartX : ChartQuotient 3 := canonicalWChartPoint.x
def canonicalWChartY : ChartQuotient 3 := canonicalWChartPoint.y
def canonicalWChartZ : ChartQuotient 3 := canonicalWChartPoint.z

theorem canonicalWChartPoint_w : canonicalWChartPoint.w = 1 := by
  simpa [canonicalWChartPoint, coordinates4ToFun] using
    chartQuotientPoint_pivot 3

private theorem coordinates4_ext {R : Type*} {P Q : Coordinates4 R}
    (hx : P.x = Q.x) (hy : P.y = Q.y) (hz : P.z = Q.z) (hw : P.w = Q.w) :
    P = Q := by
  cases P
  cases Q
  simp_all

theorem wChartPoint_eq_canonicalWChartPoint :
    wChartPoint canonicalWChartX canonicalWChartY canonicalWChartZ =
      canonicalWChartPoint := by
  apply coordinates4_ext <;>
    simp [wChartPoint, canonicalWChartX, canonicalWChartY,
      canonicalWChartZ, canonicalWChartPoint_w]

/-- Evaluate `F₂[z]` in the canonical `w = 1` chart at its `z` coordinate. -/
def zPolynomialToCanonicalWChart : k[X] →+* ChartQuotient 3 :=
  Polynomial.eval₂RingHom (algebraMap k (ChartQuotient 3)) canonicalWChartZ

theorem planeSexticPolynomial_eval_canonicalWChart :
    planeSexticPolynomial.eval₂ zPolynomialToCanonicalWChart canonicalWChartX = 0 := by
  change planeSexticPolynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap k (ChartQuotient 3)) canonicalWChartZ)
        canonicalWChartX = 0
  apply planeSexticPolynomial_eval_eq_zero_of_canonical
    canonicalWChartX canonicalWChartY canonicalWChartZ
  · rw [wChartPoint_eq_canonicalWChartPoint]
    exact chartQuotientPoint_quadric 3
  · rw [wChartPoint_eq_canonicalWChartPoint]
    exact chartQuotientPoint_cubic 3

/-- The plane-sextic coordinate ring maps to the canonical `w = 1` chart by
sending its two coordinates to the canonical `x` and `z` classes. -/
def planeCoordinateRingToCanonicalWChart :
    PlaneCoordinateRing →+* ChartQuotient 3 :=
  AdjoinRoot.lift zPolynomialToCanonicalWChart canonicalWChartX
    planeSexticPolynomial_eval_canonicalWChart

@[simp]
theorem planeCoordinateRingToCanonicalWChart_root :
    planeCoordinateRingToCanonicalWChart (AdjoinRoot.root planeSexticPolynomial) =
      canonicalWChartX := by
  exact AdjoinRoot.lift_root _

@[simp]
theorem planeCoordinateRingToCanonicalWChart_planeX :
    planeCoordinateRingToCanonicalWChart planeX = canonicalWChartX := by
  exact planeCoordinateRingToCanonicalWChart_root

@[simp]
theorem planeCoordinateRingToCanonicalWChart_planeZ :
    planeCoordinateRingToCanonicalWChart planeZ = canonicalWChartZ := by
  simp [planeCoordinateRingToCanonicalWChart, planeZ,
    zPolynomialToCanonicalWChart]

/-- The denominator on the canonical chart. -/
def canonicalWChartProjectionDenominator : ChartQuotient 3 :=
  projectionDenominator canonicalWChartX canonicalWChartZ

/-- The numerator on the canonical chart. -/
def canonicalWChartProjectionNumerator : ChartQuotient 3 :=
  projectionNumerator canonicalWChartX canonicalWChartZ

@[simp]
theorem planeCoordinateRingToCanonicalWChart_denominator :
    planeCoordinateRingToCanonicalWChart planeProjectionDenominator =
      canonicalWChartProjectionDenominator := by
  simp [planeProjectionDenominator, canonicalWChartProjectionDenominator,
    projectionDenominator]

@[simp]
theorem planeCoordinateRingToCanonicalWChart_numerator :
    planeCoordinateRingToCanonicalWChart planeProjectionNumerator =
      canonicalWChartProjectionNumerator := by
  simp [planeProjectionNumerator, canonicalWChartProjectionNumerator,
    projectionNumerator]

end MazurProof.RationalPointsN25QuotientTwoPlaneChartBridge
