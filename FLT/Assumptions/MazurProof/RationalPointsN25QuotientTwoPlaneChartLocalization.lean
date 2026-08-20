import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneChartBridge

/-!
# The common principal open of the N25 plane and canonical charts

The inverse projection from the canonical `w = 1` chart uses the denominator
`D = xz + x + z`.  This module first extends the plane-to-canonical map to
the corresponding principal opens.  It then constructs the three candidate
coordinates of the inverse map inside the localized plane ring.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneChartLocalization

open Polynomial
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoStructuralJacobian

private abbrev k := ZMod 2

/-- The principal open of the integral plane chart on which the inverse
projection is defined. -/
abbrev PlaneDOpen := Localization.Away planeProjectionDenominator

/-- The matching principal open in the canonical `w = 1` chart. -/
abbrev CanonicalWChartDOpen :=
  Localization.Away canonicalWChartProjectionDenominator

/-- The plane coordinate map followed by the canonical localization map. -/
def planeToCanonicalWChartDOpen :
    PlaneCoordinateRing →+* CanonicalWChartDOpen :=
  (algebraMap (ChartQuotient 3) CanonicalWChartDOpen).comp
    planeCoordinateRingToCanonicalWChart

theorem planeDenominator_mapsToUnit :
    IsUnit (planeToCanonicalWChartDOpen planeProjectionDenominator) := by
  rw [planeToCanonicalWChartDOpen, RingHom.comp_apply,
    planeCoordinateRingToCanonicalWChart_denominator]
  exact IsLocalization.Away.algebraMap_isUnit
    canonicalWChartProjectionDenominator

/-- The forward coordinate-ring map on the common principal open. -/
def planeDOpenToCanonicalWChartDOpen :
    PlaneDOpen →+* CanonicalWChartDOpen :=
  IsLocalization.Away.lift
    planeProjectionDenominator planeDenominator_mapsToUnit

@[simp]
theorem planeDOpenToCanonicalWChartDOpen_algebraMap
    (p : PlaneCoordinateRing) :
    planeDOpenToCanonicalWChartDOpen (algebraMap PlaneCoordinateRing PlaneDOpen p) =
      algebraMap (ChartQuotient 3) CanonicalWChartDOpen
        (planeCoordinateRingToCanonicalWChart p) := by
  exact IsLocalization.Away.lift_eq
    planeProjectionDenominator planeDenominator_mapsToUnit p

/-- The localized plane `x` coordinate. -/
def planeDOpenX : PlaneDOpen :=
  algebraMap PlaneCoordinateRing PlaneDOpen planeX

/-- The localized plane `z` coordinate. -/
def planeDOpenZ : PlaneDOpen :=
  algebraMap PlaneCoordinateRing PlaneDOpen planeZ

/-- The localized inverse-projection denominator. -/
def planeDOpenDenominator : PlaneDOpen :=
  algebraMap PlaneCoordinateRing PlaneDOpen planeProjectionDenominator

/-- The localized inverse-projection numerator. -/
def planeDOpenNumerator : PlaneDOpen :=
  algebraMap PlaneCoordinateRing PlaneDOpen planeProjectionNumerator

/-- The candidate canonical `y` coordinate `N/D` on the plane principal
open. -/
def planeDOpenY : PlaneDOpen :=
  planeDOpenNumerator *
    IsLocalization.Away.invSelf planeProjectionDenominator

@[simp]
theorem planeDOpenDenominator_mul_invSelf :
    planeDOpenDenominator *
        IsLocalization.Away.invSelf planeProjectionDenominator = 1 := by
  exact IsLocalization.Away.mul_invSelf planeProjectionDenominator

@[simp]
theorem planeDOpenDenominator_eq_projection :
    planeDOpenDenominator =
      projectionDenominator planeDOpenX planeDOpenZ := by
  simp [planeDOpenDenominator, planeDOpenX, planeDOpenZ,
    planeProjectionDenominator, projectionDenominator]

@[simp]
theorem planeDOpenNumerator_eq_projection :
    planeDOpenNumerator =
      projectionNumerator planeDOpenX planeDOpenZ := by
  simp [planeDOpenNumerator, planeDOpenX, planeDOpenZ,
    planeProjectionNumerator, projectionNumerator]

theorem planeDOpen_two_eq_zero : (2 : PlaneDOpen) = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h := congrArg
    ((algebraMap PlaneCoordinateRing PlaneDOpen).comp
      (algebraMap k PlaneCoordinateRing)) htwo
  simpa only [RingHom.comp_apply, map_ofNat, map_zero] using h

/-- The defining denominator relation for the inverse coordinate `y=N/D`. -/
theorem planeDOpenDenominator_mul_y :
    planeDOpenDenominator * planeDOpenY = planeDOpenNumerator := by
  rw [planeDOpenY]
  calc
    planeDOpenDenominator *
          (planeDOpenNumerator *
            IsLocalization.Away.invSelf planeProjectionDenominator) =
        planeDOpenNumerator *
          (planeDOpenDenominator *
            IsLocalization.Away.invSelf planeProjectionDenominator) := by
      ring
    _ = planeDOpenNumerator := by
      rw [planeDOpenDenominator_mul_invSelf, mul_one]

@[simp]
theorem planeDOpenToCanonicalWChartDOpen_x :
    planeDOpenToCanonicalWChartDOpen planeDOpenX =
      algebraMap (ChartQuotient 3) CanonicalWChartDOpen canonicalWChartX := by
  simp [planeDOpenX]

@[simp]
theorem planeDOpenToCanonicalWChartDOpen_z :
    planeDOpenToCanonicalWChartDOpen planeDOpenZ =
      algebraMap (ChartQuotient 3) CanonicalWChartDOpen canonicalWChartZ := by
  simp [planeDOpenZ]

@[simp]
theorem planeDOpenToCanonicalWChartDOpen_denominator :
    planeDOpenToCanonicalWChartDOpen planeDOpenDenominator =
      algebraMap (ChartQuotient 3) CanonicalWChartDOpen
        canonicalWChartProjectionDenominator := by
  simp [planeDOpenDenominator]

@[simp]
theorem planeDOpenToCanonicalWChartDOpen_numerator :
    planeDOpenToCanonicalWChartDOpen planeDOpenNumerator =
      algebraMap (ChartQuotient 3) CanonicalWChartDOpen
        canonicalWChartProjectionNumerator := by
  simp [planeDOpenNumerator]

/-- The canonical cubic is the denominator relation already in the affine
chart ring. -/
theorem canonicalWChartDenominator_mul_y :
    canonicalWChartProjectionDenominator * canonicalWChartY =
      canonicalWChartProjectionNumerator := by
  have hc := chartQuotientPoint_cubic 3
  change canonicalCubic25CharTwo canonicalWChartPoint = 0 at hc
  rw [← wChartPoint_eq_canonicalWChartPoint, canonicalCubic_wChart] at hc
  have htwo : (2 : ChartQuotient 3) = 0 :=
    CharP.cast_eq_zero (ChartQuotient 3) 2
  change projectionDenominator canonicalWChartX canonicalWChartZ *
      canonicalWChartY =
    projectionNumerator canonicalWChartX canonicalWChartZ
  linear_combination hc -
    projectionNumerator canonicalWChartX canonicalWChartZ * htwo

/-- The forward principal-open map sends `N/D` to the canonical `y`
coordinate. -/
@[simp]
theorem planeDOpenToCanonicalWChartDOpen_y :
    planeDOpenToCanonicalWChartDOpen planeDOpenY =
      algebraMap (ChartQuotient 3) CanonicalWChartDOpen canonicalWChartY := by
  have hPlane := congrArg planeDOpenToCanonicalWChartDOpen
    planeDOpenDenominator_mul_y
  simp only [map_mul, planeDOpenToCanonicalWChartDOpen_denominator,
    planeDOpenToCanonicalWChartDOpen_numerator] at hPlane
  have hCanonical := congrArg
    (algebraMap (ChartQuotient 3) CanonicalWChartDOpen)
    canonicalWChartDenominator_mul_y
  simp only [map_mul] at hCanonical
  apply (IsUnit.mul_right_inj
    (IsLocalization.Away.algebraMap_isUnit
      canonicalWChartProjectionDenominator)).mp
  exact hPlane.trans hCanonical.symm

/-- The inverse-projection candidate as a canonical point on `w = 1`. -/
def planeDOpenCanonicalPoint :
    RationalPointsN25QuotientF2.Coordinates4 PlaneDOpen :=
  wChartPoint planeDOpenX planeDOpenY planeDOpenZ

/-- The universal plane equation remains zero after passing to the
principal open. -/
theorem planeDOpen_planeSexticValue :
    planeSexticValue planeDOpenX planeDOpenZ = 0 := by
  have h := congrArg (algebraMap PlaneCoordinateRing PlaneDOpen)
    planeSexticValue_planeCoordinates
  simpa [planeDOpenX, planeDOpenZ, planeSexticValue] using h

/-- The candidate inverse coordinates satisfy the canonical cubic. -/
theorem planeDOpenCanonicalPoint_cubic :
    canonicalCubic25CharTwo planeDOpenCanonicalPoint = 0 := by
  rw [planeDOpenCanonicalPoint, canonicalCubic_wChart]
  rw [← planeDOpenDenominator_eq_projection,
    ← planeDOpenNumerator_eq_projection]
  rw [mul_comm, planeDOpenDenominator_mul_y]
  linear_combination planeDOpenNumerator * planeDOpen_two_eq_zero

/-- The candidate inverse coordinates satisfy the canonical quadric.  The
division-free syzygy first proves this after multiplication by `D²`; the
unit property of `D` then cancels that factor. -/
theorem planeDOpenCanonicalPoint_quadric :
    canonicalQuadric25CharTwo planeDOpenCanonicalPoint = 0 := by
  have hmul := denominator_sq_mul_canonicalQuadric_of_two_eq_zero
    planeDOpenX planeDOpenY planeDOpenZ planeDOpen_two_eq_zero
  rw [← planeDOpenCanonicalPoint] at hmul
  rw [planeDOpen_planeSexticValue, planeDOpenCanonicalPoint_cubic] at hmul
  simp only [zero_mul, add_zero] at hmul
  rw [← planeDOpenDenominator_eq_projection] at hmul
  have hunit : IsUnit (planeDOpenDenominator ^ 2) :=
    (IsLocalization.Away.algebraMap_isUnit
      planeProjectionDenominator).pow 2
  exact (IsUnit.mul_right_eq_zero hunit).mp hmul

/-! ## The reverse map from the canonical chart -/

/-- Evaluate a free affine variable at the corresponding coordinate of the
inverse-projection candidate. -/
def canonicalWChartAffineVariableToPlaneDOpen
    (j : OtherCoordinate 3) : PlaneDOpen :=
  coordinates4ToFun planeDOpenCanonicalPoint j.1

/-- Evaluation of the three-variable `w = 1` polynomial ring at the
inverse-projection candidate. -/
def canonicalWChartAffinePolynomialToPlaneDOpen :
    AffineChart 3 →+* PlaneDOpen :=
  MvPolynomial.eval₂Hom (algebraMap k PlaneDOpen)
    canonicalWChartAffineVariableToPlaneDOpen

theorem canonicalWChartAffinePolynomialToPlaneDOpen_quadric :
    canonicalWChartAffinePolynomialToPlaneDOpen (chartAffineQuadric 3) = 0 := by
  simpa [canonicalWChartAffinePolynomialToPlaneDOpen,
    canonicalWChartAffineVariableToPlaneDOpen,
    planeDOpenCanonicalPoint, chartAffineQuadric,
    ambientDehomogenize, dehomogenizedVariable,
    RationalPointsN25QuotientTwoConormal.canonicalQuadricPolynomial25Two,
    canonicalQuadric25CharTwo, wChartPoint, coordinates4ToFun] using
      planeDOpenCanonicalPoint_quadric

theorem canonicalWChartAffinePolynomialToPlaneDOpen_cubic :
    canonicalWChartAffinePolynomialToPlaneDOpen (chartAffineCubic 3) = 0 := by
  simpa [canonicalWChartAffinePolynomialToPlaneDOpen,
    canonicalWChartAffineVariableToPlaneDOpen,
    planeDOpenCanonicalPoint, chartAffineCubic,
    ambientDehomogenize, dehomogenizedVariable,
    RationalPointsN25QuotientTwoConormal.canonicalCubicPolynomial25Two,
    canonicalCubic25CharTwo, wChartPoint, coordinates4ToFun] using
      planeDOpenCanonicalPoint_cubic

theorem wChartAffineEquationIdeal_le_planeEvaluationKernel :
    chartAffineEquationIdeal 3 ≤
      RingHom.ker canonicalWChartAffinePolynomialToPlaneDOpen := by
  rw [chartAffineEquationIdeal, Ideal.span_le]
  rintro f ⟨r, rfl⟩
  fin_cases r
  · exact canonicalWChartAffinePolynomialToPlaneDOpen_quadric
  · exact canonicalWChartAffinePolynomialToPlaneDOpen_cubic

/-- The reverse coordinate-ring map before localizing the canonical chart. -/
def canonicalWChartToPlaneDOpen : ChartQuotient 3 →+* PlaneDOpen :=
  Ideal.Quotient.lift (chartAffineEquationIdeal 3)
    canonicalWChartAffinePolynomialToPlaneDOpen
    wChartAffineEquationIdeal_le_planeEvaluationKernel

@[simp]
theorem canonicalWChartToPlaneDOpen_mk (p : AffineChart 3) :
    canonicalWChartToPlaneDOpen
        (Ideal.Quotient.mk (chartAffineEquationIdeal 3) p) =
      canonicalWChartAffinePolynomialToPlaneDOpen p := by
  exact Ideal.Quotient.lift_mk _ _ _

@[simp]
theorem canonicalWChartToPlaneDOpen_x :
    canonicalWChartToPlaneDOpen canonicalWChartX = planeDOpenX := by
  simp [canonicalWChartToPlaneDOpen, canonicalWChartX,
    canonicalWChartPoint, chartQuotientPoint, mappedAmbientPoint, chartMap,
    ambientDehomogenize, dehomogenizedVariable,
    canonicalWChartAffinePolynomialToPlaneDOpen,
    canonicalWChartAffineVariableToPlaneDOpen,
    planeDOpenCanonicalPoint, wChartPoint, coordinates4ToFun]

@[simp]
theorem canonicalWChartToPlaneDOpen_y :
    canonicalWChartToPlaneDOpen canonicalWChartY = planeDOpenY := by
  simp [canonicalWChartToPlaneDOpen, canonicalWChartY,
    canonicalWChartPoint, chartQuotientPoint, mappedAmbientPoint, chartMap,
    ambientDehomogenize, dehomogenizedVariable,
    canonicalWChartAffinePolynomialToPlaneDOpen,
    canonicalWChartAffineVariableToPlaneDOpen,
    planeDOpenCanonicalPoint, wChartPoint, coordinates4ToFun]

@[simp]
theorem canonicalWChartToPlaneDOpen_z :
    canonicalWChartToPlaneDOpen canonicalWChartZ = planeDOpenZ := by
  simp [canonicalWChartToPlaneDOpen, canonicalWChartZ,
    canonicalWChartPoint, chartQuotientPoint, mappedAmbientPoint, chartMap,
    ambientDehomogenize, dehomogenizedVariable,
    canonicalWChartAffinePolynomialToPlaneDOpen,
    canonicalWChartAffineVariableToPlaneDOpen,
    planeDOpenCanonicalPoint, wChartPoint, coordinates4ToFun]

@[simp]
theorem canonicalWChartToPlaneDOpen_denominator :
    canonicalWChartToPlaneDOpen canonicalWChartProjectionDenominator =
      planeDOpenDenominator := by
  simp [canonicalWChartProjectionDenominator, projectionDenominator]

theorem canonicalDenominator_mapsToUnit :
    IsUnit
      (canonicalWChartToPlaneDOpen canonicalWChartProjectionDenominator) := by
  rw [canonicalWChartToPlaneDOpen_denominator]
  exact IsLocalization.Away.algebraMap_isUnit planeProjectionDenominator

/-- The reverse coordinate-ring map on the common principal open. -/
def canonicalWChartDOpenToPlaneDOpen :
    CanonicalWChartDOpen →+* PlaneDOpen :=
  IsLocalization.Away.lift canonicalWChartProjectionDenominator
    canonicalDenominator_mapsToUnit

@[simp]
theorem canonicalWChartDOpenToPlaneDOpen_algebraMap
    (c : ChartQuotient 3) :
    canonicalWChartDOpenToPlaneDOpen
        (algebraMap (ChartQuotient 3) CanonicalWChartDOpen c) =
      canonicalWChartToPlaneDOpen c := by
  exact IsLocalization.Away.lift_eq
    canonicalWChartProjectionDenominator canonicalDenominator_mapsToUnit c

/-- The reverse principal-open map is a left inverse of the forward map. -/
theorem canonicalWChartDOpenToPlaneDOpen_comp_planeDOpenToCanonicalWChartDOpen :
    canonicalWChartDOpenToPlaneDOpen.comp
        planeDOpenToCanonicalWChartDOpen =
      RingHom.id PlaneDOpen := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers planeProjectionDenominator)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,
        planeDOpenToCanonicalWChartDOpen_algebraMap,
        canonicalWChartDOpenToPlaneDOpen_algebraMap,
        planeCoordinateRingToCanonicalWChart, AdjoinRoot.lift_of,
        zPolynomialToCanonicalWChart, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      calc
        _ = algebraMap k PlaneDOpen a := by
          change canonicalWChartToPlaneDOpen
              (Ideal.Quotient.mk (chartAffineEquationIdeal 3)
                (MvPolynomial.C a)) =
            algebraMap k PlaneDOpen a
          rw [canonicalWChartToPlaneDOpen_mk]
          simp [canonicalWChartAffinePolynomialToPlaneDOpen]
        _ = _ := by
          rw [← evalAtPlaneZ_eq_adjoinRootOf]
          simpa using
            (IsScalarTower.algebraMap_apply
              k PlaneCoordinateRing PlaneDOpen a)
    · change canonicalWChartDOpenToPlaneDOpen
          (planeDOpenToCanonicalWChartDOpen planeDOpenZ) = planeDOpenZ
      simp
  · change canonicalWChartDOpenToPlaneDOpen
        (planeDOpenToCanonicalWChartDOpen planeDOpenX) = planeDOpenX
    simp

/-- The forward principal-open map is a left inverse of the reverse map. -/
theorem planeDOpenToCanonicalWChartDOpen_comp_canonicalWChartDOpenToPlaneDOpen :
    planeDOpenToCanonicalWChartDOpen.comp
        canonicalWChartDOpenToPlaneDOpen =
      RingHom.id CanonicalWChartDOpen := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers canonicalWChartProjectionDenominator)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,
      canonicalWChartDOpenToPlaneDOpen_algebraMap,
      canonicalWChartToPlaneDOpen_mk,
      canonicalWChartAffinePolynomialToPlaneDOpen,
      MvPolynomial.eval₂Hom_C]
    rw [IsScalarTower.algebraMap_apply k PlaneCoordinateRing PlaneDOpen,
      planeDOpenToCanonicalWChartDOpen_algebraMap]
    change algebraMap (ChartQuotient 3) CanonicalWChartDOpen
          (planeCoordinateRingToCanonicalWChart
            (algebraMap k PlaneCoordinateRing a)) =
        algebraMap (ChartQuotient 3) CanonicalWChartDOpen
          (Ideal.Quotient.mk (chartAffineEquationIdeal 3)
            (MvPolynomial.C a))
    apply congrArg (algebraMap (ChartQuotient 3) CanonicalWChartDOpen)
    have hCoeff :
        algebraMap k PlaneCoordinateRing a =
          AdjoinRoot.of planeSexticPolynomial (Polynomial.C a) := by
      simpa [AdjoinRoot.algebraMap_eq] using
        (IsScalarTower.algebraMap_apply k k[X] PlaneCoordinateRing a)
    rw [hCoeff]
    simp [planeCoordinateRingToCanonicalWChart,
      zPolynomialToCanonicalWChart]
    simpa using
      (IsScalarTower.algebraMap_apply
        k (AffineChart 3) (ChartQuotient 3) a)
  · rintro ⟨j, hj⟩
    fin_cases j
    · simp [RingHom.comp_apply, canonicalWChartToPlaneDOpen,
        canonicalWChartAffinePolynomialToPlaneDOpen,
        canonicalWChartAffineVariableToPlaneDOpen,
        planeDOpenCanonicalPoint, wChartPoint, coordinates4ToFun,
        canonicalWChartX, canonicalWChartPoint, chartQuotientPoint,
        mappedAmbientPoint, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
    · simp [RingHom.comp_apply, canonicalWChartToPlaneDOpen,
        canonicalWChartAffinePolynomialToPlaneDOpen,
        canonicalWChartAffineVariableToPlaneDOpen,
        planeDOpenCanonicalPoint, wChartPoint, coordinates4ToFun,
        canonicalWChartY, canonicalWChartPoint, chartQuotientPoint,
        mappedAmbientPoint, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
    · simp [RingHom.comp_apply, canonicalWChartToPlaneDOpen,
        canonicalWChartAffinePolynomialToPlaneDOpen,
        canonicalWChartAffineVariableToPlaneDOpen,
        planeDOpenCanonicalPoint, wChartPoint, coordinates4ToFun,
        canonicalWChartZ, canonicalWChartPoint, chartQuotientPoint,
        mappedAmbientPoint, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
    · exact (hj rfl).elim

/-- The explicit birational projection is an isomorphism on the principal
open `D ≠ 0`. -/
noncomputable def planeDOpenEquivCanonicalWChartDOpen :
    PlaneDOpen ≃+* CanonicalWChartDOpen where
  toEquiv :=
    { toFun := planeDOpenToCanonicalWChartDOpen
      invFun := canonicalWChartDOpenToPlaneDOpen
      left_inv := fun p ↦ by
        simpa using DFunLike.congr_fun
          canonicalWChartDOpenToPlaneDOpen_comp_planeDOpenToCanonicalWChartDOpen p
      right_inv := fun c ↦ by
        simpa using DFunLike.congr_fun
          planeDOpenToCanonicalWChartDOpen_comp_canonicalWChartDOpenToPlaneDOpen c }
  map_mul' := planeDOpenToCanonicalWChartDOpen.map_mul
  map_add' := planeDOpenToCanonicalWChartDOpen.map_add

@[simp]
theorem planeDOpenEquivCanonicalWChartDOpen_apply (p : PlaneDOpen) :
    planeDOpenEquivCanonicalWChartDOpen p =
      planeDOpenToCanonicalWChartDOpen p :=
  rfl

@[simp]
theorem planeDOpenEquivCanonicalWChartDOpen_symm_apply
    (c : CanonicalWChartDOpen) :
    planeDOpenEquivCanonicalWChartDOpen.symm c =
      canonicalWChartDOpenToPlaneDOpen c :=
  rfl

end MazurProof.RationalPointsN25QuotientTwoPlaneChartLocalization
