import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCharts
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingTransition
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingSheafCharts
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingSheafGluing
import FLT.Mathlib.RingTheory.Kaehler.FormallyEtale

/-!
# Canonical differentials on the N25 coordinate overlaps

The two projections from an ordered pair overlap are localizations of the
corresponding homogeneous chart rings.  Formally etale base change therefore
transports both chart residue coordinates to the same overlap differential
module.  This file constructs the two resulting rank-one coordinates; their
remaining change-of-basis calculation is the projective adjunction seam.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps

open RationalPointsN25QuotientTwoCanonicalDifferentialCharts
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineCanonicalDifferentials
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingTransition
open RationalPointsN25QuotientTwoStructuralJacobian
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical chart ring and the overlap chart ring use propositionally
equal homogeneous denominators.  This cast records that equality explicitly. -/
def chartCoordinateRingCastEquiv (i : Fin 4) :
    ChartCoordinateRing i ≃+* coordinateChartRing i :=
  RingEquiv.refl _

/-- The first projection from a homogeneous chart ring to an ordered overlap. -/
def coordinateChartToLeftOverlapRingHom (i j : Fin 4) :
    ChartCoordinateRing i →+* coordinateOverlapRing i j :=
  (awayMap literalConePiece (f := coordinateClass i)
    (coordinateClass_mem_degreeOne j) rfl).comp
      (chartCoordinateRingCastEquiv i).toRingHom

/-- The second projection from a homogeneous chart ring to an ordered overlap. -/
def coordinateChartToRightOverlapRingHom (i j : Fin 4) :
    ChartCoordinateRing j →+* coordinateOverlapRing i j :=
  (awayMap literalConePiece (f := coordinateClass j)
    (coordinateClass_mem_degreeOne i) (mul_comm _ _)).comp
      (chartCoordinateRingCastEquiv j).toRingHom

/-- The binary coefficient algebra on a homogeneous chart is the transported
algebra used by its explicit Kahler differential coordinate. -/
noncomputable instance coordinateChartRingAlgebra (i : Fin 4) :
    Algebra k (ChartCoordinateRing i) :=
  RationalPointsN25QuotientTwoAffineChartsSmooth.chartCoordinateRingAlgebra i

noncomputable instance coordinateChartRingSMul (i : Fin 4) :
    SMul k (ChartCoordinateRing i) :=
  (RationalPointsN25QuotientTwoAffineChartsSmooth.chartCoordinateRingAlgebra i).toSMul

/-- The coefficient algebra on an ordered overlap is oriented through its
first chart projection. -/
noncomputable instance coordinateOverlapRingAlgebra (i j : Fin 4) :
    Algebra k (coordinateOverlapRing i j) :=
  ((coordinateChartToLeftOverlapRingHom i j).comp
      (algebraMap k (ChartCoordinateRing i))).toAlgebra

noncomputable instance coordinateOverlapRingSMul (i j : Fin 4) :
    SMul k (coordinateOverlapRing i j) :=
  (coordinateOverlapRingAlgebra i j).toSMul

/-- An ordinary affine variable becomes the same chart ratio used as the
localization parameter in the homogeneous presentation. -/
theorem chartCoordinateRingEquivAffine_X_eq_isLocalizationElem
    (i : Fin 4) (j : OtherCoordinate i) :
    chartCoordinateRingEquivAffine i
        (algebraMap (AffineChart i) (ChartQuotient i) (MvPolynomial.X j)) =
      (chartCoordinateRingCastEquiv i).symm
        (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j.1)) := by
  change chartCoordinateRingEquivAffine i
      (Ideal.Quotient.mk (chartAffineEquationIdeal i) (MvPolynomial.X j)) = _
  rw [chartCoordinateRingEquivAffine_mk, standardChartEquiv_apply,
    affineToStandardChart_X]
  unfold canonicalConeChartMap coordinateRatio fullRatio
  rw [Away.map_mk]
  change Away.mk literalConePiece _ 1
      (canonicalConeGradedProjection (MvPolynomial.X j.1)) _ =
    Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j.1)
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk]

/-- The residue coordinate of the chart localization parameter is the image
of the corresponding affine Jacobian minor. -/
theorem chartCoordinateKaehlerDifferentialEquiv_D_isLocalizationElem
    (i : Fin 4) (j : OtherCoordinate i) :
    chartCoordinateKaehlerDifferentialEquiv i
        (KaehlerDifferential.D k (ChartCoordinateRing i)
          ((chartCoordinateRingCastEquiv i).symm
            (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
              (coordinateClass_mem_degreeOne j.1)))) =
      chartCoordinateRingEquivAffine i
        (chartJacobianCross i ((finSuccAboveEquiv i).symm j)) := by
  let e := chartCoordinateRingAlgEquivAffine i
  letI := RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI := RingHomInvPair.symm
    (↑e.toRingEquiv : ChartQuotient i →+* ChartCoordinateRing i)
    (e.toRingEquiv.symm : ChartCoordinateRing i →+* ChartQuotient i)
  rw [← chartCoordinateRingEquivAffine_X_eq_isLocalizationElem]
  change chartCoordinateKaehlerDifferentialEquiv i
      (KaehlerDifferential.D k (ChartCoordinateRing i)
        (e (algebraMap (AffineChart i) (ChartQuotient i)
          (MvPolynomial.X j)))) =
    e (chartJacobianCross i ((finSuccAboveEquiv i).symm j))
  rw [← KaehlerDifferential.mapAlgEquiv_D e]
  rw [chartCoordinateKaehlerDifferentialEquiv_mapAlgEquiv]
  change e (chartKaehlerDifferentialEquiv i
      (KaehlerDifferential.D k (ChartQuotient i)
        (algebraMap (AffineChart i) (ChartQuotient i)
          (MvPolynomial.X j)))) =
    e (chartJacobianCross i ((finSuccAboveEquiv i).symm j))
  let r := (finSuccAboveEquiv i).symm j
  have hj : affineCoordinate i r = j :=
    (finSuccAboveEquiv i).apply_symm_apply j
  have h := chartKaehlerDifferentialEquiv_D_coordinate i r
  rw [hj] at h
  exact congrArg e h

/-- The element inverted from the first chart becomes the coordinate ratio
`X_j/X_i` on the ordered overlap. -/
theorem coordinateChartToLeftOverlapRingHom_isLocalizationElem (i j : Fin 4) :
    coordinateChartToLeftOverlapRingHom i j
        ((chartCoordinateRingCastEquiv i).symm
          (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
            (coordinateClass_mem_degreeOne j))) =
      Away.degreeOneRatio literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) := by
  rw [coordinateChartToLeftOverlapRingHom, RingHom.comp_apply]
  change (awayMap literalConePiece (coordinateClass_mem_degreeOne j) rfl)
      (chartCoordinateRingCastEquiv i
        ((chartCoordinateRingCastEquiv i).symm
          (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
            (coordinateClass_mem_degreeOne j)))) = _
  rw [(chartCoordinateRingCastEquiv i).apply_symm_apply]
  rw [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp [Away.degreeOneRatio, pow_two]

/-- The element inverted from the second chart becomes the reverse coordinate
ratio `X_i/X_j` on the ordered overlap. -/
theorem coordinateChartToRightOverlapRingHom_isLocalizationElem (i j : Fin 4) :
    coordinateChartToRightOverlapRingHom i j
        ((chartCoordinateRingCastEquiv j).symm
          (Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
            (coordinateClass_mem_degreeOne i))) =
      Away.degreeOneRatioInv literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) := by
  rw [coordinateChartToRightOverlapRingHom, RingHom.comp_apply]
  change (awayMap literalConePiece (coordinateClass_mem_degreeOne i) (mul_comm _ _))
      (chartCoordinateRingCastEquiv j
        ((chartCoordinateRingCastEquiv j).symm
          (Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
            (coordinateClass_mem_degreeOne i)))) = _
  rw [(chartCoordinateRingCastEquiv j).apply_symm_apply]
  rw [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp [Away.degreeOneRatioInv, pow_two]

/-- Restricting a homogeneous polynomial through the first affine chart is
the left homogeneous expression on the ordered overlap. -/
theorem coordinateChartToLeftOverlapRingHom_chartMap
    (i j : Fin 4) (n : ℕ) (p : S) (hp : p ∈ standardConePiece n) :
    coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i (chartMap i p)) =
      Away.homogeneousElementLeft literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) n
        (canonicalConeGradedProjection.map_mem hp) := by
  rw [chartCoordinateRingEquivAffine_chartMap i n p (by simpa using hp)]
  rfl

/-- Restricting a homogeneous polynomial through the second affine chart is
the right homogeneous expression on the ordered overlap. -/
theorem coordinateChartToRightOverlapRingHom_chartMap
    (i j : Fin 4) (n : ℕ) (p : S) (hp : p ∈ standardConePiece n) :
    coordinateChartToRightOverlapRingHom i j
        (chartCoordinateRingEquivAffine j (chartMap j p)) =
      Away.homogeneousElementRight literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) n
        (canonicalConeGradedProjection.map_mem hp) := by
  rw [chartCoordinateRingEquivAffine_chartMap j n p (by simpa using hp)]
  rfl

/-- The normalized ambient coordinate `X_t/X_i` on the first chart, viewed
on the ordered overlap. -/
def coordinateOverlapLeftCoordinate (i j t : Fin 4) :
    coordinateOverlapRing i j :=
  Away.homogeneousElementLeft literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) 1
    (coordinateClass_mem_degreeOne t)

/-- The normalized ambient coordinate `X_t/X_j` on the second chart, viewed
on the same ordered overlap. -/
def coordinateOverlapRightCoordinate (i j t : Fin 4) :
    coordinateOverlapRing i j :=
  Away.homogeneousElementRight literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) 1
    (coordinateClass_mem_degreeOne t)

/-- The pivot-normalized coordinate on the second chart is one. -/
theorem coordinateOverlapRightCoordinate_pivot (i j : Fin 4) :
    coordinateOverlapRightCoordinate i j j = 1 := by
  unfold coordinateOverlapRightCoordinate
  rw [← coordinateChartToRightOverlapRingHom_chartMap i j 1
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X (ZMod 2) j)]
  simp

/-- The second ambient coordinate normalized on the first chart is the
basic overlap ratio `X_j/X_i`. -/
theorem coordinateOverlapLeftCoordinate_second (i j : Fin 4) :
    coordinateOverlapLeftCoordinate i j j =
      Away.degreeOneRatio literalConePiece
        (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j) := by
  apply HomogeneousLocalization.val_injective
  simp [coordinateOverlapLeftCoordinate,
    Away.homogeneousElementLeft, Away.degreeOneRatio, pow_two]

/-- The first ambient coordinate normalized on the second chart is the
inverse overlap ratio `X_i/X_j`. -/
theorem coordinateOverlapRightCoordinate_first (i j : Fin 4) :
    coordinateOverlapRightCoordinate i j i =
      Away.degreeOneRatioInv literalConePiece
        (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j) := by
  apply HomogeneousLocalization.val_injective
  simp [coordinateOverlapRightCoordinate,
    Away.homogeneousElementRight, Away.degreeOneRatioInv, pow_two]

/-- Normalized ambient coordinates on the two charts differ by the basic
coordinate ratio `X_j/X_i`. -/
theorem coordinateOverlapCoordinate_transition (i j t : Fin 4) :
    coordinateOverlapLeftCoordinate i j t =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) *
        coordinateOverlapRightCoordinate i j t := by
  simpa only [coordinateOverlapLeftCoordinate,
    coordinateOverlapRightCoordinate, coordinateRatioUnit, pow_one] using
      Away.homogeneousElementLeft_eq_ratio_mul_right literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) 1
        (coordinateClass_mem_degreeOne t)

/-- A non-pivot affine coordinate from the first chart maps to its normalized
homogeneous coordinate on the overlap. -/
theorem coordinateChartToLeftOverlapRingHom_affineCoordinate
    (i j : Fin 4) (r : Fin 3) :
    coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i
          (algebraMap (AffineChart i) (ChartQuotient i)
            (MvPolynomial.X (affineCoordinate i r)))) =
      coordinateOverlapLeftCoordinate i j (i.succAbove r) := by
  rw [← dehomogenizedVariable_succAbove]
  rw [← ambientDehomogenize_X]
  change coordinateChartToLeftOverlapRingHom i j
      (chartCoordinateRingEquivAffine i
        (chartMap i (MvPolynomial.X (i.succAbove r)))) = _
  exact coordinateChartToLeftOverlapRingHom_chartMap i j 1
    (MvPolynomial.X (i.succAbove r))
    (MvPolynomial.isHomogeneous_X (ZMod 2) (i.succAbove r))

/-- A non-pivot affine coordinate from the second chart maps to its normalized
homogeneous coordinate on the overlap. -/
theorem coordinateChartToRightOverlapRingHom_affineCoordinate
    (i j : Fin 4) (r : Fin 3) :
    coordinateChartToRightOverlapRingHom i j
        (chartCoordinateRingEquivAffine j
          (algebraMap (AffineChart j) (ChartQuotient j)
            (MvPolynomial.X (affineCoordinate j r)))) =
      coordinateOverlapRightCoordinate i j (j.succAbove r) := by
  rw [← dehomogenizedVariable_succAbove]
  rw [← ambientDehomogenize_X]
  change coordinateChartToRightOverlapRingHom i j
      (chartCoordinateRingEquivAffine j
        (chartMap j (MvPolynomial.X (j.succAbove r)))) = _
  exact coordinateChartToRightOverlapRingHom_chartMap i j 1
    (MvPolynomial.X (j.succAbove r))
    (MvPolynomial.isHomogeneous_X (ZMod 2) (j.succAbove r))

/-- The two chart restrictions of a degree-`n` homogeneous polynomial differ
by the `n`th power of the projective coordinate ratio. -/
theorem coordinateChartMap_transition
    (i j : Fin 4) (n : ℕ) (p : S) (hp : p ∈ standardConePiece n) :
    coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i (chartMap i p)) =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) ^ n *
        coordinateChartToRightOverlapRingHom i j
          (chartCoordinateRingEquivAffine j (chartMap j p)) := by
  rw [coordinateChartToLeftOverlapRingHom_chartMap i j n p hp,
    coordinateChartToRightOverlapRingHom_chartMap i j n p hp]
  exact Away.homogeneousElementLeft_eq_ratio_mul_right literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) n
    (canonicalConeGradedProjection.map_mem hp)

/-- In particular, every ambient Jacobian minor has cubic transition weight
on an ordered projective overlap. -/
theorem ambientPolynomialMinor_chartTransition
    (i j a b : Fin 4) :
    coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i
          (chartMap i (ambientPolynomialMinor a b))) =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) ^ 3 *
        coordinateChartToRightOverlapRingHom i j
          (chartCoordinateRingEquivAffine j
            (chartMap j (ambientPolynomialMinor a b))) := by
  apply coordinateChartMap_transition i j 3
  simpa [standardConePiece, MvPolynomial.mem_homogeneousSubmodule] using
    ambientPolynomialMinor_isHomogeneous a b

/-- The left-chart expression of an ambient Jacobian minor on an ordered
overlap. -/
def coordinateOverlapLeftMinor (i j a b : Fin 4) :
    coordinateOverlapRing i j :=
  coordinateChartToLeftOverlapRingHom i j
    (chartCoordinateRingEquivAffine i
      (chartMap i (ambientPolynomialMinor a b)))

/-- The right-chart expression of an ambient Jacobian minor on the same
ordered overlap. -/
def coordinateOverlapRightMinor (i j a b : Fin 4) :
    coordinateOverlapRing i j :=
  coordinateChartToRightOverlapRingHom i j
    (chartCoordinateRingEquivAffine j
      (chartMap j (ambientPolynomialMinor a b)))

/-- A right-chart minor with repeated columns vanishes. -/
@[simp]
theorem coordinateOverlapRightMinor_self (i j a : Fin 4) :
    coordinateOverlapRightMinor i j a a = 0 := by
  simp [coordinateOverlapRightMinor]

/-- Ambient minors have cubic weight between their left and right overlap
expressions. -/
theorem coordinateOverlapMinor_transition (i j a b : Fin 4) :
    coordinateOverlapLeftMinor i j a b =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) ^ 3 *
        coordinateOverlapRightMinor i j a b := by
  exact ambientPolynomialMinor_chartTransition i j a b

/-- Euler's minor syzygy remains zero after restriction through the second
chart to an ordered overlap. -/
theorem coordinateOverlapRight_weighted_minor_sum_zero
    (i j a : Fin 4) :
    ∑ t : Fin 4, coordinateOverlapRightCoordinate i j t *
        coordinateOverlapRightMinor i j t a = 0 := by
  have h := congrArg
    (fun x : ChartQuotient j ↦ coordinateChartToRightOverlapRingHom i j
      (chartCoordinateRingEquivAffine j x))
    (chartMap_weighted_minor_sum_zero j a)
  simp only [map_sum, map_mul, map_zero] at h
  have hcoordinate (t : Fin 4) :
      coordinateChartToRightOverlapRingHom i j
          (chartCoordinateRingEquivAffine j
            (chartMap j (MvPolynomial.X t))) =
        coordinateOverlapRightCoordinate i j t := by
    simpa only [coordinateOverlapRightCoordinate] using
      coordinateChartToRightOverlapRingHom_chartMap i j 1
        (MvPolynomial.X t) (MvPolynomial.isHomogeneous_X (ZMod 2) t)
  simp_rw [hcoordinate] at h
  simpa only [coordinateOverlapRightMinor] using h

/-- For four distinct coordinate labels, Euler's syzygy expresses the minor
through the chart pivot as the sum of the other two nonzero terms. -/
theorem coordinateOverlapRight_minor_euler_three
    (i j t l : Fin 4)
    (hij : i ≠ j) (hit : i ≠ t) (hil : i ≠ l)
    (hjt : j ≠ t) (hjl : j ≠ l) (htl : t ≠ l) :
    coordinateOverlapRightMinor i j j l =
      coordinateOverlapRightCoordinate i j i *
          coordinateOverlapRightMinor i j i l +
        coordinateOverlapRightCoordinate i j t *
          coordinateOverlapRightMinor i j t l := by
  have hsum := coordinateOverlapRight_weighted_minor_sum_zero i j l
  have huniv : Finset.univ = {i, j, t, l} := by
    ext s
    simp
    omega
  rw [huniv] at hsum
  simp [hij, hit, hil, hjt, hjl, htl,
    coordinateOverlapRightCoordinate_pivot] at hsum
  have hsum' :
      coordinateOverlapRightMinor i j j l +
          (coordinateOverlapRightCoordinate i j i *
              coordinateOverlapRightMinor i j i l +
            coordinateOverlapRightCoordinate i j t *
              coordinateOverlapRightMinor i j t l) = 0 := by
    calc
      _ = coordinateOverlapRightCoordinate i j i *
            coordinateOverlapRightMinor i j i l +
          (coordinateOverlapRightMinor i j j l +
            coordinateOverlapRightCoordinate i j t *
              coordinateOverlapRightMinor i j t l) := by ring
      _ = 0 := hsum
  have hrest := eq_neg_of_add_eq_zero_left hsum'
  have hneg (x : coordinateOverlapRing i j) : -x = x := by
    have htwo : (2 : coordinateOverlapRing i j) = 0 := by
      calc
        (2 : coordinateOverlapRing i j) =
            algebraMap k (coordinateOverlapRing i j) (2 : k) :=
          (map_natCast (algebraMap k (coordinateOverlapRing i j)) 2).symm
        _ = algebraMap k (coordinateOverlapRing i j) 0 := by
          exact congrArg (algebraMap k (coordinateOverlapRing i j))
            (CharP.cast_eq_zero k 2)
        _ = 0 := map_zero _
    have hx : x + x = 0 := by
      calc
        x + x = (2 : coordinateOverlapRing i j) * x := by ring
        _ = 0 := by rw [htwo, zero_mul]
    exact (eq_neg_of_add_eq_zero_left hx).symm
  rw [hneg] at hrest
  exact hrest

/-- The cross component selected by omitting the other chart pivot has cubic
transition weight between the two affine Jacobian presentations. -/
theorem chartJacobianCross_chartTransition
    (i j : Fin 4) (hji : j ≠ i) :
    coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i
          (chartJacobianCross i
            ((finSuccAboveEquiv i).symm ⟨j, hji⟩))) =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) ^ 3 *
        coordinateChartToRightOverlapRingHom i j
          (chartCoordinateRingEquivAffine j
            (chartJacobianCross j
              ((finSuccAboveEquiv j).symm ⟨i, hji.symm⟩))) := by
  rw [chartJacobianCross_eq_chartMap_minor,
    chartJacobianCross_eq_chartMap_minor]
  rw [← ambientPolynomialMinor_complementary_chart_pair i j hji]
  apply ambientPolynomialMinor_chartTransition

/-- The residue coordinate from the first chart, localized to an ordered
pair overlap. -/
def coordinateOverlapLeftKaehlerDifferentialEquiv (i j : Fin 4) :
    Ω[coordinateOverlapRing i j⁄k] ≃ₗ[coordinateOverlapRing i j]
      coordinateOverlapRing i j := by
  letI : Algebra (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  haveI : Algebra.FormallyEtale (ChartCoordinateRing i)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)))
  letI : IsScalarTower k (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact KaehlerDifferential.coordinateEquivOfFormallyEtale
    (chartCoordinateKaehlerDifferentialEquiv i)

/-- The residue coordinate from the second chart, localized to the same
ordered pair overlap. -/
def coordinateOverlapRightKaehlerDifferentialEquiv (i j : Fin 4) :
    Ω[coordinateOverlapRing i j⁄k] ≃ₗ[coordinateOverlapRing i j]
      coordinateOverlapRing i j := by
  letI : Algebra (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne i))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  haveI : Algebra.FormallyEtale (ChartCoordinateRing j)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne j) (coordinateClass_mem_degreeOne i)))
  letI : IsScalarTower k (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  exact KaehlerDifferential.coordinateEquivOfFormallyEtale
    (chartCoordinateKaehlerDifferentialEquiv j)

/-- The differential map from the first chart to an ordered overlap. -/
def coordinateOverlapLeftKaehlerDifferentialMap (i j : Fin 4) :
    Ω[ChartCoordinateRing i⁄k] → Ω[coordinateOverlapRing i j⁄k] := fun x ↦ by
  letI : Algebra (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsScalarTower k (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact KaehlerDifferential.map k k
    (ChartCoordinateRing i) (coordinateOverlapRing i j) x

/-- The first-chart differential map commutes with the universal
derivation. -/
theorem coordinateOverlapLeftKaehlerDifferentialMap_D
    (i j : Fin 4) (x : ChartCoordinateRing i) :
    coordinateOverlapLeftKaehlerDifferentialMap i j
        (KaehlerDifferential.D k (ChartCoordinateRing i) x) =
      KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateChartToLeftOverlapRingHom i j x) := by
  letI : Algebra (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsScalarTower k (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  change KaehlerDifferential.map k k
      (ChartCoordinateRing i) (coordinateOverlapRing i j)
        (KaehlerDifferential.D k (ChartCoordinateRing i) x) = _
  rw [KaehlerDifferential.map_D]
  rw [RingHom.algebraMap_toAlgebra]

/-- The left overlap coordinate maps a differential from the first chart to
the image of its residue coordinate. -/
theorem coordinateOverlapLeftKaehlerDifferentialEquiv_map
    (i j : Fin 4) (x : Ω[ChartCoordinateRing i⁄k]) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (coordinateOverlapLeftKaehlerDifferentialMap i j x) =
      coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateKaehlerDifferentialEquiv i x) := by
  letI : Algebra (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  haveI : Algebra.FormallyEtale (ChartCoordinateRing i)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)))
  letI : IsScalarTower k (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact KaehlerDifferential.coordinateEquivOfFormallyEtale_map
    (chartCoordinateKaehlerDifferentialEquiv i) x

/-- The differential map from the second chart to an ordered overlap. -/
def coordinateOverlapRightKaehlerDifferentialMap (i j : Fin 4) :
    Ω[ChartCoordinateRing j⁄k] → Ω[coordinateOverlapRing i j⁄k] := fun x ↦ by
  letI : Algebra (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsScalarTower k (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  exact KaehlerDifferential.map k k
    (ChartCoordinateRing j) (coordinateOverlapRing i j) x

/-- The second-chart differential map commutes with the universal
derivation. -/
theorem coordinateOverlapRightKaehlerDifferentialMap_D
    (i j : Fin 4) (x : ChartCoordinateRing j) :
    coordinateOverlapRightKaehlerDifferentialMap i j
        (KaehlerDifferential.D k (ChartCoordinateRing j) x) =
      KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateChartToRightOverlapRingHom i j x) := by
  letI : Algebra (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsScalarTower k (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  change KaehlerDifferential.map k k
      (ChartCoordinateRing j) (coordinateOverlapRing i j)
        (KaehlerDifferential.D k (ChartCoordinateRing j) x) = _
  rw [KaehlerDifferential.map_D]
  rw [RingHom.algebraMap_toAlgebra]

/-- The right overlap coordinate maps a differential from the second chart to
the image of its residue coordinate. -/
theorem coordinateOverlapRightKaehlerDifferentialEquiv_map
    (i j : Fin 4) (x : Ω[ChartCoordinateRing j⁄k]) :
    coordinateOverlapRightKaehlerDifferentialEquiv i j
        (coordinateOverlapRightKaehlerDifferentialMap i j x) =
      coordinateChartToRightOverlapRingHom i j
        (chartCoordinateKaehlerDifferentialEquiv j x) := by
  letI : Algebra (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne i))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  haveI : Algebra.FormallyEtale (ChartCoordinateRing j)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne j) (coordinateClass_mem_degreeOne i)))
  letI : IsScalarTower k (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  exact KaehlerDifferential.coordinateEquivOfFormallyEtale_map
    (chartCoordinateKaehlerDifferentialEquiv j) x

/-- The first residue of a normalized ambient-coordinate differential is
the corresponding localized component of the first chart's Jacobian cross. -/
theorem coordinateOverlapLeftKaehlerDifferentialEquiv_D_coordinate
    (i j : Fin 4) (r : Fin 3) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (coordinateOverlapLeftCoordinate i j (i.succAbove r))) =
      coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i
          (chartJacobianCross i r)) := by
  rw [← coordinateChartToLeftOverlapRingHom_affineCoordinate]
  rw [← coordinateOverlapLeftKaehlerDifferentialMap_D]
  rw [coordinateOverlapLeftKaehlerDifferentialEquiv_map]
  rw [chartCoordinateKaehlerDifferentialEquiv_D_affineCoordinate]

/-- The second residue of a normalized ambient-coordinate differential is
the corresponding localized component of the second chart's Jacobian cross. -/
theorem coordinateOverlapRightKaehlerDifferentialEquiv_D_coordinate
    (i j : Fin 4) (r : Fin 3) :
    coordinateOverlapRightKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (coordinateOverlapRightCoordinate i j (j.succAbove r))) =
      coordinateChartToRightOverlapRingHom i j
        (chartCoordinateRingEquivAffine j
          (chartJacobianCross j r)) := by
  rw [← coordinateChartToRightOverlapRingHom_affineCoordinate]
  rw [← coordinateOverlapRightKaehlerDifferentialMap_D]
  rw [coordinateOverlapRightKaehlerDifferentialEquiv_map]
  rw [chartCoordinateKaehlerDifferentialEquiv_D_affineCoordinate]

/-- The left overlap residue of `d(X_j/X_i)` reduces to the corresponding
chart residue before localization. -/
theorem coordinateOverlapLeftKaehlerDifferentialEquiv_D_ratio (i j : Fin 4) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (Away.degreeOneRatio literalConePiece
            (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j))) =
      coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateKaehlerDifferentialEquiv i
          (KaehlerDifferential.D k (ChartCoordinateRing i)
            ((chartCoordinateRingCastEquiv i).symm
              (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
                (coordinateClass_mem_degreeOne j))))) := by
  rw [← coordinateChartToLeftOverlapRingHom_isLocalizationElem]
  rw [← coordinateOverlapLeftKaehlerDifferentialEquiv_map]
  rw [coordinateOverlapLeftKaehlerDifferentialMap_D]

/-- The right overlap residue of `d(X_i/X_j)` reduces to the corresponding
chart residue before localization. -/
theorem coordinateOverlapRightKaehlerDifferentialEquiv_D_ratioInv (i j : Fin 4) :
    coordinateOverlapRightKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (Away.degreeOneRatioInv literalConePiece
            (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j))) =
      coordinateChartToRightOverlapRingHom i j
        (chartCoordinateKaehlerDifferentialEquiv j
          (KaehlerDifferential.D k (ChartCoordinateRing j)
            ((chartCoordinateRingCastEquiv j).symm
              (Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
                (coordinateClass_mem_degreeOne i))))) := by
  rw [← coordinateChartToRightOverlapRingHom_isLocalizationElem]
  rw [← coordinateOverlapRightKaehlerDifferentialEquiv_map]
  rw [coordinateOverlapRightKaehlerDifferentialMap_D]

/-- Away from a self-overlap, the left residue of the ratio differential is
the localized Jacobian minor indexed by the second chart coordinate. -/
theorem coordinateOverlapLeftKaehlerDifferentialEquiv_D_ratio_eq_minor
    (i j : Fin 4) (hji : j ≠ i) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (Away.degreeOneRatio literalConePiece
            (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j))) =
      coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i
          (chartJacobianCross i
            ((finSuccAboveEquiv i).symm ⟨j, hji⟩))) := by
  rw [coordinateOverlapLeftKaehlerDifferentialEquiv_D_ratio]
  exact congrArg (coordinateChartToLeftOverlapRingHom i j)
    (chartCoordinateKaehlerDifferentialEquiv_D_isLocalizationElem i ⟨j, hji⟩)

/-- Away from a self-overlap, the right residue of the reverse-ratio
differential is the localized Jacobian minor indexed by the first chart
coordinate. -/
theorem coordinateOverlapRightKaehlerDifferentialEquiv_D_ratioInv_eq_minor
    (i j : Fin 4) (hij : i ≠ j) :
    coordinateOverlapRightKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (Away.degreeOneRatioInv literalConePiece
            (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j))) =
      coordinateChartToRightOverlapRingHom i j
        (chartCoordinateRingEquivAffine j
          (chartJacobianCross j
            ((finSuccAboveEquiv j).symm ⟨i, hij⟩))) := by
  rw [coordinateOverlapRightKaehlerDifferentialEquiv_D_ratioInv]
  exact congrArg (coordinateChartToRightOverlapRingHom i j)
    (chartCoordinateKaehlerDifferentialEquiv_D_isLocalizationElem j ⟨i, hij⟩)

/-- In characteristic two, the differential of a chart ratio is its square
times the differential of the inverse ratio. -/
theorem coordinateOverlap_D_ratio_eq_sq_smul_D_ratioInv (i j : Fin 4) :
    KaehlerDifferential.D k (coordinateOverlapRing i j)
        (Away.degreeOneRatio literalConePiece
          (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)) =
      (Away.degreeOneRatio literalConePiece
          (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j)) ^ 2 •
        KaehlerDifferential.D k (coordinateOverlapRing i j)
          (Away.degreeOneRatioInv literalConePiece
            (coordinateClass_mem_degreeOne i)
            (coordinateClass_mem_degreeOne j)) := by
  let u := Away.degreeOneRatio literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  let v := Away.degreeOneRatioInv literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  have huv : u * v = 1 :=
    Away.degreeOneRatio_mul_inv literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  have hD := congrArg
    (KaehlerDifferential.D k (coordinateOverlapRing i j)) huv
  rw [Derivation.leibniz, Derivation.map_one_eq_zero] at hD
  have hvu : v • KaehlerDifferential.D k (coordinateOverlapRing i j) u =
      u • KaehlerDifferential.D k (coordinateOverlapRing i j) v := by
    have h := eq_neg_of_add_eq_zero_right hD
    simpa only [ZModModule.neg_eq_self] using h
  change KaehlerDifferential.D k (coordinateOverlapRing i j) u =
    u ^ 2 • KaehlerDifferential.D k (coordinateOverlapRing i j) v
  calc
    KaehlerDifferential.D k (coordinateOverlapRing i j) u =
        (1 : coordinateOverlapRing i j) •
          KaehlerDifferential.D k (coordinateOverlapRing i j) u := by simp
    _ = (u * v) • KaehlerDifferential.D k (coordinateOverlapRing i j) u := by
      rw [huv]
    _ = u • (v • KaehlerDifferential.D k (coordinateOverlapRing i j) u) := by
      rw [mul_smul]
    _ = u • (u • KaehlerDifferential.D k (coordinateOverlapRing i j) v) := by
      rw [hvu]
    _ = u ^ 2 • KaehlerDifferential.D k (coordinateOverlapRing i j) v := by
      rw [pow_two, mul_smul]

/-- On a nontrivial ordered overlap, the two residue evaluations of the
opposite ratio differentials carry the cubic Jacobian transition weight. -/
theorem coordinateOverlapResidues_D_ratios_cubicTransition
    (i j : Fin 4) (hji : j ≠ i) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (Away.degreeOneRatio literalConePiece
            (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j))) =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) ^ 3 *
        coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (Away.degreeOneRatioInv literalConePiece
              (coordinateClass_mem_degreeOne i)
              (coordinateClass_mem_degreeOne j))) := by
  rw [coordinateOverlapLeftKaehlerDifferentialEquiv_D_ratio_eq_minor i j hji,
    coordinateOverlapRightKaehlerDifferentialEquiv_D_ratioInv_eq_minor
      i j hji.symm]
  exact chartJacobianCross_chartTransition i j hji

/-- Combining the cubic Jacobian weight with the inverse-ratio differential
identity leaves the single coordinate-ratio factor predicted by adjunction. -/
theorem coordinateOverlapResidues_D_ratio_linearTransition
    (i j : Fin 4) (hji : j ≠ i) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (Away.degreeOneRatio literalConePiece
            (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j))) =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) *
        coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (Away.degreeOneRatio literalConePiece
              (coordinateClass_mem_degreeOne i)
              (coordinateClass_mem_degreeOne j))) := by
  let u := Away.degreeOneRatio literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  let v := Away.degreeOneRatioInv literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  have hright :
      coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j) u) =
        u ^ 2 * coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j) v) := by
    rw [coordinateOverlap_D_ratio_eq_sq_smul_D_ratioInv]
    rw [map_smul, smul_eq_mul]
  change coordinateOverlapLeftKaehlerDifferentialEquiv i j
      (KaehlerDifferential.D k (coordinateOverlapRing i j) u) =
    u * coordinateOverlapRightKaehlerDifferentialEquiv i j
      (KaehlerDifferential.D k (coordinateOverlapRing i j) u)
  rw [coordinateOverlapResidues_D_ratios_cubicTransition i j hji]
  change u ^ 3 * coordinateOverlapRightKaehlerDifferentialEquiv i j
      (KaehlerDifferential.D k (coordinateOverlapRing i j) v) =
    u * coordinateOverlapRightKaehlerDifferentialEquiv i j
      (KaehlerDifferential.D k (coordinateOverlapRing i j) u)
  rw [hright]
  ring

/-- For four distinct ambient labels, the cubic minor transition and Euler
syzygy reduce the residue transition of a coordinate differential to weight
one. -/
theorem coordinateOverlapResidues_D_coordinate_linearTransition_of_distinct
    (i j t l : Fin 4)
    (hji : j ≠ i) (hit : i ≠ t) (hil : i ≠ l)
    (hjt : j ≠ t) (hjl : j ≠ l) (htl : t ≠ l)
    (r : Fin 3) (hrt : i.succAbove r = t) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (coordinateOverlapLeftCoordinate i j t)) =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) *
        coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (coordinateOverlapLeftCoordinate i j t)) := by
  let u := Away.degreeOneRatio literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  let v := Away.degreeOneRatioInv literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  let w := coordinateOverlapRightCoordinate i j t
  let rt : Fin 3 := (finSuccAboveEquiv j).symm ⟨t, hjt.symm⟩
  let ri : Fin 3 := (finSuccAboveEquiv j).symm ⟨i, hji.symm⟩
  have hunit : (coordinateRatioUnit i j : coordinateOverlapRing i j) = u := by
    rfl
  have hjrt : j.succAbove rt = t := by
    exact congrArg Subtype.val
      ((finSuccAboveEquiv j).apply_symm_apply ⟨t, hjt.symm⟩)
  have hjri : j.succAbove ri = i := by
    exact congrArg Subtype.val
      ((finSuccAboveEquiv j).apply_symm_apply ⟨i, hji.symm⟩)
  have hleft :
      coordinateOverlapLeftKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (coordinateOverlapLeftCoordinate i j t)) =
        u ^ 3 * coordinateOverlapRightMinor i j j l := by
    rw [← hrt, coordinateOverlapLeftKaehlerDifferentialEquiv_D_coordinate]
    rw [chartJacobianCross_eq_chartMap_minor_of_complement
      i r j l hji hil.symm (by simpa only [hrt] using hjt)
        (by simpa only [hrt] using htl.symm) hjl]
    exact coordinateOverlapMinor_transition i j j l
  have hright_w :
      coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j) w) =
        coordinateOverlapRightMinor i j i l := by
    rw [show w = coordinateOverlapRightCoordinate i j (j.succAbove rt) by
      rw [hjrt]]
    rw [coordinateOverlapRightKaehlerDifferentialEquiv_D_coordinate]
    rw [chartJacobianCross_eq_chartMap_minor_of_complement
      j rt i l hji.symm hjl.symm (by simpa [hjrt] using hit)
        (by simpa [hjrt] using htl.symm) hil]
    rfl
  have hright_v :
      coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j) v) =
        coordinateOverlapRightMinor i j t l := by
    rw [show v = coordinateOverlapRightCoordinate i j (j.succAbove ri) by
      rw [hjri, coordinateOverlapRightCoordinate_first]]
    rw [coordinateOverlapRightKaehlerDifferentialEquiv_D_coordinate]
    rw [chartJacobianCross_eq_chartMap_minor_of_complement
      j ri t l hjt.symm hjl.symm (by simpa [hjri] using hit.symm)
        (by simpa [hjri] using hil.symm) htl]
    rfl
  have hright_u :
      coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j) u) =
        u ^ 2 * coordinateOverlapRightMinor i j t l := by
    rw [coordinateOverlap_D_ratio_eq_sq_smul_D_ratioInv]
    rw [map_smul, smul_eq_mul, hright_v]
  have hright :
      coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (coordinateOverlapLeftCoordinate i j t)) =
        u * coordinateOverlapRightMinor i j i l +
          w * u ^ 2 * coordinateOverlapRightMinor i j t l := by
    rw [coordinateOverlapCoordinate_transition, hunit]
    rw [Derivation.leibniz, map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, hright_w, hright_u]
    change u * coordinateOverlapRightMinor i j i l +
        w * (u ^ 2 * coordinateOverlapRightMinor i j t l) = _
    ring
  have heuler :
      coordinateOverlapRightMinor i j j l =
        v * coordinateOverlapRightMinor i j i l +
          w * coordinateOverlapRightMinor i j t l := by
    simpa only [coordinateOverlapRightCoordinate_first] using
      coordinateOverlapRight_minor_euler_three i j t l hji.symm hit hil hjt hjl htl
  have huv : u * v = 1 :=
    Away.degreeOneRatio_mul_inv literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  have hcube : u ^ 3 * v = u ^ 2 := by
    calc
      u ^ 3 * v = u ^ 2 * (u * v) := by ring
      _ = u ^ 2 := by rw [huv, mul_one]
  rw [hunit]
  change coordinateOverlapLeftKaehlerDifferentialEquiv i j
      (KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateOverlapLeftCoordinate i j t)) =
    u * coordinateOverlapRightKaehlerDifferentialEquiv i j
      (KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateOverlapLeftCoordinate i j t))
  rw [hleft, hright, heuler]
  rw [mul_add, ← mul_assoc, hcube]
  ring

/-- Every affine-coordinate differential on a nontrivial first chart overlap
has the adjunction transition weight `X_j/X_i`. -/
theorem coordinateOverlapResidues_D_coordinate_linearTransition
    (i j : Fin 4) (hji : j ≠ i) (r : Fin 3) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (KaehlerDifferential.D k (coordinateOverlapRing i j)
          (coordinateOverlapLeftCoordinate i j (i.succAbove r))) =
      (coordinateRatioUnit i j : coordinateOverlapRing i j) *
        coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (coordinateOverlapLeftCoordinate i j (i.succAbove r))) := by
  by_cases hjt : j = i.succAbove r
  · rw [← hjt, coordinateOverlapLeftCoordinate_second]
    exact coordinateOverlapResidues_D_ratio_linearTransition i j hji
  · let t := i.succAbove r
    let a := i.succAbove (r.succAbove (0 : Fin 2))
    let b := i.succAbove (r.succAbove (1 : Fin 2))
    have hit : i ≠ t := (i.succAbove_ne r).symm
    have hai : a ≠ i := i.succAbove_ne _
    have hbi : b ≠ i := i.succAbove_ne _
    have hat : a ≠ t := by
      intro h
      apply r.succAbove_ne 0
      exact i.succAbove_right_injective h
    have hbt : b ≠ t := by
      intro h
      apply r.succAbove_ne 1
      exact i.succAbove_right_injective h
    have hab : a ≠ b := by
      intro h
      have h' := i.succAbove_right_injective h
      have h'' := r.succAbove_right_injective h'
      norm_num at h''
    have hjab : j = a ∨ j = b := by
      omega
    rcases hjab with hja | hjb
    · subst j
      exact coordinateOverlapResidues_D_coordinate_linearTransition_of_distinct
        i a t b hai hit hbi.symm hat hab hbt.symm r rfl
    · subst j
      exact coordinateOverlapResidues_D_coordinate_linearTransition_of_distinct
        i b t a hbi hit hai.symm hbt hab.symm hat.symm r rfl

/-! ## A nonvanishing overlap generator -/

/-- The Bezout-normalized differential on the ordered overlap.  Its three
terms avoid choosing a nonvanishing Jacobian minor. -/
def coordinateOverlapLeftBezoutDifferential (i j : Fin 4) :
    Ω[coordinateOverlapRing i j⁄k] :=
  ∑ r : Fin 3,
    coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateRingEquivAffine i
          (chartJacobianBezoutVector i r)) •
      KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateOverlapLeftCoordinate i j (i.succAbove r))

/-- The first residue coordinate sends the localized Bezout differential to
one; in particular this differential is a genuine basis generator. -/
theorem coordinateOverlapLeftKaehlerDifferentialEquiv_bezoutDifferential
    (i j : Fin 4) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (coordinateOverlapLeftBezoutDifferential i j) = 1 := by
  have hdot := congrArg
    ((coordinateChartToLeftOverlapRingHom i j).comp
      (chartCoordinateRingEquivAffine i).toRingHom)
    (chartJacobianBezoutVector_dot i)
  simp only [dotProduct, map_sum, map_mul, map_one] at hdot
  rw [coordinateOverlapLeftBezoutDifferential, map_sum]
  simp_rw [map_smul, smul_eq_mul,
    coordinateOverlapLeftKaehlerDifferentialEquiv_D_coordinate]
  exact hdot

/-- On a nontrivial overlap, the second residue of the first chart's
Bezout-normalized differential is the inverse coordinate ratio. -/
theorem coordinateOverlapRightKaehlerDifferentialEquiv_bezoutDifferential
    (i j : Fin 4) (hji : j ≠ i) :
    coordinateOverlapRightKaehlerDifferentialEquiv i j
        (coordinateOverlapLeftBezoutDifferential i j) =
      Away.degreeOneRatioInv literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) := by
  let u := Away.degreeOneRatio literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  let v := Away.degreeOneRatioInv literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  have huv : u * v = 1 :=
    Away.degreeOneRatio_mul_inv literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  have hvu : v * u = 1 := by
    calc
      v * u = u * v := mul_comm _ _
      _ = 1 := huv
  have hright_coordinate (r : Fin 3) :
      coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (coordinateOverlapLeftCoordinate i j (i.succAbove r))) =
        v * coordinateChartToLeftOverlapRingHom i j
          (chartCoordinateRingEquivAffine i (chartJacobianCross i r)) := by
    have htransition :=
      coordinateOverlapResidues_D_coordinate_linearTransition i j hji r
    have hunit : (coordinateRatioUnit i j : coordinateOverlapRing i j) = u := by
      rfl
    rw [hunit] at htransition
    calc
      coordinateOverlapRightKaehlerDifferentialEquiv i j
          (KaehlerDifferential.D k (coordinateOverlapRing i j)
            (coordinateOverlapLeftCoordinate i j (i.succAbove r))) =
          1 * coordinateOverlapRightKaehlerDifferentialEquiv i j
            (KaehlerDifferential.D k (coordinateOverlapRing i j)
              (coordinateOverlapLeftCoordinate i j (i.succAbove r))) := by
            rw [one_mul]
      _ = (v * u) * coordinateOverlapRightKaehlerDifferentialEquiv i j
            (KaehlerDifferential.D k (coordinateOverlapRing i j)
              (coordinateOverlapLeftCoordinate i j (i.succAbove r))) := by
            rw [hvu]
      _ = v * (u * coordinateOverlapRightKaehlerDifferentialEquiv i j
            (KaehlerDifferential.D k (coordinateOverlapRing i j)
              (coordinateOverlapLeftCoordinate i j (i.succAbove r)))) := by ring
      _ = v * coordinateOverlapLeftKaehlerDifferentialEquiv i j
            (KaehlerDifferential.D k (coordinateOverlapRing i j)
              (coordinateOverlapLeftCoordinate i j (i.succAbove r))) := by
            rw [htransition]
      _ = v * coordinateChartToLeftOverlapRingHom i j
            (chartCoordinateRingEquivAffine i
              (chartJacobianCross i r)) := by
            rw [coordinateOverlapLeftKaehlerDifferentialEquiv_D_coordinate]
  have hdot := congrArg
    ((coordinateChartToLeftOverlapRingHom i j).comp
      (chartCoordinateRingEquivAffine i).toRingHom)
    (chartJacobianBezoutVector_dot i)
  simp only [dotProduct, map_sum, map_mul, map_one] at hdot
  change (∑ r : Fin 3,
      coordinateChartToLeftOverlapRingHom i j
          (chartCoordinateRingEquivAffine i
            (chartJacobianBezoutVector i r)) *
        coordinateChartToLeftOverlapRingHom i j
          (chartCoordinateRingEquivAffine i (chartJacobianCross i r))) = 1 at hdot
  change coordinateOverlapRightKaehlerDifferentialEquiv i j
      (coordinateOverlapLeftBezoutDifferential i j) = v
  rw [coordinateOverlapLeftBezoutDifferential, map_sum]
  simp_rw [map_smul, smul_eq_mul, hright_coordinate]
  calc
    ∑ r : Fin 3,
        coordinateChartToLeftOverlapRingHom i j
            (chartCoordinateRingEquivAffine i
              (chartJacobianBezoutVector i r)) *
          (v * coordinateChartToLeftOverlapRingHom i j
            (chartCoordinateRingEquivAffine i (chartJacobianCross i r))) =
        v * ∑ r : Fin 3,
          coordinateChartToLeftOverlapRingHom i j
              (chartCoordinateRingEquivAffine i
                (chartJacobianBezoutVector i r)) *
            coordinateChartToLeftOverlapRingHom i j
              (chartCoordinateRingEquivAffine i (chartJacobianCross i r)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = v * 1 := by rw [hdot]
    _ = v := by rw [mul_one]

/-- The two residue coordinates coincide when both sides use the same
projective chart. -/
theorem coordinateOverlapKaehlerDifferentialEquiv_self (i : Fin 4) :
    coordinateOverlapRightKaehlerDifferentialEquiv i i =
      coordinateOverlapLeftKaehlerDifferentialEquiv i i := by
  unfold coordinateOverlapRightKaehlerDifferentialEquiv
  unfold coordinateOverlapLeftKaehlerDifferentialEquiv
  rfl

/-! ## The remaining overlap unit -/

/-- Change from the residue coordinate induced by the first chart to the
residue coordinate induced by the second chart. -/
def coordinateOverlapResidueTransition (i j : Fin 4) :
    coordinateOverlapRing i j ≃ₗ[coordinateOverlapRing i j]
      coordinateOverlapRing i j :=
  (coordinateOverlapLeftKaehlerDifferentialEquiv i j).symm.trans
    (coordinateOverlapRightKaehlerDifferentialEquiv i j)

/-- A chart's residue coordinate has the identity transition to itself. -/
theorem coordinateOverlapResidueTransition_self (i : Fin 4) :
    coordinateOverlapResidueTransition i i = LinearEquiv.refl _ _ := by
  rw [coordinateOverlapResidueTransition,
    coordinateOverlapKaehlerDifferentialEquiv_self]
  exact LinearEquiv.symm_trans_self _

/-- The scalar that remains to be identified with the adjunction coordinate
ratio is the image of one under the residue-coordinate transition. -/
def coordinateOverlapResidueScalar (i j : Fin 4) :
    coordinateOverlapRing i j :=
  coordinateOverlapResidueTransition i j 1

@[simp]
theorem coordinateOverlapResidueScalar_self (i : Fin 4) :
    coordinateOverlapResidueScalar i i = 1 := by
  rw [coordinateOverlapResidueScalar,
    coordinateOverlapResidueTransition_self]
  rfl

/-- The transition scalar is the second residue of the first chart's Bezout
generator.  This replaces cancellation of a single possibly vanishing minor
by evaluation on a certified unit-residue differential. -/
theorem coordinateOverlapResidueScalar_eq_right_bezoutDifferential
    (i j : Fin 4) :
    coordinateOverlapResidueScalar i j =
      coordinateOverlapRightKaehlerDifferentialEquiv i j
        (coordinateOverlapLeftBezoutDifferential i j) := by
  have hgenerator :
      (coordinateOverlapLeftKaehlerDifferentialEquiv i j).symm 1 =
        coordinateOverlapLeftBezoutDifferential i j := by
    apply (coordinateOverlapLeftKaehlerDifferentialEquiv i j).injective
    rw [(coordinateOverlapLeftKaehlerDifferentialEquiv i j).apply_symm_apply]
    exact (coordinateOverlapLeftKaehlerDifferentialEquiv_bezoutDifferential i j).symm
  rw [coordinateOverlapResidueScalar, coordinateOverlapResidueTransition,
    LinearEquiv.trans_apply, hgenerator]

/-- On a nontrivial ordered overlap, changing from the first residue
coordinate to the second multiplies by `X_i/X_j`. -/
theorem coordinateOverlapResidueScalar_eq_ratioInv
    (i j : Fin 4) (hji : j ≠ i) :
    coordinateOverlapResidueScalar i j =
      Away.degreeOneRatioInv literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) := by
  rw [coordinateOverlapResidueScalar_eq_right_bezoutDifferential]
  exact coordinateOverlapRightKaehlerDifferentialEquiv_bezoutDifferential
    i j hji

/-- Since the overlap module has rank one, the full residue transition is
multiplication by its value at one. -/
theorem coordinateOverlapResidueTransition_apply (i j : Fin 4)
    (x : coordinateOverlapRing i j) :
    coordinateOverlapResidueTransition i j x =
      x * coordinateOverlapResidueScalar i j := by
  calc
    coordinateOverlapResidueTransition i j x =
        coordinateOverlapResidueTransition i j
          (x • (1 : coordinateOverlapRing i j)) := by
      rw [smul_eq_mul, mul_one]
    _ = x • coordinateOverlapResidueTransition i j 1 := by
      rw [map_smul]
    _ = x * coordinateOverlapResidueScalar i j := by
      rfl

/-- The residue transition scalar is a unit because it comes from a linear
automorphism of the rank-one overlap module. -/
def coordinateOverlapResidueUnit (i j : Fin 4) :
    (coordinateOverlapRing i j)ˣ where
  val := coordinateOverlapResidueScalar i j
  inv := (coordinateOverlapResidueTransition i j).symm 1
  val_inv := by
    rw [mul_comm]
    rw [← coordinateOverlapResidueTransition_apply]
    exact (coordinateOverlapResidueTransition i j).apply_symm_apply 1
  inv_val := by
    rw [← coordinateOverlapResidueTransition_apply]
    exact (coordinateOverlapResidueTransition i j).apply_symm_apply 1

@[simp]
theorem coordinateOverlapResidueUnit_self (i : Fin 4) :
    coordinateOverlapResidueUnit i i = 1 := by
  apply Units.ext
  exact coordinateOverlapResidueScalar_self i

/-- Away from self-overlaps, the residue-coordinate transition is the
inverse of the projective coordinate-ratio transition. -/
theorem coordinateOverlapResidueUnit_eq_inv_coordinateRatioUnit_of_ne
    (i j : Fin 4) (hji : j ≠ i) :
    coordinateOverlapResidueUnit i j = (coordinateRatioUnit i j)⁻¹ := by
  apply Units.ext
  change coordinateOverlapResidueScalar i j =
    Away.degreeOneRatioInv literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
  exact coordinateOverlapResidueScalar_eq_ratioInv i j hji

/-- On every ordered coordinate overlap, the residue transition realizes the
inverse degree-one projective transition predicted by adjunction. -/
theorem coordinateOverlapResidueUnit_eq_inv_coordinateRatioUnit
    (i j : Fin 4) :
    coordinateOverlapResidueUnit i j = (coordinateRatioUnit i j)⁻¹ := by
  by_cases hji : j = i
  · subst j
    rw [coordinateOverlapResidueUnit_self, coordinateRatioUnit_self, inv_one]
  · exact coordinateOverlapResidueUnit_eq_inv_coordinateRatioUnit_of_ne
      i j hji

/-- The full residue-coordinate transition is the integral twist transition
of exponent `-1`, not merely multiplication by an abstract unit. -/
theorem coordinateOverlapResidueTransition_eq_ratioPowerTransition
    (i j : Fin 4) :
    coordinateOverlapResidueTransition i j =
      Away.ratioPowerTransition literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) (-1) := by
  apply LinearEquiv.ext
  intro x
  rw [coordinateOverlapResidueTransition_apply]
  change x * (coordinateOverlapResidueUnit i j : coordinateOverlapRing i j) = _
  rw [coordinateOverlapResidueUnit_eq_inv_coordinateRatioUnit]
  simp only [Away.ratioPowerTransition, zpow_neg_one]
  change x * (↑((coordinateRatioUnit i j)⁻¹) : coordinateOverlapRing i j) =
    (↑((coordinateRatioUnit i j)⁻¹) : coordinateOverlapRing i j) * x
  rw [mul_comm]

end MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
