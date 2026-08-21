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

/-- The residue coordinate from the first chart, localized to an ordered
pair overlap. -/
def coordinateOverlapLeftKaehlerDifferentialEquiv (i j : Fin 4) :
    Ω[coordinateOverlapRing i j⁄k] ≃ₗ[coordinateOverlapRing i j]
      coordinateOverlapRing i j := by
  letI : Algebra (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    (coordinateChartToLeftOverlapRingHom i j).toAlgebra
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

/-! ## The remaining overlap unit -/

/-- Change from the residue coordinate induced by the first chart to the
residue coordinate induced by the second chart. -/
def coordinateOverlapResidueTransition (i j : Fin 4) :
    coordinateOverlapRing i j ≃ₗ[coordinateOverlapRing i j]
      coordinateOverlapRing i j :=
  (coordinateOverlapLeftKaehlerDifferentialEquiv i j).symm.trans
    (coordinateOverlapRightKaehlerDifferentialEquiv i j)

/-- The scalar that remains to be identified with the adjunction coordinate
ratio is the image of one under the residue-coordinate transition. -/
def coordinateOverlapResidueScalar (i j : Fin 4) :
    coordinateOverlapRing i j :=
  coordinateOverlapResidueTransition i j 1

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

end MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
