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
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingTransition
open HomogeneousLocalization

/-- The canonical chart ring and the overlap chart ring use propositionally
equal homogeneous denominators.  This cast records that equality explicitly. -/
def chartCoordinateRingCastEquiv (i : Fin 4) :
    ChartCoordinateRing i ≃+* coordinateChartRing i :=
  RingEquiv.cast (R := fun f : CanonicalConeRing25Two ↦ Away literalConePiece f)
    (show canonicalConeGradedProjection (MvPolynomial.X i) = coordinateClass i by rfl)

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

/-- The residue coordinate from the first chart, localized to an ordered
pair overlap. -/
def coordinateOverlapLeftKaehlerDifferentialEquiv (i j : Fin 4) :
    Ω[coordinateOverlapRing i j⁄k] ≃ₗ[coordinateOverlapRing i j]
      coordinateOverlapRing i j := by
  letI : Algebra (ChartCoordinateRing i) (coordinateChartRing i) :=
    (chartCoordinateRingCastEquiv i).toRingHom.toAlgebra
  letI : Algebra (coordinateChartRing i) (coordinateOverlapRing i j) :=
    (awayMap literalConePiece (f := coordinateClass i)
      (coordinateClass_mem_degreeOne j) rfl).toAlgebra
  letI : Algebra (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : IsScalarTower (ChartCoordinateRing i) (coordinateChartRing i)
      (coordinateOverlapRing i j) := IsScalarTower.of_algebraMap_eq' rfl
  let e : ChartCoordinateRing i ≃ₐ[ChartCoordinateRing i] coordinateChartRing i :=
    { toRingEquiv := chartCoordinateRingCastEquiv i
      commutes' _ := rfl }
  haveI : Algebra.FormallyEtale (ChartCoordinateRing i) (coordinateChartRing i) :=
    Algebra.FormallyEtale.of_equiv e
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  haveI : Algebra.FormallyEtale (coordinateChartRing i)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)))
  haveI : Algebra.FormallyEtale (ChartCoordinateRing i)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.comp
      (ChartCoordinateRing i) (coordinateChartRing i) (coordinateOverlapRing i j)
  letI : IsScalarTower k (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact KaehlerDifferential.coordinateEquivOfFormallyEtale
    (chartCoordinateKaehlerDifferentialEquiv i)

/-- The residue coordinate from the second chart, localized to the same
ordered pair overlap. -/
def coordinateOverlapRightKaehlerDifferentialEquiv (i j : Fin 4) :
    Ω[coordinateOverlapRing i j⁄k] ≃ₗ[coordinateOverlapRing i j]
      coordinateOverlapRing i j := by
  letI : Algebra (ChartCoordinateRing j) (coordinateChartRing j) :=
    (chartCoordinateRingCastEquiv j).toRingHom.toAlgebra
  letI : Algebra (coordinateChartRing j) (coordinateOverlapRing i j) :=
    (awayMap literalConePiece (f := coordinateClass j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _)).toAlgebra
  letI : Algebra (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : IsScalarTower (ChartCoordinateRing j) (coordinateChartRing j)
      (coordinateOverlapRing i j) := IsScalarTower.of_algebraMap_eq' rfl
  let e : ChartCoordinateRing j ≃ₐ[ChartCoordinateRing j] coordinateChartRing j :=
    { toRingEquiv := chartCoordinateRingCastEquiv j
      commutes' _ := rfl }
  haveI : Algebra.FormallyEtale (ChartCoordinateRing j) (coordinateChartRing j) :=
    Algebra.FormallyEtale.of_equiv e
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne i))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  haveI : Algebra.FormallyEtale (coordinateChartRing j)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne j) (coordinateClass_mem_degreeOne i)))
  haveI : Algebra.FormallyEtale (ChartCoordinateRing j)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.comp
      (ChartCoordinateRing j) (coordinateChartRing j) (coordinateOverlapRing i j)
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

/-- The left overlap coordinate maps a differential from the first chart to
the image of its residue coordinate. -/
theorem coordinateOverlapLeftKaehlerDifferentialEquiv_map
    (i j : Fin 4) (x : Ω[ChartCoordinateRing i⁄k]) :
    coordinateOverlapLeftKaehlerDifferentialEquiv i j
        (coordinateOverlapLeftKaehlerDifferentialMap i j x) =
      coordinateChartToLeftOverlapRingHom i j
        (chartCoordinateKaehlerDifferentialEquiv i x) := by
  letI : Algebra (ChartCoordinateRing i) (coordinateChartRing i) :=
    (chartCoordinateRingCastEquiv i).toRingHom.toAlgebra
  letI : Algebra (coordinateChartRing i) (coordinateOverlapRing i j) :=
    (awayMap literalConePiece (f := coordinateClass i)
      (coordinateClass_mem_degreeOne j) rfl).toAlgebra
  letI : Algebra (ChartCoordinateRing i) (coordinateOverlapRing i j) :=
    (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : IsScalarTower (ChartCoordinateRing i) (coordinateChartRing i)
      (coordinateOverlapRing i j) := IsScalarTower.of_algebraMap_eq' rfl
  let e : ChartCoordinateRing i ≃ₐ[ChartCoordinateRing i] coordinateChartRing i :=
    { toRingEquiv := chartCoordinateRingCastEquiv i
      commutes' _ := rfl }
  haveI : Algebra.FormallyEtale (ChartCoordinateRing i) (coordinateChartRing i) :=
    Algebra.FormallyEtale.of_equiv e
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  haveI : Algebra.FormallyEtale (coordinateChartRing i)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)))
  haveI : Algebra.FormallyEtale (ChartCoordinateRing i)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.comp
      (ChartCoordinateRing i) (coordinateChartRing i) (coordinateOverlapRing i j)
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

/-- The right overlap coordinate maps a differential from the second chart to
the image of its residue coordinate. -/
theorem coordinateOverlapRightKaehlerDifferentialEquiv_map
    (i j : Fin 4) (x : Ω[ChartCoordinateRing j⁄k]) :
    coordinateOverlapRightKaehlerDifferentialEquiv i j
        (coordinateOverlapRightKaehlerDifferentialMap i j x) =
      coordinateChartToRightOverlapRingHom i j
        (chartCoordinateKaehlerDifferentialEquiv j x) := by
  letI : Algebra (ChartCoordinateRing j) (coordinateChartRing j) :=
    (chartCoordinateRingCastEquiv j).toRingHom.toAlgebra
  letI : Algebra (coordinateChartRing j) (coordinateOverlapRing i j) :=
    (awayMap literalConePiece (f := coordinateClass j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _)).toAlgebra
  letI : Algebra (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : IsScalarTower (ChartCoordinateRing j) (coordinateChartRing j)
      (coordinateOverlapRing i j) := IsScalarTower.of_algebraMap_eq' rfl
  let e : ChartCoordinateRing j ≃ₐ[ChartCoordinateRing j] coordinateChartRing j :=
    { toRingEquiv := chartCoordinateRingCastEquiv j
      commutes' _ := rfl }
  haveI : Algebra.FormallyEtale (ChartCoordinateRing j) (coordinateChartRing j) :=
    Algebra.FormallyEtale.of_equiv e
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne i))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  haveI : Algebra.FormallyEtale (coordinateChartRing j)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne j) (coordinateClass_mem_degreeOne i)))
  haveI : Algebra.FormallyEtale (ChartCoordinateRing j)
      (coordinateOverlapRing i j) :=
    Algebra.FormallyEtale.comp
      (ChartCoordinateRing j) (coordinateChartRing j) (coordinateOverlapRing i j)
  letI : IsScalarTower k (ChartCoordinateRing j) (coordinateOverlapRing i j) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  exact KaehlerDifferential.coordinateEquivOfFormallyEtale_map
    (chartCoordinateKaehlerDifferentialEquiv j) x

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
