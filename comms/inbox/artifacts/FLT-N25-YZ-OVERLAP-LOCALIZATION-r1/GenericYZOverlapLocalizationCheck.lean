import Mathlib.RingTheory.Localization.Away.Basic
import ZChartFractionEquivCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
abbrev YChartRing := ChartQuotient (1 : Fin 4)

def yZ : YChartRing := chartMap 1 (MvPolynomial.X 2)


def yzW : YChartRing := chartMap 1 (MvPolynomial.X 3)

end MazurProof.RationalPointsN25QuotientTwoWBoundaryYZChartArtin

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
open N25F_ZChartWChartEquiv

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

variable {L : Type*} [CommRing L] [Algebra (ZMod 2) L] [Algebra YChartRing L]
  [IsScalarTower (ZMod 2) YChartRing L] [Fact (IsUnit (algebraMap YChartRing L yZ))]

/-- The unit realizing the actual germ of Z/Y. -/
def yzZUnit : Lˣ := (show IsUnit (algebraMap YChartRing L yZ) from Fact.out).unit

@[simp]
theorem yzZUnit_val : ((yzZUnit (L := L)) : L) = (algebraMap YChartRing L yZ) := (show IsUnit (algebraMap YChartRing L yZ) from Fact.out).unit_spec

/-- The actual local Y-chart point, normalized at its invertible Z coordinate. -/
def yzZPoint : Coordinates4 L :=
  scaleCoordinates4 (↑(yzZUnit (L := L))⁻¹ : L)
    (mapCoordinates4 (algebraMap YChartRing L) (chartQuotientPoint 1))

@[simp]
theorem yzZPoint_z : (yzZPoint (L := L)).z = 1 := by
  rw [yzZPoint, yChartPoint_eq]
  change (↑(yzZUnit (L := L))⁻¹ : L) * (algebraMap YChartRing L yZ) = 1
  exact Units.inv_mul_of_eq (yzZUnit_val (L := L))

private theorem yzZPoint_quadric : canonicalQuadric25CharTwo (yzZPoint (L := L)) = 0 := by
  rw [yzZPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem yzZPoint_cubic : canonicalCubic25CharTwo (yzZPoint (L := L)) = 0 := by
  rw [yzZPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

/-- The coordinate-rigid Z-chart map into the existing YZ-boundary local ring. -/
def zChartToYZLocal : ZChartRing →ₐ[ZMod 2] L :=
  chartPointEval 2 (yzZPoint (L := L))
    (by simpa [coordinates4ToFun] using (yzZPoint_z (L := L)))
    (yzZPoint_quadric (L := L)) (yzZPoint_cubic (L := L))

@[simp]
theorem zChartToYZLocal_zX :
    (zChartToYZLocal (L := L)) zX =
      (↑(yzZUnit (L := L))⁻¹ : L) * algebraMap YChartRing L yX := by
  rw [zChartToYZLocal, zX, chartPointEval_chartMap_X, yzZPoint, yChartPoint_eq]
  rfl

@[simp]
theorem zChartToYZLocal_zY :
    (zChartToYZLocal (L := L)) zY = (↑(yzZUnit (L := L))⁻¹ : L) := by
  rw [zChartToYZLocal, zY, chartPointEval_chartMap_X, yzZPoint, yChartPoint_eq]
  change (↑(yzZUnit (L := L))⁻¹ : L) * algebraMap YChartRing L 1 = _
  rw [map_one, mul_one]

@[simp]
theorem zChartToYZLocal_zW :
    (zChartToYZLocal (L := L)) zW = (↑(yzZUnit (L := L))⁻¹ : L) * (algebraMap YChartRing L yzW) := by
  rw [zChartToYZLocal, zW, chartPointEval_chartMap_X, yzZPoint, yChartPoint_eq]
  rfl

/-- The overlap map sends Y/Z to the inverse unit of the actual germ Z/Y. -/
theorem zChartToYZLocal_zY_isUnit : IsUnit ((zChartToYZLocal (L := L)) zY) := by
  rw [(zChartToYZLocal_zY (L := L))]
  exact Units.isUnit _

end MazurProof.N25F_YZOverlapMap

#check @MazurProof.N25F_YZOverlapMap.yzZUnit
#print axioms MazurProof.N25F_YZOverlapMap.yzZUnit
#check @MazurProof.N25F_YZOverlapMap.yzZUnit_val
#print axioms MazurProof.N25F_YZOverlapMap.yzZUnit_val
#check @MazurProof.N25F_YZOverlapMap.yzZPoint_z
#print axioms MazurProof.N25F_YZOverlapMap.yzZPoint_z
#check @MazurProof.N25F_YZOverlapMap.zChartToYZLocal
#print axioms MazurProof.N25F_YZOverlapMap.zChartToYZLocal
#check @MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zX
#print axioms MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zX
#check @MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zY
#print axioms MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zY
#check @MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zW
#print axioms MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zW
#check @MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zY_isUnit
#print axioms MazurProof.N25F_YZOverlapMap.zChartToYZLocal_zY_isUnit

namespace MazurProof.N25F_YZOverlapLocalization

open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open N25F_ZChartWChartEquiv N25F_YZOverlapMap

variable {L : Type*} [CommRing L] [Algebra (ZMod 2) L] [Algebra YChartRing L]
  [IsScalarTower (ZMod 2) YChartRing L] [Fact (IsUnit (algebraMap YChartRing L yZ))]

private theorem zChartToYZLocal_isUnit_of_powers (s : Submonoid.powers zY) :
    IsUnit ((zChartToYZLocal (L := L)) (s : ZChartRing) : L) := by
  obtain ⟨n, hn⟩ := s.2
  rw [← hn, map_pow]
  exact (zChartToYZLocal_zY_isUnit (L := L)).pow n

/-- The actual Z-chart Y-nonzero overlap maps to the existing YZ local ring. -/
def zYOpenToYZLocal : Localization.Away zY →ₐ[ZMod 2] L :=
  IsLocalization.liftAlgHom
    (A := ZMod 2) (R := ZChartRing) (S := Localization.Away zY)
    (P := L) (M := Submonoid.powers zY) (f := (zChartToYZLocal (L := L)))
    (zChartToYZLocal_isUnit_of_powers (L := L))

@[simp]
theorem zYOpenToYZLocal_algebraMap (a : ZChartRing) :
    (zYOpenToYZLocal (L := L)) (algebraMap ZChartRing (Localization.Away zY) a) =
      ((zChartToYZLocal (L := L)) a : L) := by
  exact IsLocalization.lift_eq (zChartToYZLocal_isUnit_of_powers (L := L)) a

/-- The inverted Y/Z coordinate maps to the actual local germ Z/Y. -/
theorem zYOpenToYZLocal_invSelf :
    (zYOpenToYZLocal (L := L)) (IsLocalization.Away.invSelf zY : Localization.Away zY) =
      algebraMap YChartRing L yZ := by
  have h := congrArg (zYOpenToYZLocal (L := L))
    (IsLocalization.Away.mul_invSelf zY (S := Localization.Away zY))
  rw [map_mul, map_one, (zYOpenToYZLocal_algebraMap (L := L)), (zChartToYZLocal_zY (L := L))] at h
  simpa using (Units.inv_mul_eq_iff_eq_mul (yzZUnit (L := L))).1 h

end MazurProof.N25F_YZOverlapLocalization

#check @MazurProof.N25F_YZOverlapLocalization.zYOpenToYZLocal
#print axioms MazurProof.N25F_YZOverlapLocalization.zYOpenToYZLocal
#check @MazurProof.N25F_YZOverlapLocalization.zYOpenToYZLocal_algebraMap
#print axioms MazurProof.N25F_YZOverlapLocalization.zYOpenToYZLocal_algebraMap
#check @MazurProof.N25F_YZOverlapLocalization.zYOpenToYZLocal_invSelf
#print axioms MazurProof.N25F_YZOverlapLocalization.zYOpenToYZLocal_invSelf
