import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientF2


structure Coordinates4 (R : Type*) where
  x : R
  y : R
  z : R
  w : R
deriving DecidableEq, Fintype

end MazurProof.RationalPointsN25QuotientF2

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

def canonicalQuadric25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : K :=
  P.x * P.z + P.x * P.w + P.y ^ 2 + P.y * P.z + P.z * P.w

def canonicalCubic25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : K :=
  P.x ^ 2 * P.w + P.x * P.y * P.z + P.x * P.y * P.w +
    P.x * P.z * P.w + P.y * P.z * P.w + P.z ^ 2 * P.w +
    P.z * P.w ^ 2

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientTwoConormal

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2

abbrev BinaryHomogeneousRing := MvPolynomial (Fin 4) (ZMod 2)

def canonicalQuadricPolynomial25Two : BinaryHomogeneousRing :=
  MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.X 0 * MvPolynomial.X 3 +
    MvPolynomial.X 1 ^ 2 +
    MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 2 * MvPolynomial.X 3

def canonicalCubicPolynomial25Two : BinaryHomogeneousRing :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
    MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 2 ^ 2 * MvPolynomial.X 3 +
    MvPolynomial.X 2 * MvPolynomial.X 3 ^ 2

def coordinates4ToFun {K : Type*} (P : Coordinates4 K) : Fin 4 → K :=
  ![P.x, P.y, P.z, P.w]

end MazurProof.RationalPointsN25QuotientTwoConormal

namespace MazurProof.RationalPointsN25QuotientTwoGradedKoszul

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal

abbrev k := ZMod 2

abbrev S := BinaryHomogeneousRing

end MazurProof.RationalPointsN25QuotientTwoGradedKoszul

namespace MazurProof.RationalPointsN25QuotientTwoAffineCharts

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul

abbrev OtherCoordinate (i : Fin 4) := {j : Fin 4 // j ≠ i}

abbrev AffineChart (i : Fin 4) := MvPolynomial (OtherCoordinate i) k

def dehomogenizedVariable (i j : Fin 4) : AffineChart i :=
  if h : j ≠ i then MvPolynomial.X ⟨j, h⟩ else 1

def ambientDehomogenize (i : Fin 4) : S →+* AffineChart i :=
  MvPolynomial.eval₂Hom MvPolynomial.C (dehomogenizedVariable i)

@[simp]
theorem ambientDehomogenize_X_self (i : Fin 4) :
    ambientDehomogenize i (MvPolynomial.X i) = 1 := by
  simp [ambientDehomogenize, dehomogenizedVariable]

def chartAffineQuadric (i : Fin 4) : AffineChart i :=
  ambientDehomogenize i canonicalQuadricPolynomial25Two

def chartAffineCubic (i : Fin 4) : AffineChart i :=
  ambientDehomogenize i canonicalCubicPolynomial25Two

def chartAffineRelation (i : Fin 4) : Fin 2 → AffineChart i :=
  Fin.cases (chartAffineQuadric i) (fun _ ↦ chartAffineCubic i)

@[simp]
theorem chartAffineRelation_zero (i : Fin 4) :
    chartAffineRelation i 0 = chartAffineQuadric i := rfl

@[simp]
theorem chartAffineRelation_one (i : Fin 4) :
    chartAffineRelation i 1 = chartAffineCubic i := rfl

theorem chartAffineRelation_range (i : Fin 4) :
    Set.range (chartAffineRelation i) =
      ({chartAffineQuadric i, chartAffineCubic i} : Set (AffineChart i)) := by
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · intro hp
    rcases hp with hp | hp
    · exact ⟨0, hp.symm⟩
    · exact ⟨1, hp.symm⟩

def chartAffineEquationIdeal (i : Fin 4) : Ideal (AffineChart i) :=
  Ideal.span (Set.range (chartAffineRelation i))

end MazurProof.RationalPointsN25QuotientTwoAffineCharts

namespace MazurProof.RationalPointsN25QuotientTwoStructuralJacobian

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts

def mappedAmbientPoint {K : Type*} [CommRing K] (φ : S →+* K) :
    Coordinates4 K :=
  ⟨φ (MvPolynomial.X 0), φ (MvPolynomial.X 1),
    φ (MvPolynomial.X 2), φ (MvPolynomial.X 3)⟩

@[simp]
theorem coordinates4ToFun_mappedAmbientPoint
    {K : Type*} [CommRing K] (φ : S →+* K) (a : Fin 4) :
    coordinates4ToFun (mappedAmbientPoint φ) a = φ (MvPolynomial.X a) := by
  fin_cases a <;> rfl

def mapCoordinates4 {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) : Coordinates4 L :=
  ⟨φ P.x, φ P.y, φ P.z, φ P.w⟩

@[simp]
theorem map_canonicalQuadric_coordinates
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalQuadric25CharTwo P) =
      canonicalQuadric25CharTwo (mapCoordinates4 φ P) := by
  simp [canonicalQuadric25CharTwo, mapCoordinates4]

@[simp]
theorem map_canonicalCubic_coordinates
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalCubic25CharTwo P) =
      canonicalCubic25CharTwo (mapCoordinates4 φ P) := by
  simp [canonicalCubic25CharTwo, mapCoordinates4]

theorem map_canonicalQuadric
    {K : Type*} [CommRing K] (φ : S →+* K) :
    φ canonicalQuadricPolynomial25Two =
      canonicalQuadric25CharTwo (mappedAmbientPoint φ) := by
  simp [canonicalQuadricPolynomial25Two, mappedAmbientPoint,
    canonicalQuadric25CharTwo]

theorem map_canonicalCubic
    {K : Type*} [CommRing K] (φ : S →+* K) :
    φ canonicalCubicPolynomial25Two =
      canonicalCubic25CharTwo (mappedAmbientPoint φ) := by
  simp [canonicalCubicPolynomial25Two, mappedAmbientPoint,
    canonicalCubic25CharTwo]

end MazurProof.RationalPointsN25QuotientTwoStructuralJacobian

namespace MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian

abbrev ChartQuotient (pivot : Fin 4) :=
  AffineChart pivot ⧸ chartAffineEquationIdeal pivot

def chartMap (pivot : Fin 4) : S →+* ChartQuotient pivot :=
  (algebraMap (AffineChart pivot) (ChartQuotient pivot)).comp
    (ambientDehomogenize pivot)

@[simp]
theorem chartQuotient_relation_zero (pivot : Fin 4) (r : Fin 2) :
    algebraMap (AffineChart pivot) (ChartQuotient pivot)
        (chartAffineRelation pivot r) = 0 := by
  change Ideal.Quotient.mk (chartAffineEquationIdeal pivot)
      (chartAffineRelation pivot r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨r, rfl⟩

@[simp]
theorem chartMap_quadric_zero (pivot : Fin 4) :
    chartMap pivot canonicalQuadricPolynomial25Two = 0 := by
  simpa [chartMap, chartAffineQuadric] using
    chartQuotient_relation_zero pivot 0

@[simp]
theorem chartMap_cubic_zero (pivot : Fin 4) :
    chartMap pivot canonicalCubicPolynomial25Two = 0 := by
  simpa [chartMap, chartAffineCubic] using
    chartQuotient_relation_zero pivot 1

def chartQuotientPoint (pivot : Fin 4) : Coordinates4 (ChartQuotient pivot) :=
  mappedAmbientPoint (chartMap pivot)

@[simp]
theorem chartMap_X_pivot (pivot : Fin 4) :
    chartMap pivot (MvPolynomial.X pivot) = 1 := by
  change algebraMap (AffineChart pivot) (ChartQuotient pivot)
      (ambientDehomogenize pivot (MvPolynomial.X pivot)) = 1
  rw [ambientDehomogenize_X_self, map_one]

@[simp]
theorem chartQuotientPoint_pivot (pivot : Fin 4) :
    coordinates4ToFun (chartQuotientPoint pivot) pivot = 1 := by
  rw [show coordinates4ToFun (chartQuotientPoint pivot) pivot =
      chartMap pivot (MvPolynomial.X pivot) by
    exact coordinates4ToFun_mappedAmbientPoint (chartMap pivot) pivot]
  exact chartMap_X_pivot pivot

@[simp]
theorem chartQuotientPoint_quadric (pivot : Fin 4) :
    canonicalQuadric25CharTwo (chartQuotientPoint pivot) = 0 := by
  change canonicalQuadric25CharTwo (mappedAmbientPoint (chartMap pivot)) = 0
  rw [← map_canonicalQuadric (chartMap pivot)]
  exact chartMap_quadric_zero pivot

@[simp]
theorem chartQuotientPoint_cubic (pivot : Fin 4) :
    canonicalCubic25CharTwo (chartQuotientPoint pivot) = 0 := by
  change canonicalCubic25CharTwo (mappedAmbientPoint (chartMap pivot)) = 0
  rw [← map_canonicalCubic (chartMap pivot)]
  exact chartMap_cubic_zero pivot

end MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth

namespace MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth

abbrev WChartQuotient := ChartQuotient (3 : Fin 4)

def scaleCoordinates4 {K : Type*} [Mul K]
    (a : K) (C : Coordinates4 K) : Coordinates4 K :=
  ⟨a * C.x, a * C.y, a * C.z, a * C.w⟩

theorem canonicalQuadric25CharTwo_scale
    {K : Type*} [CommRing K] (a : K) (C : Coordinates4 K) :
    canonicalQuadric25CharTwo (scaleCoordinates4 a C) =
      a ^ 2 * canonicalQuadric25CharTwo C := by
  simp [scaleCoordinates4, canonicalQuadric25CharTwo]
  ring

theorem canonicalCubic25CharTwo_scale
    {K : Type*} [CommRing K] (a : K) (C : Coordinates4 K) :
    canonicalCubic25CharTwo (scaleCoordinates4 a C) =
      a ^ 3 * canonicalCubic25CharTwo C := by
  simp [scaleCoordinates4, canonicalCubic25CharTwo]
  ring

end MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation

namespace MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation

abbrev W := WChartQuotient


noncomputable def qx : W :=
  Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
    (MvPolynomial.X (⟨0, by decide⟩ : OtherCoordinate (3 : Fin 4)))

noncomputable def qy : W :=
  Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
    (MvPolynomial.X (⟨1, by decide⟩ : OtherCoordinate (3 : Fin 4)))

noncomputable def qz : W :=
  Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
    (MvPolynomial.X (⟨2, by decide⟩ : OtherCoordinate (3 : Fin 4)))

end MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective

namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective

abbrev ZChartRing := ChartQuotient (2 : Fin 4)

def zW : ZChartRing := chartMap 2 (MvPolynomial.X 3)

end MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

namespace MazurProof.N25F_NonBoundaryPrincipalDivisor

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
open MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

abbrev W := WChartQuotient

end MazurProof.N25F_NonBoundaryPrincipalDivisor

namespace MazurProof.N25F_ZChartWChartEquiv

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
open MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal
open MazurProof.N25F_NonBoundaryPrincipalDivisor

def zX : ZChartRing := chartMap 2 (MvPolynomial.X 0)

def zY : ZChartRing := chartMap 2 (MvPolynomial.X 1)

end MazurProof.N25F_ZChartWChartEquiv

namespace MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
open MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal
open MazurProof.N25F_NonBoundaryPrincipalDivisor
open MazurProof.N25F_ZChartWChartEquiv
open Polynomial

private abbrev k := ZMod 2


private abbrev zRing := k[X]

def planeSexticPolynomial : zRing[X] :=
  X ^ 4 + C (X ^ 3 + 1) * X ^ 3 + C (X ^ 2 + X) * X ^ 2 +
    C (X ^ 4) * X + C (X ^ 2)

abbrev PlaneCoordinateRing := AdjoinRoot planeSexticPolynomial

def planeZ : PlaneCoordinateRing :=
  AdjoinRoot.of planeSexticPolynomial Polynomial.X

def wChartPoint {K : Type*} [CommRing K] (x y z : K) :
    RationalPointsN25QuotientF2.Coordinates4 K := ⟨x, y, z, 1⟩

def projectionDenominator {K : Type*} [CommRing K] (x z : K) : K :=
  x * z + x + z

def projectionNumerator {K : Type*} [CommRing K] (x z : K) : K :=
  x ^ 2 + x * z + z ^ 2 + z

def planeSexticValue {K : Type*} [CommRing K] (x z : K) : K :=
  x ^ 4 + x ^ 3 * z ^ 3 + x ^ 3 + x ^ 2 * z ^ 2 +
    x ^ 2 * z + x * z ^ 4 + z ^ 2

theorem planeSexticPolynomial_eval
    {K : Type*} [CommRing K] [Algebra k K] (x z : K) :
    planeSexticPolynomial.eval₂
        (Polynomial.eval₂RingHom (algebraMap k K) z) x =
      planeSexticValue x z := by
  simp only [planeSexticPolynomial, planeSexticValue, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_C, eval₂_one, map_add, map_pow, map_one,
    coe_eval₂RingHom]
  ring

theorem planeSextic_elimination_identity
    {K : Type*} [CommRing K] [CharP K 2] (x y z : K) :
    planeSexticValue x z =
      projectionDenominator x z ^ 2 *
          RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
            (wChartPoint x y z) +
        (projectionNumerator x z + projectionDenominator x z * y +
            z * projectionDenominator x z) *
          RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
            (wChartPoint x y z) := by
  simp [planeSexticValue, projectionDenominator, projectionNumerator,
    wChartPoint,
    RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo,
    RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination
    -(x ^ 3 * y * z + x ^ 3 * y + 2 * x ^ 3 * z ^ 2 + 3 * x ^ 3 * z +
      x ^ 2 * y ^ 2 * z ^ 2 + 2 * x ^ 2 * y ^ 2 * z + x ^ 2 * y ^ 2 +
      x ^ 2 * y * z ^ 3 + 3 * x ^ 2 * y * z ^ 2 + 3 * x ^ 2 * y * z +
      2 * x ^ 2 * z ^ 3 + 5 * x ^ 2 * z ^ 2 + 2 * x ^ 2 * z +
      2 * x * y ^ 2 * z ^ 2 + 2 * x * y ^ 2 * z + 3 * x * y * z ^ 3 +
      5 * x * y * z ^ 2 + x * y * z + 4 * x * z ^ 3 + 3 * x * z ^ 2 +
      y ^ 2 * z ^ 2 + 2 * y * z ^ 3 + y * z ^ 2 + z ^ 4 + 2 * z ^ 3) * htwo

theorem planeSexticPolynomial_eval_eq_zero_of_canonical
    {K : Type*} [CommRing K] [CharP K 2] [Algebra k K] (x y z : K)
    (hquadric :
      RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
        (wChartPoint x y z) = 0)
    (hcubic :
      RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
        (wChartPoint x y z) = 0) :
    planeSexticPolynomial.eval₂
        (Polynomial.eval₂RingHom (algebraMap k K) z) x = 0 := by
  rw [planeSexticPolynomial_eval, planeSextic_elimination_identity,
    hquadric, hcubic]
  ring

end MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField

namespace MazurProof.RationalPointsN25QuotientTwoPlaneChartBridge

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
open MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal
open MazurProof.N25F_NonBoundaryPrincipalDivisor
open MazurProof.N25F_ZChartWChartEquiv
open MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField
open Polynomial

private abbrev k := ZMod 2

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

def planeCoordinateRingToCanonicalWChart :
    PlaneCoordinateRing →+* ChartQuotient 3 :=
  AdjoinRoot.lift zPolynomialToCanonicalWChart canonicalWChartX
    planeSexticPolynomial_eval_canonicalWChart

@[simp]
theorem planeCoordinateRingToCanonicalWChart_planeZ :
    planeCoordinateRingToCanonicalWChart planeZ = canonicalWChartZ := by
  simp [planeCoordinateRingToCanonicalWChart, planeZ,
    zPolynomialToCanonicalWChart]

end MazurProof.RationalPointsN25QuotientTwoPlaneChartBridge

namespace MazurProof.RationalPointsN25QuotientTwoWChartNormalization

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
open MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal
open MazurProof.N25F_NonBoundaryPrincipalDivisor
open MazurProof.N25F_ZChartWChartEquiv
open MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField
open MazurProof.RationalPointsN25QuotientTwoPlaneChartBridge
local notation "Rz" => Polynomial (ZMod 2)
local notation "A" => PlaneCoordinateRing
local notation "W" => ChartQuotient 3

instance planeAlgebraW : Algebra A W :=
  planeCoordinateRingToCanonicalWChart.toAlgebra

instance rzAlgebraW : Algebra Rz W :=
  ((algebraMap A W).comp (algebraMap Rz A)).toAlgebra

end MazurProof.RationalPointsN25QuotientTwoWChartNormalization

namespace MazurProof.N25F_ZChartFractionMap

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoWChartNormalization
open N25F_ZChartWChartEquiv

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

/-- The normalization algebra sends its polynomial variable to the actual
`Z/W` coordinate of the fixed canonical chart. -/
theorem algebraMap_Rz_X :
    algebraMap (Polynomial (ZMod 2)) W Polynomial.X = qz := by
  change planeCoordinateRingToCanonicalWChart
    (AdjoinRoot.of planeSexticPolynomial Polynomial.X) = qz
  change planeCoordinateRingToCanonicalWChart planeZ = qz
  rw [planeCoordinateRingToCanonicalWChart_planeZ]
  simp [canonicalWChartZ, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize, dehomogenizedVariable, qz]

variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W]

/-- The genuine nonvanishing of `Z/W` follows from the established
torsion-free normalization algebra over the polynomial ring `F₂[z]`. -/
theorem qz_ne_zero : (qz : W) ≠ 0 := by
  rw [← algebraMap_Rz_X]
  exact (map_ne_zero_iff (algebraMap (Polynomial (ZMod 2)) W)
    (FaithfulSMul.algebraMap_injective (Polynomial (ZMod 2)) W)).2 Polynomial.X_ne_zero

/-- The Z/W coordinate stays nonzero in the actual W-chart fraction field. -/
theorem fraction_qz_ne_zero : algebraMap W (FractionRing W) qz ≠ 0 :=
  (map_ne_zero_iff (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W))).2 qz_ne_zero

private theorem wChartPoint_eq :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

variable [IsDomain W]

/-- The universal W-chart point, mapped to its fraction field and normalized
at Z. The denominator is the proved nonzero coordinate `qz`. -/
def zFractionPoint : Coordinates4 (FractionRing W) :=
  scaleCoordinates4 (algebraMap W (FractionRing W) qz)⁻¹
    (mapCoordinates4 (algebraMap W (FractionRing W)) (chartQuotientPoint 3))

@[simp]
theorem zFractionPoint_z : zFractionPoint.z = 1 := by
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ *
    algebraMap W (FractionRing W) qz = 1
  exact inv_mul_cancel₀ fraction_qz_ne_zero

private theorem zFractionPoint_quadric : canonicalQuadric25CharTwo zFractionPoint = 0 := by
  rw [zFractionPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem zFractionPoint_cubic : canonicalCubic25CharTwo zFractionPoint = 0 := by
  rw [zFractionPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

/-- The actual coordinate-rigid transition from the Z-chart ring to the
fraction field of the fixed W-chart ring. -/
def zChartToFraction : ZChartRing →ₐ[ZMod 2] FractionRing W :=
  chartPointEval 2 zFractionPoint
    (by simpa [coordinates4ToFun] using zFractionPoint_z)
    zFractionPoint_quadric zFractionPoint_cubic

@[simp]
theorem zChartToFraction_zY :
    zChartToFraction zY =
      algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qz := by
  rw [zChartToFraction, zY, chartPointEval_chartMap_X]
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ * algebraMap W (FractionRing W) qy = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem zChartToFraction_zX :
    zChartToFraction zX =
      algebraMap W (FractionRing W) qx / algebraMap W (FractionRing W) qz := by
  rw [zChartToFraction, zX, chartPointEval_chartMap_X]
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ * algebraMap W (FractionRing W) qx = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem zChartToFraction_zW :
    zChartToFraction zW = 1 / algebraMap W (FractionRing W) qz := by
  rw [zChartToFraction, zW, chartPointEval_chartMap_X]
  rw [zFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qz)⁻¹ * algebraMap W (FractionRing W) 1 = _
  rw [map_one, mul_one, one_div]

end MazurProof.N25F_ZChartFractionMap

#check @MazurProof.N25F_ZChartFractionMap.algebraMap_Rz_X
#print axioms MazurProof.N25F_ZChartFractionMap.algebraMap_Rz_X
#check @MazurProof.N25F_ZChartFractionMap.qz_ne_zero
#print axioms MazurProof.N25F_ZChartFractionMap.qz_ne_zero
#check @MazurProof.N25F_ZChartFractionMap.fraction_qz_ne_zero
#print axioms MazurProof.N25F_ZChartFractionMap.fraction_qz_ne_zero
#check @MazurProof.N25F_ZChartFractionMap.zFractionPoint_z
#print axioms MazurProof.N25F_ZChartFractionMap.zFractionPoint_z
#check @MazurProof.N25F_ZChartFractionMap.zChartToFraction
#print axioms MazurProof.N25F_ZChartFractionMap.zChartToFraction
#check @MazurProof.N25F_ZChartFractionMap.zChartToFraction_zX
#print axioms MazurProof.N25F_ZChartFractionMap.zChartToFraction_zX
#check @MazurProof.N25F_ZChartFractionMap.zChartToFraction_zY
#print axioms MazurProof.N25F_ZChartFractionMap.zChartToFraction_zY
#check @MazurProof.N25F_ZChartFractionMap.zChartToFraction_zW
#print axioms MazurProof.N25F_ZChartFractionMap.zChartToFraction_zW
