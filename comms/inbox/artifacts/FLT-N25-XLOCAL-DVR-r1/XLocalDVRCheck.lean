import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
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

namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoGradedKoszul
open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective

abbrev XChartRing := ChartQuotient (0 : Fin 4)

def xY : XChartRing := chartMap 0 (MvPolynomial.X 1)


def xZ : XChartRing := chartMap 0 (MvPolynomial.X 2)


def xW : XChartRing := chartMap 0 (MvPolynomial.X 3)

end MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

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
open MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

abbrev W := WChartQuotient

end MazurProof.N25F_NonBoundaryPrincipalDivisor


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

variable [IsDedekindDomain W]

/-- The actual X-chart ring is a domain, transported from the established
W-chart domain through the explicit algebra equivalence. -/
instance xChartRing_isDomain : IsDomain XChartRing :=
  xChartAlgEquivWChart.toRingEquiv.toMulEquiv.isDomain W

end MazurProof.N25F_XChartWChartEquiv


namespace MazurProof.N25F_XChartFractionMap

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryChartArtin

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

/-- Evaluation of the actual W-chart quotient at the binary curve point
`[1:1:0:1]`, where the X-coordinate is one. -/
def binaryPointEval : W →ₐ[ZMod 2] ZMod 2 :=
  chartPointEval 3 ⟨1, 1, 0, 1⟩ rfl
    (by decide)
    (by decide)

@[simp]
theorem binaryPointEval_qx : binaryPointEval qx = 1 := by
  simp [binaryPointEval, chartPointEval, affinePointEval, qx, coordinates4ToFun]

/-- Nonvanishing of the actual X/W coordinate, witnessed by a binary point. -/
theorem qx_ne_zero : (qx : W) ≠ 0 := by
  intro h
  have heq := congrArg binaryPointEval h
  simpa using heq

variable [IsDedekindDomain W]

/-- The X/W coordinate stays nonzero in the actual W-chart fraction field. -/
theorem fraction_qx_ne_zero : algebraMap W (FractionRing W) qx ≠ 0 :=
  (map_ne_zero_iff (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W))).2 qx_ne_zero

private theorem wChartPoint_eq :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

/-- The universal W-chart point, mapped to its fraction field and normalized
at X. The denominator is the proved nonzero coordinate `qx`. -/
def xFractionPoint : Coordinates4 (FractionRing W) :=
  scaleCoordinates4 (algebraMap W (FractionRing W) qx)⁻¹
    (mapCoordinates4 (algebraMap W (FractionRing W)) (chartQuotientPoint 3))

@[simp]
theorem xFractionPoint_x : xFractionPoint.x = 1 := by
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ *
    algebraMap W (FractionRing W) qx = 1
  exact inv_mul_cancel₀ fraction_qx_ne_zero

private theorem xFractionPoint_quadric : canonicalQuadric25CharTwo xFractionPoint = 0 := by
  rw [xFractionPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem xFractionPoint_cubic : canonicalCubic25CharTwo xFractionPoint = 0 := by
  rw [xFractionPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

/-- The actual coordinate-rigid transition from the X-chart ring to the
fraction field of the fixed W-chart ring. -/
def xChartToFraction : XChartRing →ₐ[ZMod 2] FractionRing W :=
  chartPointEval 0 xFractionPoint
    (by simpa [coordinates4ToFun] using xFractionPoint_x)
    xFractionPoint_quadric xFractionPoint_cubic

@[simp]
theorem xChartToFraction_xY :
    xChartToFraction xY =
      algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qx := by
  rw [xChartToFraction, xY, chartPointEval_chartMap_X]
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ * algebraMap W (FractionRing W) qy = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem xChartToFraction_xZ :
    xChartToFraction xZ =
      algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qx := by
  rw [xChartToFraction, xZ, chartPointEval_chartMap_X]
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ * algebraMap W (FractionRing W) qz = _
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem xChartToFraction_xW :
    xChartToFraction xW = 1 / algebraMap W (FractionRing W) qx := by
  rw [xChartToFraction, xW, chartPointEval_chartMap_X]
  rw [xFractionPoint, wChartPoint_eq]
  change (algebraMap W (FractionRing W) qx)⁻¹ * algebraMap W (FractionRing W) 1 = _
  rw [map_one, mul_one, one_div]

end MazurProof.N25F_XChartFractionMap


namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal

open MazurProof.RationalPointsN25QuotientTwoAffineCharts
open MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
open MazurProof.RationalPointsN25QuotientTwoConormal
open MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

local notation "k₂" => ZMod 2

abbrev XAffineRing := AffineChart (0 : Fin 4)

private def xAffineEval : XAffineRing →+* k₂ :=
  MvPolynomial.eval₂Hom (RingHom.id k₂) (fun _ => 0)

private noncomputable def xAffineEvalAlg : XAffineRing →ₐ[k₂] k₂ where
  __ := xAffineEval
  commutes' c := by simp [xAffineEval]

private theorem xAffineEval_quadric :
    xAffineEval (chartAffineQuadric (0 : Fin 4)) = 0 := by
  simp [xAffineEval, chartAffineQuadric, ambientDehomogenize,
    dehomogenizedVariable, canonicalQuadricPolynomial25Two]

private theorem xAffineEval_cubic :
    xAffineEval (chartAffineCubic (0 : Fin 4)) = 0 := by
  simp [xAffineEval, chartAffineCubic, ambientDehomogenize,
    dehomogenizedVariable, canonicalCubicPolynomial25Two]

private theorem xEquationIdeal_le_ker :
    chartAffineEquationIdeal (0 : Fin 4) ≤ RingHom.ker xAffineEval := by
  rw [chartAffineEquationIdeal, Ideal.span_le]
  rintro f ⟨r, rfl⟩
  fin_cases r
  · exact RingHom.mem_ker.mpr xAffineEval_quadric
  · exact RingHom.mem_ker.mpr xAffineEval_cubic

/-- Evaluation of the actual `X`-chart curve ring at `[1:0:0:0]`. -/
noncomputable def xChartEval : XChartRing →ₐ[k₂] k₂ :=
  Ideal.Quotient.liftₐ
    (chartAffineEquationIdeal (0 : Fin 4)) xAffineEvalAlg
    (fun _ ha => RingHom.mem_ker.mp (xEquationIdeal_le_ker ha))

theorem xChartEval_surjective : Function.Surjective xChartEval := by
  intro c
  refine ⟨algebraMap k₂ XChartRing c, ?_⟩
  simp [xChartEval]

/-- The maximal ideal of `[1:0:0:0]` in the actual `X` chart. -/
def xPrime : Ideal XChartRing := RingHom.ker xChartEval.toRingHom

theorem xPrime_isMaximal : xPrime.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    xChartEval.toRingHom xChartEval_surjective

local instance : xPrime.IsMaximal := xPrime_isMaximal
local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

@[simp] theorem xChartEval_xW : xChartEval xW = 0 := by
  simp [xChartEval, xAffineEvalAlg, xAffineEval, xW, chartMap,
    ambientDehomogenize, dehomogenizedVariable]

@[simp] theorem xChartEval_xY : xChartEval xY = 0 := by
  simp [xChartEval, xAffineEvalAlg, xAffineEval, xY, chartMap,
    ambientDehomogenize, dehomogenizedVariable]

@[simp] theorem xChartEval_xZ : xChartEval xZ = 0 := by
  simp [xChartEval, xAffineEvalAlg, xAffineEval, xZ, chartMap,
    ambientDehomogenize, dehomogenizedVariable]


abbrev XLocalRing := Localization.AtPrime xPrime

local instance xLocalRingCommRing : CommRing XLocalRing :=
  OreLocalization.instCommRing


noncomputable def xWGerm : XLocalRing :=
  algebraMap XChartRing XLocalRing xW


end MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal

namespace MazurProof.N25F_XLocalDVR

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_XChartWChartEquiv
open N25F_XChartFractionMap

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

variable [IsDedekindDomain W]

/-- The actual X chart inherits Dedekind structure through its explicit
algebra equivalence with the established W chart. -/
instance xChartRing_isDedekindDomain : IsDedekindDomain XChartRing := by
  letI : IsNoetherianRing XChartRing :=
    isNoetherianRing_of_ringEquiv W xChartAlgEquivWChart.symm.toRingEquiv
  letI : Ring.DimensionLEOne XChartRing :=
    Ring.DimensionLEOne.of_ringEquiv xChartAlgEquivWChart.toRingEquiv
  letI : IsIntegrallyClosed XChartRing :=
    IsIntegrallyClosed.of_equiv xChartAlgEquivWChart.symm.toRingEquiv
  exact { }

/-- The actual coordinate `W/X` is nonzero, since its image is `1/(X/W)`
in the W-chart fraction field. No injectivity of the chart map is needed. -/
theorem xW_ne_zero : (xW : XChartRing) ≠ 0 := by
  intro h
  have heq := congrArg xChartToFraction h
  rw [xChartToFraction_xW, map_zero] at heq
  exact (one_div_ne_zero fraction_qx_ne_zero) heq

/-- The boundary coordinate vanishes at the actual X-boundary point. -/
theorem xW_mem_xPrime : xW ∈ xPrime :=
  RingHom.mem_ker.mpr xChartEval_xW

/-- The prime of `[1:0:0:0]` is a nonzero prime of the actual X chart. -/
theorem xPrime_ne_bot : xPrime ≠ ⊥ := by
  intro h
  have hw := xW_mem_xPrime
  rw [h, Ideal.mem_bot] at hw
  exact xW_ne_zero hw

local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

/-- The actual curve local ring at `[1:0:0:0]` is a DVR. -/
instance xLocalRing_isDiscreteValuationRing : IsDiscreteValuationRing XLocalRing :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    XChartRing xPrime_ne_bot XLocalRing

/-- The actual germ of `W/X` stays nonzero in the boundary local ring. -/
theorem xWGerm_ne_zero : xWGerm ≠ 0 :=
  (map_ne_zero_iff (algebraMap XChartRing XLocalRing)
    (IsLocalization.injective XLocalRing xPrime.primeCompl_le_nonZeroDivisors)).2
      xW_ne_zero

end MazurProof.N25F_XLocalDVR


#check @MazurProof.N25F_XLocalDVR.xChartRing_isDedekindDomain
#print axioms MazurProof.N25F_XLocalDVR.xChartRing_isDedekindDomain
#check @MazurProof.N25F_XLocalDVR.xW_ne_zero
#print axioms MazurProof.N25F_XLocalDVR.xW_ne_zero
#check @MazurProof.N25F_XLocalDVR.xW_mem_xPrime
#print axioms MazurProof.N25F_XLocalDVR.xW_mem_xPrime
#check @MazurProof.N25F_XLocalDVR.xPrime_ne_bot
#print axioms MazurProof.N25F_XLocalDVR.xPrime_ne_bot
#check @MazurProof.N25F_XLocalDVR.xLocalRing_isDiscreteValuationRing
#print axioms MazurProof.N25F_XLocalDVR.xLocalRing_isDiscreteValuationRing
#check @MazurProof.N25F_XLocalDVR.xWGerm_ne_zero
#print axioms MazurProof.N25F_XLocalDVR.xWGerm_ne_zero
