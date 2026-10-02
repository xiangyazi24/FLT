import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
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

/-- The X/W coordinate stays nonzero in the actual W-chart fraction field. -/
theorem fraction_qx_ne_zero : algebraMap W (FractionRing W) qx ≠ 0 :=
  (map_ne_zero_iff (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W))).2 qx_ne_zero

private theorem wChartPoint_eq :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

variable [IsDomain W]

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

#print axioms MazurProof.N25F_XChartFractionMap.qx_ne_zero
#check @MazurProof.N25F_XChartFractionMap.qx_ne_zero
#check @MazurProof.N25F_XChartFractionMap.xChartToFraction
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xY
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xZ
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xW
