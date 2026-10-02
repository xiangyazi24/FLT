import FLT.Assumptions.MazurProof.N25F_XChartFractionMap
import FLT.Assumptions.MazurProof.N25F_XChartWChartEquiv
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Injectivity of the actual coordinate-rigid X-chart map

A noninjective homomorphism from a one-dimensional finite-type binary
algebra to a field has finite image. Applied to the actual X chart, this
would make `1/qx` have finite positive multiplicative order. But the actual
W-chart coordinate `qx` vanishes at `[0:0:0:1]`, so no positive power of it
is one. The dimension bound is transported through the explicit X/W
algebra equivalence from the established W-chart Dedekind instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_XChartFractionInjective

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryChartArtin
open N25F_XChartFractionMap N25F_XChartWChartEquiv

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

private theorem finite_power_of_not_injective
    {R K : Type*} [CommRing R] [Ring.DimensionLEOne R]
    [Algebra (ZMod 2) R] [Algebra.FiniteType (ZMod 2) R] [Field K]
    (f : R →+* K) (hf : ¬ Function.Injective f)
    (r : R) (hr : f r ≠ 0) : ∃ n : ℕ, 0 < n ∧ (f r) ^ n = 1 := by
  let m := RingHom.ker f
  have hm : m ≠ ⊥ := by
    intro h
    exact hf ((RingHom.injective_iff_ker_eq_bot f).2 h)
  letI : m.IsMaximal := (RingHom.ker_isPrime f).isMaximal hm
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite (ZMod 2) (R ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing (ZMod 2) (R ⧸ m)
  letI : Finite (R ⧸ m) := Module.finite_of_finite (ZMod 2)
  letI : Fintype (R ⧸ m) := Fintype.ofFinite _
  have hbar : Ideal.Quotient.mk m r ≠ 0 := by
    intro h
    apply hr
    simpa only [m, RingHom.kerLift_mk, map_zero] using congrArg (RingHom.kerLift f) h
  refine ⟨Fintype.card (R ⧸ m) - 1, Nat.sub_pos_of_lt Fintype.one_lt_card, ?_⟩
  have hpow := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk m r) hbar
  simpa only [m, map_pow, RingHom.kerLift_mk, map_one] using
    congrArg (RingHom.kerLift f) hpow

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

/-- Evaluation of the actual W-chart quotient at the binary origin
`[0:0:0:1]`. -/
def originEval : W →ₐ[ZMod 2] ZMod 2 :=
  chartPointEval 3 ⟨0, 0, 0, 1⟩ rfl (by decide) (by decide)

@[simp]
theorem originEval_qx : originEval qx = 0 := by
  simp [originEval, chartPointEval, affinePointEval, qx, coordinates4ToFun]

/-- No positive power of the actual X/W coordinate equals one. -/
theorem qx_pow_ne_one (n : ℕ) (hn : 0 < n) : (qx : W) ^ n ≠ 1 := by
  intro h
  have h01 := congrArg originEval h
  simpa [Nat.ne_of_gt hn] using h01

/-- The actual coordinate-rigid X-chart map into the fixed W-chart
function field is injective. No geometric or nonvanishing premise is added. -/
theorem xChartToFraction_injective : Function.Injective xChartToFraction := by
  letI : Ring.DimensionLEOne XChartRing :=
    Ring.DimensionLEOne.of_ringEquiv xChartAlgEquivWChart.toRingEquiv
  by_contra h
  obtain ⟨n, hn, hpow⟩ := finite_power_of_not_injective
    xChartToFraction.toRingHom h xW
    (by simpa using (inv_ne_zero fraction_qx_ne_zero))
  have hfrac : (algebraMap W (FractionRing W) qx) ^ n = 1 := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      xChartToFraction_xW, one_div, inv_pow, inv_eq_one] using hpow
  apply qx_pow_ne_one n hn
  apply IsFractionRing.injective W (FractionRing W)
  simpa only [map_pow, map_one] using hfrac

end MazurProof.N25F_XChartFractionInjective
