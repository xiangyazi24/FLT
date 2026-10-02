import FLT.Assumptions.MazurProof.N25F_InfinityNormFraction
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryOrderTransport
import FLT.Assumptions.MazurProof.N25F_InfinityNormMultiplicity
import FLT.Assumptions.MazurProof.N25F_LocalFractionFactorOrder
import Lean.Elab.Tactic.Omega

/-! The actual reciprocal field norm has order at (T) equal to the sum
of the three existing signed boundary orders of every nonzero function. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityNormBoundarySum
open UniqueFactorizationMonoid
open N25F_RationalBaseInversion N25F_InfinityBaseMaps N25F_InfinityFunctionField
open N25F_InfinityNormalization N25F_InfinityBoundaryAlgebras
open N25F_InfinityBoundaryCenters N25F_InfinityPrimeContraction
open N25F_InfinityNormFraction N25F_InfinityNormMultiplicity
open N25F_InfinityBoundaryOrderTransport N25F_LocalFactorOrder N25F_LocalFractionFactorOrder
open N25F_XBoundaryOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
attribute [local instance] infinityPolynomialAlgebra infinityRationalAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra
local instance : Module BasePolynomial CurveField :=
  @Algebra.toModule BasePolynomial CurveField _ _ infinityPolynomialAlgebra
local instance : SMul BasePolynomial CurveField := infinityPolynomialAlgebra.toSMul
local instance : Module BaseField CurveField :=
  @Algebra.toModule BaseField CurveField _ _ infinityRationalAlgebra
local instance : SMul BaseField CurveField := infinityRationalAlgebra.toSMul
local instance : IsScalarTower BasePolynomial BaseField CurveField :=
  IsScalarTower.of_algebraMap_eq fun p => (infinityRationalBaseToField_algebraMap p).symm
local instance : Module.Finite BaseField CurveField :=
  infinityRationalBaseToField_finite_finrank.1

/-- The genuine fraction-field order at the actual reciprocal base prime (T). -/
def infinityBaseFractionOrder : BaseField →*₀ WithZero (Multiplicative ℤ) :=
  Ring.ordFrac (Localization.AtPrime infinityBasePrime)

private theorem infinity_intNorm_ne_zero (a : InfinityNormalization) (ha : a ≠ 0) :
    Algebra.intNorm BasePolynomial InfinityNormalization a ≠ 0 := by
  have hI : (Ideal.span {a} : Ideal InfinityNormalization) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  have hN : Ideal.relNorm BasePolynomial (Ideal.span {a}) ≠ ⊥ :=
    Ideal.relNorm_eq_bot_iff.not.mpr hI
  rw [Ideal.relNorm_singleton] at hN
  exact Ideal.span_singleton_eq_bot.not.mp hN

/-- For the fixed function and exact reciprocal base action, the order of
its field norm is the sum of its genuine signed X, YZ and Z boundary orders. -/
theorem infinity_norm_boundary_order_sum (f : Additive CurveFieldˣ) :
    WithZero.log (infinityBaseFractionOrder (Algebra.norm BaseField (f.toMul : CurveField))) =
      xBoundaryOrder f + yzBoundaryOrder f + zBoundaryOrder f := by
  obtain ⟨a, b, ha, hb, hf⟩ := exists_normalization_fraction (f.toMul : CurveField) (Units.ne_zero _)
  have hp : infinityBasePrime ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Polynomial.X_ne_zero (R := ZMod 2))
  rw [xBoundaryOrder_normalization_fraction a b ha hb f hf,
    yzBoundaryOrder_normalization_fraction a b ha hb f hf,
    zBoundaryOrder_normalization_fraction a b ha hb f hf]
  rw [hf, infinity_norm_fraction]
  change WithZero.log (Ring.ordFrac (Localization.AtPrime infinityBasePrime)
    (algebraMap BasePolynomial BaseField (Algebra.intNorm BasePolynomial InfinityNormalization a) /
      algebraMap BasePolynomial BaseField (Algebra.intNorm BasePolynomial InfinityNormalization b))) = _
  rw [log_ordFrac_atPrime_div infinityBasePrime hp _ _
    (infinity_intNorm_ne_zero a ha) (infinity_intNorm_ne_zero b hb)]
  rw [ord_algebraMap_eq_factor_count a ha _ xInfinityPrime_ne_bot,
    ord_algebraMap_eq_factor_count b hb _ xInfinityPrime_ne_bot,
    ord_algebraMap_eq_factor_count a ha _ yzInfinityPrime_ne_bot,
    ord_algebraMap_eq_factor_count b hb _ yzInfinityPrime_ne_bot,
    ord_algebraMap_eq_factor_count a ha _ zInfinityPrime_ne_bot,
    ord_algebraMap_eq_factor_count b hb _ zInfinityPrime_ne_bot]
  simp only [ENat.toNat_coe]
  have hma := infinity_relNorm_multiplicity (Ideal.span {a}) (Ideal.span_singleton_eq_bot.not.mpr ha)
  have hmb := infinity_relNorm_multiplicity (Ideal.span {b}) (Ideal.span_singleton_eq_bot.not.mpr hb)
  rw [Ideal.relNorm_singleton] at hma hmb
  rw [hma, hmb]
  simp only [Nat.cast_add]
  omega

end MazurProof.N25F_InfinityNormBoundarySum
