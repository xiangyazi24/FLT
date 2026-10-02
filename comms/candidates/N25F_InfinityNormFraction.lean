import FLT.Assumptions.MazurProof.N25F_InfinityCanonicalSeparable
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! Convert the integral norm in the actual reciprocal normalization to
the norm on the fixed curve field, retaining its exact reciprocal base action. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityNormFraction
open N25F_RationalBaseInversion N25F_InfinityBaseMaps N25F_InfinityFunctionField
open N25F_InfinityNormalization N25F_InfinityBoundaryAlgebras
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
attribute [local instance] infinityPolynomialAlgebra infinityRationalAlgebra
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

/-- Integral and fixed-field norms agree under the exact reciprocal action. -/
theorem infinity_norm_normalization (a : InfinityNormalization) :
    Algebra.norm BaseField (a : CurveField) =
      algebraMap BasePolynomial BaseField (Algebra.intNorm BasePolynomial InfinityNormalization a) :=
  (Algebra.algebraMap_intNorm (A := BasePolynomial) (B := InfinityNormalization)
    (K := BaseField) (L := CurveField) a).symm

/-- The norm of a normalization fraction is the quotient of its integral norms. -/
theorem infinity_norm_fraction (a b : InfinityNormalization) :
    Algebra.norm BaseField ((a : CurveField) / (b : CurveField)) =
      algebraMap BasePolynomial BaseField (Algebra.intNorm BasePolynomial InfinityNormalization a) /
      algebraMap BasePolynomial BaseField (Algebra.intNorm BasePolynomial InfinityNormalization b) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    infinity_norm_normalization, infinity_norm_normalization, ← div_eq_mul_inv]

/-- Every nonzero function admits nonzero numerator and denominator in the
actual reciprocal normalization, inside the same fixed function field. -/
theorem exists_normalization_fraction (f : CurveField) (hf : f ≠ 0) :
    ∃ a b : InfinityNormalization, a ≠ 0 ∧ b ≠ 0 ∧
      f = (a : CurveField) / (b : CurveField) := by
  obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective InfinityNormalization f
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [map_zero, zero_div] at h
    exact hf h.symm
  exact ⟨a, b, ha, mem_nonZeroDivisors_iff_ne_zero.mp hb, h.symm⟩

end MazurProof.N25F_InfinityNormFraction
