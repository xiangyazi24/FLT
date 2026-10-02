import FLT.Assumptions.MazurProof.N25F_InfinityFunctionField
import Mathlib.FieldTheory.Separable

/-! Separability of the same actual curve function field under the reciprocal
rational-base action. The original canonical separability is transported
through proved equal maps and the explicit base inversion. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinitySeparable

private theorem separable_twist {B L : Type*} [Field B] [Field L]
    [Algebra B L] [Algebra.IsSeparable B L] (e : B ≃+* B) :
    letI : Algebra B L := ((algebraMap B L).comp e.toRingHom).toAlgebra
    Algebra.IsSeparable B L := by
  let oldAlgebra : Algebra B L := inferInstance
  let φ := algebraMap B L
  let newAlgebra : Algebra B L := (φ.comp e.toRingHom).toAlgebra
  have hs : @Algebra.IsSeparable B L _ _ oldAlgebra := inferInstance
  exact @Algebra.IsSeparable.of_equiv_equiv B L B L _ _ _ _ oldAlgebra newAlgebra
    e.symm (RingEquiv.refl L) (by
      ext b
      change φ (e (e.symm b)) = φ b
      rw [e.apply_symm_apply]) hs

open N25F_RationalBaseInversion N25F_InfinityFunctionField
open N25F_ProjectivePrincipalDivisor
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing W

/-- The explicit old rational-base map equals the source's canonical fraction lift. -/
theorem affineRationalBaseToField_eq_canonicalLift :
    affineRationalBaseToField.toRingHom =
      IsFractionRing.lift (K := BaseField)
        (FaithfulSMul.algebraMap_injective BasePolynomial CurveField) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors BasePolynomial)
  apply RingHom.ext
  intro p
  change affineRationalBaseToField (algebraMap BasePolynomial BaseField p) =
    IsFractionRing.lift (K := BaseField)
      (FaithfulSMul.algebraMap_injective BasePolynomial CurveField)
      (algebraMap BasePolynomial BaseField p)
  rw [affineRationalBaseToField_algebraMap, IsFractionRing.lift_algebraMap]
  rw [IsScalarTower.algebraMap_apply BasePolynomial W CurveField]
  exact (basePolynomial_inFunctionField p).symm

/-- The existing actual canonical separability applies to the explicit old action. -/
theorem affineRationalBaseToField_isSeparable :
    letI : Algebra BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra
    Algebra.IsSeparable BaseField CurveField := by
  change @Algebra.IsSeparable BaseField CurveField _ _
    affineRationalBaseToField.toRingHom.toAlgebra
  rw [affineRationalBaseToField_eq_canonicalLift]
  exact RationalPointsN25QuotientTwoWChartNormalization.canonicalWChart_fractionRing_isSeparable

/-- The actual reciprocal rational-base extension is separable. -/
theorem infinityRationalBaseToField_isSeparable :
    letI : Algebra BaseField CurveField := infinityRationalBaseToField.toRingHom.toAlgebra
    Algebra.IsSeparable BaseField CurveField := by
  letI : Algebra BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra
  letI : Algebra.IsSeparable BaseField CurveField := affineRationalBaseToField_isSeparable
  exact separable_twist (L := CurveField) baseInversion.toRingEquiv

end MazurProof.N25F_InfinitySeparable
