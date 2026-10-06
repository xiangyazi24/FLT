import FLT.Assumptions.MazurProof.N25F_InfinityAffineNormComparison
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! The actual affine field norm of a regular W-chart function is the
image of its existing polynomial-base norm. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_AffineNormPolynomial
open N25F_RationalBaseInversion N25F_InfinityFunctionField
open N25F_ProjectivePrincipalDivisor N25F_InfinityAffineNormComparison
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
local instance : Algebra BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra
local instance : Module BaseField CurveField :=
  @Algebra.toModule BaseField CurveField _ _ affineRationalBaseToField.toRingHom.toAlgebra
local instance : SMul BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra.toSMul
local instance : IsScalarTower BasePolynomial BaseField CurveField :=
  IsScalarTower.of_algebraMap_eq fun p => by
    calc
      algebraMap BasePolynomial CurveField p =
          algebraMap W CurveField (algebraMap BasePolynomial W p) :=
        IsScalarTower.algebraMap_apply BasePolynomial W CurveField p
      _ = affinePolynomialBaseToField p := basePolynomial_inFunctionField p
      _ = affineRationalBaseToField (algebraMap BasePolynomial BaseField p) :=
        (affineRationalBaseToField_algebraMap p).symm
local instance : Module.Finite BaseField CurveField :=
  FiniteDimensional.of_finrank_pos (by rw [affineRationalBaseToField_finrank]; decide)

/-- The fixed affine field norm agrees with the polynomial norm used by
the accepted W-chart quotient-dimension formula. -/
theorem affineFieldNorm_algebraMap (a : W) :
    affineFieldNorm (algebraMap W CurveField a) =
      algebraMap BasePolynomial BaseField (Algebra.norm BasePolynomial a) := by
  letI : Module.Free BasePolynomial W := Module.free_of_finite_type_torsion_free'
  letI : IsIntegralClosure W BasePolynomial CurveField :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  change Algebra.norm BaseField (algebraMap W CurveField a) = _
  simpa only [Algebra.intNorm_eq_norm] using
    (Algebra.algebraMap_intNorm (A := BasePolynomial) (B := W)
      (K := BaseField) (L := CurveField) a).symm

end MazurProof.N25F_AffineNormPolynomial
