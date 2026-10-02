import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import InfinityNormalizationCheck
import Mathlib.RingTheory.Norm.Basic


/-! Compare norms on the same fixed curve field under the actual affine
and reciprocal rational-base actions. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_NormBaseTwist

/-- Precomposing the base action with an automorphism applies its inverse
to the norm. The two Algebra structures remain explicit. -/
theorem norm_twist {B L : Type*} [CommRing B] [CommRing L]
    (A : Algebra B L) (e : B ≃+* B) (x : L) :
    let A' : Algebra B L := ((@algebraMap B L _ _ A).comp e.toRingHom).toAlgebra
    @Algebra.norm B L _ _ A' x = e.symm (@Algebra.norm B L _ _ A x) := by
  let A' : Algebra B L := ((@algebraMap B L _ _ A).comp e.toRingHom).toAlgebra
  exact @Algebra.norm_eq_of_equiv_equiv B L B L _ _ _ _ A' A e (RingEquiv.refl L)
    (by rfl) x

end MazurProof.N25F_NormBaseTwist

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityAffineNormComparison
open N25F_RationalBaseInversion N25F_InfinityFunctionField
open N25F_InfinityNormalization N25F_NormBaseTwist
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [Module.Finite BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
attribute [local instance] infinityRationalAlgebra

/-- The norm for the established affine action sending the base variable to qz. -/
def affineFieldNorm : CurveField →* BaseField :=
  @Algebra.norm BaseField CurveField _ _ affineRationalBaseToField.toRingHom.toAlgebra

/-- The reciprocal norm is precisely the inverse base-coordinate change
applied to the affine norm, with the function itself unchanged. -/
theorem infinity_norm_eq_baseInversion_affine_norm (f : CurveField) :
    Algebra.norm BaseField f = baseInversion.symm (affineFieldNorm f) :=
  norm_twist affineRationalBaseToField.toRingHom.toAlgebra baseInversion.toRingEquiv f

end MazurProof.N25F_InfinityAffineNormComparison

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_AffineNormPolynomial
open N25F_RationalBaseInversion N25F_InfinityFunctionField
open N25F_ProjectivePrincipalDivisor N25F_InfinityAffineNormComparison
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial W]
variable [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable [hWrank : Fact (Module.finrank BasePolynomial W = 4)]
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
  FiniteDimensional.of_finrank_pos (by rw [affineRationalBaseToField_finrank hWrank.out]; decide)

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

#print axioms affineFieldNorm_algebraMap
end MazurProof.N25F_AffineNormPolynomial
