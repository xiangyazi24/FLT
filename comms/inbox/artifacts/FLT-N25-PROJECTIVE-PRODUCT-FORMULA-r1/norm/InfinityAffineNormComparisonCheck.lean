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

#print axioms MazurProof.N25F_NormBaseTwist.norm_twist
#print axioms affineFieldNorm
#print axioms infinity_norm_eq_baseInversion_affine_norm
end MazurProof.N25F_InfinityAffineNormComparison
