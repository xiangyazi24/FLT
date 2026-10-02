import FLT.Assumptions.MazurProof.N25F_InfinityNormalization
import FLT.Assumptions.MazurProof.N25F_NormBaseTwist

/-! Compare norms on the same fixed curve field under the actual affine
and reciprocal rational-base actions. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityAffineNormComparison
open N25F_RationalBaseInversion N25F_InfinityFunctionField
open N25F_InfinityNormalization N25F_NormBaseTwist
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
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
