import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryMaps

/-! Named boundary Algebra data for downstream modules. These are not global
instances. Import this module and enable the six desired definitions locally,
together with N25F_InfinityNormalization.infinityPolynomialAlgebra. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityBoundaryAlgebras
open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_InfinityNormalization N25F_InfinityBoundaryMaps
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal

abbrev xInfinityBaseAlgebra : Algebra BasePolynomial XLocalRing :=
  infinityBaseToX.toRingHom.toAlgebra

abbrev yzInfinityBaseAlgebra : Algebra BasePolynomial YZLocalRing :=
  infinityBaseToYZ.toRingHom.toAlgebra

abbrev zInfinityBaseAlgebra : Algebra BasePolynomial ZLocalRing :=
  infinityBaseToZ.toRingHom.toAlgebra

attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra

abbrev xInfinityNormalizationAlgebra : Algebra InfinityNormalization XLocalRing :=
  infinityNormalizationToX.toRingHom.toAlgebra

abbrev yzInfinityNormalizationAlgebra : Algebra InfinityNormalization YZLocalRing :=
  infinityNormalizationToYZ.toRingHom.toAlgebra

abbrev zInfinityNormalizationAlgebra : Algebra InfinityNormalization ZLocalRing :=
  infinityNormalizationToZ.toRingHom.toAlgebra

end MazurProof.N25F_InfinityBoundaryAlgebras
