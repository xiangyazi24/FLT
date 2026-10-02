import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryCenters
import FLT.Assumptions.MazurProof.N25F_CenterLocalization

/-! The actual boundary local rings are the localizations of the reciprocal
normalization at their constructed center primes. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityLocalizations
open N25F_InfinityNormalization N25F_InfinityBoundaryMaps
open N25F_InfinityBoundaryCenters N25F_CenterLocalization
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XLocalFractionEmbedding N25F_YZLocalFractionEmbedding N25F_ZBoundaryOrder
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The actual X boundary ring is the normalization localized at its center. -/
def xInfinityLocalizationEquiv :
    letI : Algebra InfinityNormalization XLocalRing :=
      infinityNormalizationToX.toRingHom.toAlgebra
    Localization.AtPrime xInfinityPrime ≃ₐ[InfinityNormalization] XLocalRing :=
  centerLocalizationEquiv xInfinityPrime infinityNormalizationToX.toRingHom rfl
    xInfinityPrime_ne_bot xLocalToFraction.toRingHom xLocalToFraction_injective
    (RingHom.ext fun a => xLocalToFraction_infinityNormalizationToX a)

@[simp]
theorem xInfinityLocalizationEquiv_algebraMap (a : InfinityNormalization) :
    xInfinityLocalizationEquiv
      (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a) =
      infinityNormalizationToX a :=
  by
    letI : Algebra InfinityNormalization XLocalRing :=
      infinityNormalizationToX.toRingHom.toAlgebra
    exact xInfinityLocalizationEquiv.commutes a

/-- The local identification preserves the fixed common-field inclusion. -/
@[simp]
theorem xLocalToFraction_localization_algebraMap (a : InfinityNormalization) :
    xLocalToFraction (xInfinityLocalizationEquiv
      (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a)) =
      (a : CurveField) := by
  rw [xInfinityLocalizationEquiv_algebraMap,
    xLocalToFraction_infinityNormalizationToX]

/-- The actual YZ boundary ring is the normalization localized at its center. -/
def yzInfinityLocalizationEquiv :
    letI : Algebra InfinityNormalization YZLocalRing :=
      infinityNormalizationToYZ.toRingHom.toAlgebra
    Localization.AtPrime yzInfinityPrime ≃ₐ[InfinityNormalization] YZLocalRing :=
  centerLocalizationEquiv yzInfinityPrime infinityNormalizationToYZ.toRingHom rfl
    yzInfinityPrime_ne_bot yzLocalToFraction.toRingHom yzLocalToFraction_injective
    (RingHom.ext fun a => yzLocalToFraction_infinityNormalizationToYZ a)

@[simp]
theorem yzInfinityLocalizationEquiv_algebraMap (a : InfinityNormalization) :
    yzInfinityLocalizationEquiv
      (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a) =
      infinityNormalizationToYZ a :=
  by
    letI : Algebra InfinityNormalization YZLocalRing :=
      infinityNormalizationToYZ.toRingHom.toAlgebra
    exact yzInfinityLocalizationEquiv.commutes a

/-- The local identification preserves the fixed common-field inclusion. -/
@[simp]
theorem yzLocalToFraction_localization_algebraMap (a : InfinityNormalization) :
    yzLocalToFraction (yzInfinityLocalizationEquiv
      (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a)) =
      (a : CurveField) := by
  rw [yzInfinityLocalizationEquiv_algebraMap,
    yzLocalToFraction_infinityNormalizationToYZ]

/-- The actual Z boundary ring is the normalization localized at its center. -/
def zInfinityLocalizationEquiv :
    letI : Algebra InfinityNormalization ZLocalRing :=
      infinityNormalizationToZ.toRingHom.toAlgebra
    Localization.AtPrime zInfinityPrime ≃ₐ[InfinityNormalization] ZLocalRing :=
  centerLocalizationEquiv zInfinityPrime infinityNormalizationToZ.toRingHom rfl
    zInfinityPrime_ne_bot zLocalToFraction.toRingHom zLocalToFraction_injective
    (RingHom.ext fun a => zLocalToFraction_infinityNormalizationToZ a)

@[simp]
theorem zInfinityLocalizationEquiv_algebraMap (a : InfinityNormalization) :
    zInfinityLocalizationEquiv
      (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a) =
      infinityNormalizationToZ a :=
  by
    letI : Algebra InfinityNormalization ZLocalRing :=
      infinityNormalizationToZ.toRingHom.toAlgebra
    exact zInfinityLocalizationEquiv.commutes a

/-- The local identification preserves the fixed common-field inclusion. -/
@[simp]
theorem zLocalToFraction_localization_algebraMap (a : InfinityNormalization) :
    zLocalToFraction (zInfinityLocalizationEquiv
      (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a)) =
      (a : CurveField) := by
  rw [zInfinityLocalizationEquiv_algebraMap,
    zLocalToFraction_infinityNormalizationToZ]

end MazurProof.N25F_InfinityLocalizations
