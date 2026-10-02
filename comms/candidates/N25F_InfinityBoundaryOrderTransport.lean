import FLT.Assumptions.MazurProof.N25F_InfinityLocalizations
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras
import FLT.Assumptions.MazurProof.N25F_OrderRingEquiv
import FLT.Assumptions.MazurProof.N25F_FractionOrderDifference
import FLT.Assumptions.MazurProof.N25F_YZBoundaryOrder

/-! Transport the existing signed X, YZ and Z boundary coefficients of a
normalization fraction to genuine quotient lengths in its three localizations.
Only previously accepted maps and local equivalences are used. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityBoundaryOrderTransport
open N25F_InfinityNormalization N25F_InfinityBoundaryMaps
open N25F_InfinityBoundaryCenters N25F_InfinityLocalizations N25F_InfinityBoundaryAlgebras
open N25F_OrderRingEquiv N25F_FractionOrderDifference
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra

/-- The actual X boundary quotient length equals the normalization-local one. -/
theorem xInfinityNormalization_order (a : InfinityNormalization) :
    Ring.ord XLocalRing (infinityNormalizationToX a) =
      Ring.ord (Localization.AtPrime xInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a) := by
  have h := ord_map_ringEquiv xInfinityLocalizationEquiv.toRingEquiv
    (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a)
  change Ring.ord XLocalRing (xInfinityLocalizationEquiv _) = _ at h
  rw [xInfinityLocalizationEquiv_algebraMap] at h
  exact h

/-- The existing signed X boundary coefficient of a normalization fraction. -/
theorem xBoundaryOrder_normalization_fraction
    (a b : InfinityNormalization) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) = (a : CurveField) / (b : CurveField)) :
    xBoundaryOrder f =
      ((Ring.ord (Localization.AtPrime xInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a)).toNat : ℤ) -
      ((Ring.ord (Localization.AtPrime xInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) b)).toNat : ℤ) := by
  letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
  have hxa : infinityNormalizationToX a ≠ 0 :=
    (map_ne_zero_iff _ infinityNormalizationToX_injective).mpr ha
  have hxb : infinityNormalizationToX b ≠ 0 :=
    (map_ne_zero_iff _ infinityNormalizationToX_injective).mpr hb
  change WithZero.log (xLocalFractionOrder (f.toMul : CurveField)) = _
  rw [hf, ← xLocalToFraction_infinityNormalizationToX a,
    ← xLocalToFraction_infinityNormalizationToX b]
  change WithZero.log (Ring.ordFrac XLocalRing
    (algebraMap XLocalRing CurveField (infinityNormalizationToX a) /
      algebraMap XLocalRing CurveField (infinityNormalizationToX b))) = _
  rw [log_ordFrac_div _ _ hxa hxb,
    xInfinityNormalization_order, xInfinityNormalization_order]

/-- The actual YZ boundary quotient length equals the normalization-local one. -/
theorem yzInfinityNormalization_order (a : InfinityNormalization) :
    Ring.ord YZLocalRing (infinityNormalizationToYZ a) =
      Ring.ord (Localization.AtPrime yzInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a) := by
  have h := ord_map_ringEquiv yzInfinityLocalizationEquiv.toRingEquiv
    (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a)
  change Ring.ord YZLocalRing (yzInfinityLocalizationEquiv _) = _ at h
  rw [yzInfinityLocalizationEquiv_algebraMap] at h
  exact h

/-- The existing signed YZ boundary coefficient of a normalization fraction. -/
theorem yzBoundaryOrder_normalization_fraction
    (a b : InfinityNormalization) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) = (a : CurveField) / (b : CurveField)) :
    yzBoundaryOrder f =
      ((Ring.ord (Localization.AtPrime yzInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a)).toNat : ℤ) -
      ((Ring.ord (Localization.AtPrime yzInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) b)).toNat : ℤ) := by
  letI : Algebra YZLocalRing CurveField := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing CurveField := yzLocalToFraction_isFractionRing
  have hyza : infinityNormalizationToYZ a ≠ 0 :=
    (map_ne_zero_iff _ infinityNormalizationToYZ_injective).mpr ha
  have hyzb : infinityNormalizationToYZ b ≠ 0 :=
    (map_ne_zero_iff _ infinityNormalizationToYZ_injective).mpr hb
  change WithZero.log (yzLocalFractionOrder (f.toMul : CurveField)) = _
  rw [hf, ← yzLocalToFraction_infinityNormalizationToYZ a,
    ← yzLocalToFraction_infinityNormalizationToYZ b]
  change WithZero.log (Ring.ordFrac YZLocalRing
    (algebraMap YZLocalRing CurveField (infinityNormalizationToYZ a) /
      algebraMap YZLocalRing CurveField (infinityNormalizationToYZ b))) = _
  rw [log_ordFrac_div _ _ hyza hyzb,
    yzInfinityNormalization_order, yzInfinityNormalization_order]

/-- The actual Z boundary quotient length equals the normalization-local one. -/
theorem zInfinityNormalization_order (a : InfinityNormalization) :
    Ring.ord ZLocalRing (infinityNormalizationToZ a) =
      Ring.ord (Localization.AtPrime zInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a) := by
  have h := ord_map_ringEquiv zInfinityLocalizationEquiv.toRingEquiv
    (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a)
  change Ring.ord ZLocalRing (zInfinityLocalizationEquiv _) = _ at h
  rw [zInfinityLocalizationEquiv_algebraMap] at h
  exact h

/-- The existing signed Z boundary coefficient of a normalization fraction. -/
theorem zBoundaryOrder_normalization_fraction
    (a b : InfinityNormalization) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) = (a : CurveField) / (b : CurveField)) :
    zBoundaryOrder f =
      ((Ring.ord (Localization.AtPrime zInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a)).toNat : ℤ) -
      ((Ring.ord (Localization.AtPrime zInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) b)).toNat : ℤ) := by
  letI : Algebra ZLocalRing CurveField := zLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing CurveField := zLocalToFraction_isFractionRing
  have hza : infinityNormalizationToZ a ≠ 0 :=
    (map_ne_zero_iff _ infinityNormalizationToZ_injective).mpr ha
  have hzb : infinityNormalizationToZ b ≠ 0 :=
    (map_ne_zero_iff _ infinityNormalizationToZ_injective).mpr hb
  change WithZero.log (zLocalFractionOrder (f.toMul : CurveField)) = _
  rw [hf, ← zLocalToFraction_infinityNormalizationToZ a,
    ← zLocalToFraction_infinityNormalizationToZ b]
  change WithZero.log (Ring.ordFrac ZLocalRing
    (algebraMap ZLocalRing CurveField (infinityNormalizationToZ a) /
      algebraMap ZLocalRing CurveField (infinityNormalizationToZ b))) = _
  rw [log_ordFrac_div _ _ hza hzb,
    zInfinityNormalization_order, zInfinityNormalization_order]

end MazurProof.N25F_InfinityBoundaryOrderTransport
