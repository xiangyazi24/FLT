import FLT.Assumptions.MazurProof.N25F_InfinityLocalizations
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras
import FLT.Assumptions.MazurProof.N25F_OrderRingEquiv

/-! Reciprocal-parameter orders in the actual normalization localizations.
The double-order Z center differs from each simple-order center. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityParameterOrders

private theorem parameter_order_transport {A R : Type*} [CommRing A] [CommRing R]
    (p : Ideal A) [p.IsPrime] (e : Localization.AtPrime p ≃+* R)
    (a : A) (s : R) (n : ℕ)
    (he : e (algebraMap A (Localization.AtPrime p) a) = s)
    (hs : Ring.ord R s = n) :
    Ring.ord (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) a) = n := by
  have h := N25F_OrderRingEquiv.ord_map_ringEquiv e
    (algebraMap A (Localization.AtPrime p) a)
  rw [he, hs] at h
  exact h.symm

private theorem localization_order_congr {A : Type*} [CommRing A]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime] (h : p = q) (a : A) :
    Ring.ord (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) a) =
    Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) a) := by
  subst q
  rfl

open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_InfinityNormalization N25F_InfinityBoundaryMaps
open N25F_InfinityBoundaryCenters N25F_InfinityLocalizations
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XInfinityGerm
open N25F_InfinityBoundaryAlgebras
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra

@[simp]
theorem infinityNormalizationToX_parameter :
    infinityNormalizationToX infinityParameter = xInverseZGerm := by
  change infinityNormalizationToX
    (algebraMap BasePolynomial InfinityNormalization Polynomial.X) = xInverseZGerm
  rw [infinityNormalizationToX.commutes]
  exact Polynomial.aeval_X _

theorem xInfinityParameter_order :
    Ring.ord (Localization.AtPrime xInfinityPrime)
      (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime)
        infinityParameter) = 1 :=
  parameter_order_transport xInfinityPrime xInfinityLocalizationEquiv.toRingEquiv
    infinityParameter xInverseZGerm 1
    (by change xInfinityLocalizationEquiv _ = _; rw [xInfinityLocalizationEquiv_algebraMap, infinityNormalizationToX_parameter])
    xInverseZGerm_ord_eq_one

@[simp]
theorem infinityNormalizationToYZ_parameter :
    infinityNormalizationToYZ infinityParameter = yzInverseZGerm := by
  change infinityNormalizationToYZ
    (algebraMap BasePolynomial InfinityNormalization Polynomial.X) = yzInverseZGerm
  rw [infinityNormalizationToYZ.commutes]
  exact Polynomial.aeval_X _

theorem yzInfinityParameter_order :
    Ring.ord (Localization.AtPrime yzInfinityPrime)
      (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime)
        infinityParameter) = 1 :=
  parameter_order_transport yzInfinityPrime yzInfinityLocalizationEquiv.toRingEquiv
    infinityParameter yzInverseZGerm 1
    (by change yzInfinityLocalizationEquiv _ = _; rw [yzInfinityLocalizationEquiv_algebraMap, infinityNormalizationToYZ_parameter])
    yzInverseZGerm_ord_eq_one

@[simp]
theorem infinityNormalizationToZ_parameter :
    infinityNormalizationToZ infinityParameter = zWGerm := by
  change infinityNormalizationToZ
    (algebraMap BasePolynomial InfinityNormalization Polynomial.X) = zWGerm
  rw [infinityNormalizationToZ.commutes]
  exact Polynomial.aeval_X _

theorem zInfinityParameter_order :
    Ring.ord (Localization.AtPrime zInfinityPrime)
      (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime)
        infinityParameter) = 2 :=
  parameter_order_transport zInfinityPrime zInfinityLocalizationEquiv.toRingEquiv
    infinityParameter zWGerm 2
    (by change zInfinityLocalizationEquiv _ = _; rw [zInfinityLocalizationEquiv_algebraMap, infinityNormalizationToZ_parameter])
    zWGerm_ord_eq_two

theorem xInfinityPrime_ne_zInfinityPrime : xInfinityPrime ≠ zInfinityPrime := by
  intro h
  have ho := localization_order_congr h infinityParameter
  rw [xInfinityParameter_order, zInfinityParameter_order] at ho
  norm_num at ho

theorem yzInfinityPrime_ne_zInfinityPrime : yzInfinityPrime ≠ zInfinityPrime := by
  intro h
  have ho := localization_order_congr h infinityParameter
  rw [yzInfinityParameter_order, zInfinityParameter_order] at ho
  norm_num at ho

end MazurProof.N25F_InfinityParameterOrders
