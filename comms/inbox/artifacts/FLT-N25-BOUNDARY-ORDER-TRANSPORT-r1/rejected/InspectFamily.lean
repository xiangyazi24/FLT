import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! The signed length order of a fraction is the difference of the finite
length orders of its nonzero numerator and denominator. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_FractionOrderDifference

/-- Compute the genuine signed fraction-field order using quotient lengths. -/
theorem log_ordFrac_div {R L : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R L a / algebraMap R L b)) =
      ((Ring.ord R a).toNat : ℤ) - ((Ring.ord R b).toNat : ℤ) := by
  have he (c : R) (hc : c ≠ 0) :
      Ring.ordFrac R (algebraMap R L c) =
        WithZero.exp ((Ring.ord R c).toNat : ℤ) := by
    have hc' : c ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr hc
    rw [Ring.ordFrac_eq_ord R hc,
      Ring.ordMonoidWithZeroHom_eq_coe R hc'
        (ENat.coe_toNat (Ring.ord_ne_top hc')).symm]
    rfl
  rw [map_div₀, he a ha, he b hb, ← WithZero.exp_sub, WithZero.log_exp]

end MazurProof.N25F_FractionOrderDifference

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_OrderRingEquiv

/-- Ring length order is invariant under the actual local-ring equivalence. -/
theorem ord_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let e' : R ≃ₐ[R] S := { e with commutes' := fun _ => rfl }
  let q := Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) e'
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  change Module.length S (S ⧸ Ideal.span {e a}) = Module.length R (R ⧸ Ideal.span {a})
  rw [← Module.length_eq_of_surjective (S := R) (R := S)
    (M := S ⧸ Ideal.span {e a}) e.surjective]
  exact q.toLinearEquiv.length_eq.symm

end MazurProof.N25F_OrderRingEquiv

namespace MazurProof.N25F_InfinityBoundaryOrderTransport
open N25F_OrderRingEquiv N25F_FractionOrderDifference

section X
variable {N R L : Type*} [CommRing N] [IsDedekindDomain N]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra N L] [Algebra N R] [Algebra R L] [IsFractionRing R L]
local notation "infinityNormalizationToX" => algebraMap N R
local notation "xLocalToFraction" => algebraMap R L
variable (infinityNormalizationToX_injective : Function.Injective (algebraMap N R))
variable (xLocalToFraction_infinityNormalizationToX : ∀ a : N,
  xLocalToFraction (infinityNormalizationToX a) = algebraMap N L a)
variable (xInfinityPrime : Ideal N) [xInfinityPrime.IsPrime]
variable (xInfinityLocalizationEquiv : Localization.AtPrime xInfinityPrime ≃ₐ[N] R)
local notation "InfinityNormalization" => N
local notation "XLocalRing" => R
local notation "CurveField" => L
local notation "xLocalFractionOrder" => Ring.ordFrac R (K := L)
local notation "xBoundaryOrder" => fun f : Additive Lˣ => WithZero.log (Ring.ordFrac R ((Additive.toMul f : Lˣ) : L))
omit [IsDedekindDomain N] [IsDomain R] [IsDiscreteValuationRing R] in
private theorem xInfinityLocalizationEquiv_algebraMap (a : N) :
  xInfinityLocalizationEquiv (algebraMap N (Localization.AtPrime xInfinityPrime) a) = infinityNormalizationToX a :=
  xInfinityLocalizationEquiv.commutes a
include xInfinityLocalizationEquiv in
/-- The actual X boundary quotient length equals the normalization-local one. -/
theorem xInfinityNormalization_order (a : InfinityNormalization) :
    Ring.ord XLocalRing (infinityNormalizationToX a) =
      Ring.ord (Localization.AtPrime xInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a) := by
  have h := ord_map_ringEquiv xInfinityLocalizationEquiv.toRingEquiv
    (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a)
  change Ring.ord XLocalRing (xInfinityLocalizationEquiv _) = _ at h
  rw [xInfinityLocalizationEquiv_algebraMap xInfinityPrime xInfinityLocalizationEquiv] at h
  exact h

include infinityNormalizationToX_injective xLocalToFraction_infinityNormalizationToX xInfinityLocalizationEquiv in
/-- The existing signed X boundary coefficient of a normalization fraction. -/
theorem xBoundaryOrder_normalization_fraction
    (a b : InfinityNormalization) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) = (algebraMap N L a) / (algebraMap N L b)) :
    xBoundaryOrder f =
      ((Ring.ord (Localization.AtPrime xInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a)).toNat : ℤ) -
      ((Ring.ord (Localization.AtPrime xInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) b)).toNat : ℤ) := by
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
    xInfinityNormalization_order xInfinityPrime xInfinityLocalizationEquiv, xInfinityNormalization_order xInfinityPrime xInfinityLocalizationEquiv]

end X

section YZ
variable {N R L : Type*} [CommRing N] [IsDedekindDomain N]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra N L] [Algebra N R] [Algebra R L] [IsFractionRing R L]
local notation "infinityNormalizationToYZ" => algebraMap N R
local notation "yzLocalToFraction" => algebraMap R L
variable (infinityNormalizationToYZ_injective : Function.Injective (algebraMap N R))
variable (yzLocalToFraction_infinityNormalizationToYZ : ∀ a : N,
  yzLocalToFraction (infinityNormalizationToYZ a) = algebraMap N L a)
variable (yzInfinityPrime : Ideal N) [yzInfinityPrime.IsPrime]
variable (yzInfinityLocalizationEquiv : Localization.AtPrime yzInfinityPrime ≃ₐ[N] R)
local notation "InfinityNormalization" => N
local notation "YZLocalRing" => R
local notation "CurveField" => L
local notation "yzLocalFractionOrder" => Ring.ordFrac R (K := L)
local notation "yzBoundaryOrder" => fun f : Additive Lˣ => WithZero.log (Ring.ordFrac R ((Additive.toMul f : Lˣ) : L))
omit [IsDedekindDomain N] [IsDomain R] [IsDiscreteValuationRing R] in
private theorem yzInfinityLocalizationEquiv_algebraMap (a : N) :
  yzInfinityLocalizationEquiv (algebraMap N (Localization.AtPrime yzInfinityPrime) a) = infinityNormalizationToYZ a :=
  yzInfinityLocalizationEquiv.commutes a
include yzInfinityLocalizationEquiv in
/-- The actual YZ boundary quotient length equals the normalization-local one. -/
theorem yzInfinityNormalization_order (a : InfinityNormalization) :
    Ring.ord YZLocalRing (infinityNormalizationToYZ a) =
      Ring.ord (Localization.AtPrime yzInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a) := by
  have h := ord_map_ringEquiv yzInfinityLocalizationEquiv.toRingEquiv
    (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a)
  change Ring.ord YZLocalRing (yzInfinityLocalizationEquiv _) = _ at h
  rw [yzInfinityLocalizationEquiv_algebraMap yzInfinityPrime yzInfinityLocalizationEquiv] at h
  exact h

include infinityNormalizationToYZ_injective yzLocalToFraction_infinityNormalizationToYZ yzInfinityLocalizationEquiv in
/-- The existing signed YZ boundary coefficient of a normalization fraction. -/
theorem yzBoundaryOrder_normalization_fraction
    (a b : InfinityNormalization) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) = (algebraMap N L a) / (algebraMap N L b)) :
    yzBoundaryOrder f =
      ((Ring.ord (Localization.AtPrime yzInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a)).toNat : ℤ) -
      ((Ring.ord (Localization.AtPrime yzInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) b)).toNat : ℤ) := by
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
    yzInfinityNormalization_order yzInfinityPrime yzInfinityLocalizationEquiv, yzInfinityNormalization_order yzInfinityPrime yzInfinityLocalizationEquiv]

end YZ

section Z
variable {N R L : Type*} [CommRing N] [IsDedekindDomain N]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra N L] [Algebra N R] [Algebra R L] [IsFractionRing R L]
local notation "infinityNormalizationToZ" => algebraMap N R
local notation "zLocalToFraction" => algebraMap R L
variable (infinityNormalizationToZ_injective : Function.Injective (algebraMap N R))
variable (zLocalToFraction_infinityNormalizationToZ : ∀ a : N,
  zLocalToFraction (infinityNormalizationToZ a) = algebraMap N L a)
variable (zInfinityPrime : Ideal N) [zInfinityPrime.IsPrime]
variable (zInfinityLocalizationEquiv : Localization.AtPrime zInfinityPrime ≃ₐ[N] R)
local notation "InfinityNormalization" => N
local notation "ZLocalRing" => R
local notation "CurveField" => L
local notation "zLocalFractionOrder" => Ring.ordFrac R (K := L)
local notation "zBoundaryOrder" => fun f : Additive Lˣ => WithZero.log (Ring.ordFrac R ((Additive.toMul f : Lˣ) : L))
omit [IsDedekindDomain N] [IsDomain R] [IsDiscreteValuationRing R] in
private theorem zInfinityLocalizationEquiv_algebraMap (a : N) :
  zInfinityLocalizationEquiv (algebraMap N (Localization.AtPrime zInfinityPrime) a) = infinityNormalizationToZ a :=
  zInfinityLocalizationEquiv.commutes a
include zInfinityLocalizationEquiv in
/-- The actual Z boundary quotient length equals the normalization-local one. -/
theorem zInfinityNormalization_order (a : InfinityNormalization) :
    Ring.ord ZLocalRing (infinityNormalizationToZ a) =
      Ring.ord (Localization.AtPrime zInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a) := by
  have h := ord_map_ringEquiv zInfinityLocalizationEquiv.toRingEquiv
    (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a)
  change Ring.ord ZLocalRing (zInfinityLocalizationEquiv _) = _ at h
  rw [zInfinityLocalizationEquiv_algebraMap zInfinityPrime zInfinityLocalizationEquiv] at h
  exact h

include infinityNormalizationToZ_injective zLocalToFraction_infinityNormalizationToZ zInfinityLocalizationEquiv in
/-- The existing signed Z boundary coefficient of a normalization fraction. -/
theorem zBoundaryOrder_normalization_fraction
    (a b : InfinityNormalization) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) = (algebraMap N L a) / (algebraMap N L b)) :
    zBoundaryOrder f =
      ((Ring.ord (Localization.AtPrime zInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a)).toNat : ℤ) -
      ((Ring.ord (Localization.AtPrime zInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) b)).toNat : ℤ) := by
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
    zInfinityNormalization_order zInfinityPrime zInfinityLocalizationEquiv, zInfinityNormalization_order zInfinityPrime zInfinityLocalizationEquiv]

end Z

#print axioms MazurProof.N25F_FractionOrderDifference.log_ordFrac_div
#print axioms xInfinityNormalization_order
#print axioms xBoundaryOrder_normalization_fraction
#print axioms yzInfinityNormalization_order
#print axioms yzBoundaryOrder_normalization_fraction
#print axioms zInfinityNormalization_order
#print axioms zBoundaryOrder_normalization_fraction
end MazurProof.N25F_InfinityBoundaryOrderTransport

#print MazurProof.N25F_InfinityBoundaryOrderTransport.xBoundaryOrder_normalization_fraction
