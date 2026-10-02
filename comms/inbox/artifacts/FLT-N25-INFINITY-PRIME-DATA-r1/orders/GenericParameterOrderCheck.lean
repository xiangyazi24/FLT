import Mathlib.RingTheory.Localization.AtPrime.Basic
import N25F_OrderRingEquiv

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

#print axioms parameter_order_transport
#print axioms localization_order_congr
end MazurProof.N25F_InfinityParameterOrders
