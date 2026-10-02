import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.OrderOfVanishing.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityRamificationIndices

/-- A principal contracted prime computes ramification by the actual order
of its parameter in the source localization. -/
theorem ramificationIdx_eq_of_parameter_order {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (q : Ideal B) [q.IsPrime] (a : A) (n : ℕ)
    (hunder : q.under A = Ideal.span {a})
    (horder : Ring.ord (Localization.AtPrime q)
      (algebraMap B (Localization.AtPrime q) (algebraMap A B a)) = n) :
    q.ramificationIdx' A = n := by
  rw [Ideal.ramificationIdx'_def, hunder, Ideal.map_span, Set.image_singleton]
  change (Ring.ord (Localization.AtPrime q)
    (algebraMap A (Localization.AtPrime q) a)).toNat = n
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q), horder]
  exact ENat.toNat_coe n

#print axioms ramificationIdx_eq_of_parameter_order
end MazurProof.N25F_InfinityRamificationIndices
