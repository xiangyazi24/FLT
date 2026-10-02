import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Order of vanishing is preserved by a ring equivalence, including the
length change of scalars. This will compare the identified boundary DVRs. -/
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
