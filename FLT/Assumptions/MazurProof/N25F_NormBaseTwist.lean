import Mathlib.RingTheory.Norm.Basic

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
