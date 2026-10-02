import Mathlib.FieldTheory.Separable
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25SeparableTwistCheck

theorem separable_twist {B L : Type*} [Field B] [Field L]
    [Algebra B L] [Algebra.IsSeparable B L] (e : B ≃+* B) :
    letI : Algebra B L := ((algebraMap B L).comp e.toRingHom).toAlgebra
    Algebra.IsSeparable B L := by
  let oldAlgebra : Algebra B L := inferInstance
  let φ := algebraMap B L
  let newAlgebra : Algebra B L := (φ.comp e.toRingHom).toAlgebra
  have hs : @Algebra.IsSeparable B L _ _ oldAlgebra := inferInstance
  exact @Algebra.IsSeparable.of_equiv_equiv B L B L _ _ _ _ oldAlgebra newAlgebra
    e.symm (RingEquiv.refl L) (by
      ext b
      change φ (e (e.symm b)) = φ b
      rw [e.apply_symm_apply]) hs

#print axioms separable_twist
end N25SeparableTwistCheck
