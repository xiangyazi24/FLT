import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Defs
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25TwistedBaseCheck

theorem finite_finrank_twist
    {B L : Type*} [Field B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (e : B ≃+* B) :
    let n := Module.finrank B L
    letI : Algebra B L := ((algebraMap B L).comp e.toRingHom).toAlgebra
    Module.Finite B L ∧ Module.finrank B L = n := by
  let n := Module.finrank B L
  let φ := algebraMap B L
  let oldModule : Module B L := inferInstance
  let b := Module.finBasis B L
  have hsmul (c : B) (x : L) : c • x = φ c * x := Algebra.smul_def c x
  let newAlgebra : Algebra B L := (φ.comp e.toRingHom).toAlgebra
  letI : Algebra B L := newAlgebra
  let newModule : Module B L := @Algebra.toModule B L _ _ newAlgebra
  letI : Module B L := newModule
  let b' : @Module.Basis (Fin n) B L _ _ newModule :=
    @Module.Basis.mapCoeffs (Fin n) B L _ _ oldModule b B _ newModule e.symm (by
    intro c x
    rw [hsmul]
    change φ (e (e.symm c)) * x = φ c * x
    rw [e.apply_symm_apply])
  exact ⟨b'.finiteDimensional_of_finite, by simpa using Module.finrank_eq_card_basis b'⟩

#print axioms finite_finrank_twist
end N25TwistedBaseCheck
