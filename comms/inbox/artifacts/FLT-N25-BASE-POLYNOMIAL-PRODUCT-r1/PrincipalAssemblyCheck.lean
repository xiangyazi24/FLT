import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25PrincipalAssemblyCheck
variable {U P C : Type*} [AddCommGroup U] [AddCommGroup P] [AddCommGroup C]
variable (e : P ≃+ ((ℤ × (ℤ × ℤ)) × C))
variable (x y z : U →+ ℤ) (a : U →+ C)

def principal : U →+ P :=
  e.symm.toAddMonoidHom.comp ((x.prod (y.prod z)).prod a)

theorem split (f : U) :
    e (principal e x y z a f) = ((x f, (y f, z f)), a f) := by
  change e (e.symm _) = _
  exact e.apply_symm_apply _

theorem degree_base (d : P →+ ℤ) (dc : C →+ ℤ)
    (hd : ∀ t, d (e.symm t) = t.1.1 + t.1.2.1 + t.1.2.2 + dc t.2)
    (f : U) (n : ℕ)
    (hx : x f = -(1 * n : ℤ)) (hy : y f = -(1 * n : ℤ))
    (hz : z f = -(2 * n : ℤ)) (ha : dc (a f) = (4 * n : ℕ)) :
    d (principal e x y z a f) = 0 := by
  change d (e.symm ((x f, (y f, z f)), a f)) = _
  rw [hd, hx, hy, hz, ha]
  push_cast
  ring

#print axioms principal
#print axioms split
#print axioms degree_base
end N25PrincipalAssemblyCheck
