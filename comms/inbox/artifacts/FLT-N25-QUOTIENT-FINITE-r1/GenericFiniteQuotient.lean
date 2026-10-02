import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Zero

set_option autoImplicit false
set_option relaxedAutoImplicit false

section

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] [Ring.DimensionLEOne A]

/-- A nonzero ideal in a finite-type algebra of dimension at most one
has a finite-dimensional quotient over its ground field. -/
theorem finite_quotient_of_ne_bot
    (I : Ideal A) (hI : I ≠ ⊥) : Module.Finite k (A ⧸ I) := by
  apply (Module.finite_iff_krullDimLE_zero k (A ⧸ I)).2
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  exact hP.1.1.isMaximal (ne_bot_of_le_ne_bot hI hP.1.2)

end


#print axioms finite_quotient_of_ne_bot

section
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] [Ring.DimensionLEOne A]

theorem finite_principal_quotient_checked (a : A) (ha : a ≠ 0) :
    Module.Finite k (A ⧸ Ideal.span ({a} : Set A)) := by
  exact finite_quotient_of_ne_bot _ (Ideal.span_singleton_eq_bot.not.mpr ha)
#print axioms finite_principal_quotient_checked
end
