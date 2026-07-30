import Mathlib.Algebra.Group.Units.Defs

/-!
# Lifting a square root of a unit

In a commutative monoid, an element whose square is a unit is itself a
unit.  This packages the elementary construction needed when a polynomial
ideal square is identified with an invertible Mumford ideal.
-/

namespace MazurProof.SquareRootUnitLift

variable {A : Type*} [CommMonoid A]

/-- If the square of `a` is a unit, retain a unit lift whose value is
literally `a` together with its square identity. -/
theorem exists_unit_val_eq_and_sq_eq
    (a : A) (u : Aˣ) (h : a ^ 2 = (u : A)) :
    ∃ v : Aˣ, (v : A) = a ∧ v ^ 2 = u := by
  have ha : IsUnit a := by
    apply isUnit_of_mul_isUnit_left
    rw [← pow_two, h]
    exact u.isUnit
  refine ⟨ha.unit, ha.unit_spec, ?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, ha.unit_spec] using h

/-- If the square of `a` is the value of a unit `u`, then `a` lifts to a
unit whose square is exactly `u`. -/
theorem exists_unit_sq_eq
    (a : A) (u : Aˣ) (h : a ^ 2 = (u : A)) :
    ∃ v : Aˣ, v ^ 2 = u := by
  obtain ⟨v, _, hv⟩ :=
    exists_unit_val_eq_and_sq_eq a u h
  exact ⟨v, hv⟩

end MazurProof.SquareRootUnitLift
