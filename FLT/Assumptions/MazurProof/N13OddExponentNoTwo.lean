import FLT.Assumptions.MazurProof.N13SymmetricSquareTwo

/-!
# Odd annihilators exclude two-torsion

The special N13 Jacobian is annihilated by `19`.  The only group-theoretic
consequence needed for uniqueness of a special half is that doubling is
injective.  This file proves that consequence for an arbitrary odd
annihilator, independently of the finite special-fibre model.
-/

namespace MazurProof.N13OddExponentNoTwo

/-- Doubling is injective on an additive commutative group annihilated by
an odd natural number. -/
theorem two_nsmul_injective_of_odd_annihilator
    {G : Type*} [AddCommGroup G]
    {m : ℕ}
    (hm : Odd m)
    (hann : ∀ z : G, m • z = 0) :
    Function.Injective (fun z : G => 2 • z) := by
  obtain ⟨k, hk⟩ := hm
  have hmk : m + 1 = 2 * (k + 1) := by
    omega
  intro x y hxy
  have hx : (m + 1) • x = x := by
    rw [add_nsmul, hann x]
    simp
  have hy : (m + 1) • y = y := by
    rw [add_nsmul, hann y]
    simp
  calc
    x = (m + 1) • x := hx.symm
    _ = (k + 1) • (2 • x) := by
      rw [hmk]
      exact mul_nsmul x 2 (k + 1)
    _ = (k + 1) • (2 • y) := by
      exact congrArg (fun z : G => (k + 1) • z) hxy
    _ = (m + 1) • y := by
      rw [hmk]
      exact (mul_nsmul y 2 (k + 1)).symm
    _ = y := hy

/-- Concrete form used by the N13 special Jacobian. -/
theorem two_nsmul_injective_of_exponent_nineteen
    {G : Type*} [AddCommGroup G]
    (h19 : ∀ z : G, 19 • z = 0) :
    Function.Injective (fun z : G => 2 • z) :=
  two_nsmul_injective_of_odd_annihilator
    (m := 19) (by norm_num) h19

/-- A class killed by both two and nineteen is zero. -/
theorem eq_zero_of_two_nsmul_eq_zero_of_exponent_nineteen
    {G : Type*} [AddCommGroup G]
    (h19 : ∀ z : G, 19 • z = 0)
    {z : G}
    (hz : 2 • z = 0) :
    z = 0 := by
  apply two_nsmul_injective_of_exponent_nineteen h19
  simpa using hz

/-- Two halves of the same class are equal in a group of exponent
dividing nineteen. -/
theorem eq_of_two_nsmul_eq_two_nsmul_of_exponent_nineteen
    {G : Type*} [AddCommGroup G]
    (h19 : ∀ z : G, 19 • z = 0)
    {x y : G}
    (hxy : 2 • x = 2 • y) :
    x = y :=
  two_nsmul_injective_of_exponent_nineteen h19 hxy

/-- The structural Abel-fibre count supplies the exponent-nineteen
hypothesis and hence injectivity of doubling on the actual special
Jacobian. -/
theorem specialJacobian_two_nsmul_injective
    {J : Type*} [AddCommGroup J] [Finite J]
    (D : N13SymmetricSquareTwo.AbelFiberData J) :
    Function.Injective (fun z : J => 2 • z) :=
  two_nsmul_injective_of_exponent_nineteen
    (N13SymmetricSquareTwo.jacobian_exponent_nineteen D)

/-- Uniqueness of a half on the special N13 Jacobian. -/
theorem specialJacobian_half_unique
    {J : Type*} [AddCommGroup J] [Finite J]
    (D : N13SymmetricSquareTwo.AbelFiberData J)
    {a x y : J}
    (hx : 2 • x = a)
    (hy : 2 • y = a) :
    x = y := by
  apply specialJacobian_two_nsmul_injective D
  exact hx.trans hy.symm

end MazurProof.N13OddExponentNoTwo
