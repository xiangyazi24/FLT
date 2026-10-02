import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Data.ZMod.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityPrimeContraction

/-- A prime containing the polynomial parameter lies over its principal prime. -/
theorem contraction_eq_span_X {k A : Type*} [Field k] [CommRing A]
    [Algebra (Polynomial k) A] (p : Ideal A) [p.IsPrime]
    (hX : algebraMap (Polynomial k) A Polynomial.X ∈ p) :
    p.comap (algebraMap (Polynomial k) A) = Ideal.span {Polynomial.X} := by
  have hmax : (Ideal.span {(Polynomial.X : Polynomial k)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hprime : (p.comap (algebraMap (Polynomial k) A)).IsPrime := inferInstance
  exact (hmax.eq_of_le hprime.ne_top
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))).symm

example {k A : Type*} [Field k] [CommRing A] [Algebra (Polynomial k) A]
    (p : Ideal A) [p.IsPrime] (hX : algebraMap (Polynomial k) A Polynomial.X ∈ p) :
    p.LiesOver (Ideal.span {(Polynomial.X : Polynomial k)}) where
  over := (contraction_eq_span_X p hX).symm

#print axioms contraction_eq_span_X
end MazurProof.N25F_InfinityPrimeContraction
