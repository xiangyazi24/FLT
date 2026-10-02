import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryCenters
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras
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

open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityBoundaryCenters N25F_InfinityBoundaryAlgebras
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra

/-- The reciprocal-coordinate prime in the polynomial base. -/
def infinityBasePrime : Ideal BasePolynomial := Ideal.span {Polynomial.X}

instance infinityBasePrime_isMaximal : infinityBasePrime.IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X


theorem xInfinityPrime_under :
    xInfinityPrime.under BasePolynomial = infinityBasePrime :=
  contraction_eq_span_X xInfinityPrime infinityParameter_mem_xInfinityPrime

instance xInfinityPrime_liesOver : xInfinityPrime.LiesOver infinityBasePrime :=
  ⟨xInfinityPrime_under.symm⟩

theorem yzInfinityPrime_under :
    yzInfinityPrime.under BasePolynomial = infinityBasePrime :=
  contraction_eq_span_X yzInfinityPrime infinityParameter_mem_yzInfinityPrime

instance yzInfinityPrime_liesOver : yzInfinityPrime.LiesOver infinityBasePrime :=
  ⟨yzInfinityPrime_under.symm⟩

theorem zInfinityPrime_under :
    zInfinityPrime.under BasePolynomial = infinityBasePrime :=
  contraction_eq_span_X zInfinityPrime infinityParameter_mem_zInfinityPrime

instance zInfinityPrime_liesOver : zInfinityPrime.LiesOver infinityBasePrime :=
  ⟨zInfinityPrime_under.symm⟩

end MazurProof.N25F_InfinityPrimeContraction
