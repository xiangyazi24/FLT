import FLT.Assumptions.MazurProof.N25F_WChartNormDimension
import FLT.Assumptions.MazurProof.N25F_ZChartFractionMap
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneQuarticFunctionField

/-! The actual W chart has rank four over F₂[z]. Its norm and quotient
length on base polynomials are consequently the fourth power and four
times degree. This is the affine half of the base-polynomial product formula. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_NonBoundaryPrincipalDivisor

open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneQuarticFunctionField
open RationalPointsN25QuotientTwoWChartNormalization
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_ZChartFractionMap

/-- The existing polynomial-base module has rank four, inherited from the
already constructed common plane function field. -/
theorem wChart_finrank_polynomial_eq_four :
    Module.finrank (Polynomial (ZMod 2)) W = 4 := by
  letI : Algebra.IsAlgebraic (Polynomial (ZMod 2)) W :=
    Algebra.IsAlgebraic.of_finite _ _
  rw [← Algebra.IsAlgebraic.finrank_of_isFractionRing
    (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) W PlaneFunctionField]
  exact planeFunctionField_finrank

/-- Norm on the actual polynomial base is fourth power. -/
theorem wChart_norm_algebraMap_eq_pow_four (p : Polynomial (ZMod 2)) :
    Algebra.norm (Polynomial (ZMod 2))
      (algebraMap (Polynomial (ZMod 2)) W p) = p ^ 4 := by
  letI : Module.Free (Polynomial (ZMod 2)) W :=
    Module.free_of_finite_type_torsion_free'
  rw [Algebra.norm_algebraMap, wChart_finrank_polynomial_eq_four]

/-- The actual base polynomial p(z) has affine zero-scheme dimension
four times its polynomial degree. -/
theorem wChart_quotient_finrank_base_polynomial
    (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    Module.finrank (ZMod 2)
      (W ⧸ Ideal.span ({algebraMap (Polynomial (ZMod 2)) W p} : Set W)) =
      4 * p.natDegree := by
  have hmap : algebraMap (Polynomial (ZMod 2)) W p ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (Polynomial (ZMod 2)) W)).mpr hp
  rw [wChart_quotient_finrank_eq_natDegree_norm _ hmap,
    wChart_norm_algebraMap_eq_pow_four, Polynomial.natDegree_pow]

end MazurProof.N25F_NonBoundaryPrincipalDivisor
