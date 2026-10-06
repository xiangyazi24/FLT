import FLT.Assumptions.MazurProof.N25F_InfinityNormBoundarySum
import FLT.Assumptions.MazurProof.N25F_BaseInversionOrder
import FLT.Assumptions.MazurProof.N25F_AffineNormPolynomial
import FLT.Assumptions.MazurProof.N25F_WChartNormDimension
import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalDivisor
import Lean.Elab.Tactic.Omega

/-! The constructed genuine projective principal divisor has degree zero
for every nonzero function in the fixed W-chart function field. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ProjectiveProductFormula

private theorem hom_zero_of_regular {R L : Type*} [CommRing R] [IsDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (D : Additive Lˣ →+ ℤ)
    (h : ∀ (a : R) (ha : a ≠ 0), D (Additive.ofMul (Units.mk0
      (algebraMap R L a) ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr ha))) = 0)
    (f : Additive Lˣ) : D f = 0 := by
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective R (f.toMul : L)
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [map_zero, zero_div] at heq
    exact (Units.ne_zero f.toMul) heq.symm
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let fa : Additive Lˣ := Additive.ofMul (Units.mk0 (algebraMap R L a)
    ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr ha))
  let fb : Additive Lˣ := Additive.ofMul (Units.mk0 (algebraMap R L b)
    ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hb'))
  have hf : f = fa - fb := by
    apply Additive.toMul.injective
    apply Units.ext
    simpa [fa, fb] using heq.symm
  rw [hf, map_sub, h a ha, h b hb', sub_self]

open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityPrimeContraction N25F_InfinityNormBoundarySum
open N25F_InfinityAffineNormComparison N25F_BaseInversionOrder N25F_AffineNormPolynomial
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit N25F_ProjectiveDivisorDegree
open N25F_ProjectivePrincipalDivisor
open N25F_XBoundaryOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open RationalPointsN25QuotientTwoFullClosedPoints
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
attribute [local instance] infinityRationalAlgebra

/-- Degree zero for every nonzero regular W-chart function, with its actual
boundary poles and affine zeros computed from the same field norm. -/
theorem projectivePrincipalDivisor_degree_regular
    (a : W) (ha : a ≠ 0) (f : Additive CurveFieldˣ)
    (hf : (f.toMul : CurveField) = algebraMap W CurveField a) :
    fullClosedPointGrading25Two.divisorDegree (projectivePrincipalDivisor f) = 0 := by
  letI : Module.Free BasePolynomial W := Module.free_of_finite_type_torsion_free'
  have hn : Algebra.norm BasePolynomial a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have hsum := infinity_norm_boundary_order_sum f
  rw [hf, infinity_norm_eq_baseInversion_affine_norm, affineFieldNorm_algebraMap] at hsum
  change WithZero.log (Ring.ordFrac (Localization.AtPrime infinityBasePrime)
    (baseInversion.symm (algebraMap BasePolynomial BaseField (Algebra.norm BasePolynomial a)))) =
      xBoundaryOrder f + yzBoundaryOrder f + zBoundaryOrder f at hsum
  rw [baseInversion_polynomial_order _ hn] at hsum
  have haff := wChart_principal_degree_eq_quotient_finrank a ha f hf
  rw [wChart_quotient_finrank_eq_natDegree_norm a ha] at haff
  rw [projectivePrincipalDivisor_degree, ← hsum, haff]
  exact neg_add_cancel _

/-- The actual projective principal divisor of every nonzero function has
degree zero. The fraction representation extends the regular-function case. -/
theorem projectivePrincipalDivisor_degree_eq_zero (f : Additive CurveFieldˣ) :
    fullClosedPointGrading25Two.divisorDegree (projectivePrincipalDivisor f) = 0 :=
  hom_zero_of_regular (R := W)
    (fullClosedPointGrading25Two.divisorDegree.comp projectivePrincipalDivisor)
    (fun a ha => projectivePrincipalDivisor_degree_regular a ha _ rfl) f

end MazurProof.N25F_ProjectiveProductFormula
