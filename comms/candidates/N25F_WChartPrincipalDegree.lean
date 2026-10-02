import FLT.Assumptions.MazurProof.N25F_WChartQuotientFinite
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree
import FLT.Assumptions.MazurProof.N25F_PrincipalDivisorQuotientDegree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazurProof.N25F_NonBoundaryPrincipalDivisor

open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_ProjectiveDivisorSplit
open N25F_ProjectiveDivisorDegree

/-- The affine degree of the existing principal divisor of the same nonzero
regular W-chart function is its binary quotient dimension. -/
theorem wChart_principal_degree_eq_quotient_finrank
    (a : W) (ha : a ≠ 0)
    (f : Additive ((FractionRing W)ˣ))
    (hf : (f.toMul : FractionRing W) = algebraMap W (FractionRing W) a) :
    wChartDivisorDegree
        (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) =
      (Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) : ℤ) := by
  classical
  haveI : Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) :=
    wChart_quotient_finite a ha
  have hweight (v : WHeightOne) :
      wChartMaximalIdealDegree
          (fullNonBoundaryAtomEquivMaximalIdeal (fullNonBoundaryAtomEquivHeightOne.symm v)) =
        Module.finrank (ZMod 2) (W ⧸ v.asIdeal) := by
    change Module.finrank (ZMod 2)
      (W ⧸ (fullNonBoundaryAtomEquivHeightOne
        (fullNonBoundaryAtomEquivHeightOne.symm v)).asIdeal) = _
    rw [Equiv.apply_symm_apply]
  rw [wChartDivisorDegree_apply]
  change (Finsupp.equivMapDomain fullNonBoundaryAtomEquivMaximalIdeal
    (Finsupp.equivMapDomain fullNonBoundaryAtomEquivHeightOne.symm
      (CurveDedekindDivisor.principalDivisor f))).sum
        (fun m n => n * (wChartMaximalIdealDegree m : ℤ)) = _
  rw [Finsupp.sum_equivMapDomain, Finsupp.sum_equivMapDomain]
  calc
    _ = (CurveDedekindDivisor.principalDivisor f).sum
        (fun v n => n * (Module.finrank (ZMod 2) (W ⧸ v.asIdeal) : ℤ)) := by
      apply Finsupp.sum_congr
      intro v hv
      rw [hweight v]
    _ = _ := CurveDedekindDivisor.principalDivisor_degree_eq_quotient_finrank
      (ZMod 2) a ha f hf

end MazurProof.N25F_NonBoundaryPrincipalDivisor
