import FLT.Assumptions.MazurProof.N25F_WBasisPoleBound
import FLT.Assumptions.MazurProof.N25F_RiemannRochSpace
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree

/-! The fixed actual W basis lies in one uniformly bounded-pole section space.
All nonboundary conditions are proved from integral ideal multiplicities. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_WBasisPoleSections
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
open N25F_ProjectiveDivisorDegree N25F_RiemannRochSpace N25F_WBasisPoleBound
open N25F_XBoundaryOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
local notation "K" => FractionRing W

/-- The actual pole-weight divisor of the established base coordinate Z/W. -/
def basePoleDivisor25Two : ProjectiveDivisor25Two :=
  Finsupp.single (fullBoundaryAtomOfTag .X) 1 +
    Finsupp.single (fullBoundaryAtomOfTag .YZ) 1 +
      Finsupp.single (fullBoundaryAtomOfTag .Z) 2

theorem basePoleDivisor25Two_degree :
    fullClosedPointGrading25Two.divisorDegree basePoleDivisor25Two = 4 := by
  unfold basePoleDivisor25Two
  rw [map_add, map_add]
  simp [ClosedPointGrading.divisorDegree]

private theorem basePoleDivisor_apply_boundary (t : FullBoundaryTag25Two) :
    basePoleDivisor25Two (fullBoundaryAtomOfTag t) =
      match t with | .X => 1 | .YZ => 1 | .Z => 2 := by
  cases t <;> simp [basePoleDivisor25Two, fullBoundaryAtomOfTag_injective.eq_iff]

private theorem basePoleDivisor_apply_nonBoundary (A : FullNonBoundaryAtom25Two) :
    basePoleDivisor25Two A.1 = 0 := by
  have hn (t : FullBoundaryTag25Two) : fullBoundaryAtomOfTag t ≠ A.1 := by
    intro h
    exact A.2 (h ▸ fullBoundaryAtomOfTag_isFullBoundaryAtom t)
  simp [basePoleDivisor25Two, Ne.symm (hn .X), Ne.symm (hn .YZ), Ne.symm (hn .Z)]

/-- An actual regular W function satisfying the three boundary bounds belongs
to the genuine full section space; no affine positivity premise is assumed. -/
theorem regular_function_mem_basePole_space (n : ℕ) (a : W) (ha : a ≠ 0)
    (f : Additive Kˣ) (hf : (f.toMul : K) = algebraMap W K a)
    (hx : -(n : ℤ) ≤ xBoundaryOrder f)
    (hyz : -(n : ℤ) ≤ yzBoundaryOrder f)
    (hz : -(2 * (n : ℤ)) ≤ zBoundaryOrder f) :
    (f.toMul : K) ∈ fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two) := by
  classical
  refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
  have hunit : Additive.ofMul (Units.mk0 (f.toMul : K) f.toMul.ne_zero) = f := by
    apply Additive.toMul.injective
    exact Units.ext rfl
  intro A
  rw [hunit, Finsupp.smul_apply, smul_eq_mul]
  by_cases hA : IsFullBoundaryAtom A
  · obtain ⟨t, rfl⟩ := (isFullBoundaryAtom_iff_exists_fullBoundaryTag A).mp hA
    rw [basePoleDivisor_apply_boundary]
    cases t with
    | X => rw [projectivePrincipalDivisor_apply_X]; simp only [mul_one]; omega
    | YZ => rw [projectivePrincipalDivisor_apply_YZ]; simp only [mul_one]; omega
    | Z =>
        rw [projectivePrincipalDivisor_apply_Z]
        change 0 ≤ (n : ℤ) * 2 + zBoundaryOrder f
        omega
  · let B : FullNonBoundaryAtom25Two := ⟨A, hA⟩
    have hb : basePoleDivisor25Two A = 0 := basePoleDivisor_apply_nonBoundary B
    rw [hb, mul_zero, zero_add]
    rw [projectivePrincipalDivisor_apply_nonBoundary f B, nonBoundaryPrincipalDivisor_apply,
      CurveDedekindDivisor.principalDivisor_regular_apply a ha f hf]
    exact Int.natCast_nonneg _

/-- Every element of the one fixed polynomial basis lies in L(B H), with
one constant B independent of every divisor class or representative. -/
theorem wPolynomialBasis_mem_uniform_section_space (i : Fin 4) :
    algebraMap W K (wPolynomialBasis25Two i) ∈
      fullRiemannRochSpace25Two
        ((wPolynomialBasisPoleBound25Two : ℤ) • basePoleDivisor25Two) := by
  obtain ⟨hx, hyz, hz⟩ := wPolynomialBasis_boundary_orders_bounded i
  exact regular_function_mem_basePole_space wPolynomialBasisPoleBound25Two
    (wPolynomialBasis25Two i) (wPolynomialBasis25Two_ne_zero i)
    (wPolynomialBasisFunction25Two i) rfl hx hyz hz

end MazurProof.N25F_WBasisPoleSections
