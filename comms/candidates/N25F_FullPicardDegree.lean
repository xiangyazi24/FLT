import FLT.Assumptions.MazurProof.N25F_ProjectiveProductFormula
import FLT.Assumptions.MazurProof.CurveDivisorPicard

/-! The actual principal subgroup and descended class degree on the full
closed-point divisor group. No truncation to low-degree closed points is used. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_FullPicardDegree
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectivePrincipalDivisor N25F_ProjectiveProductFormula
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The actual principal divisors, as the image of the established map on
all nonzero functions in the fixed curve field. -/
def fullProjectivePrincipalSubgroup25Two : AddSubgroup fullClosedPointGrading25Two.Divisor :=
  projectivePrincipalDivisor.range

/-- The genuine principal subgroup satisfies the existing Picard degree-descent input. -/
theorem fullProjectivePrincipalSubgroup25Two_le_degree_ker :
    fullProjectivePrincipalSubgroup25Two ≤ fullClosedPointGrading25Two.divisorDegree.ker := by
  rintro D ⟨f, rfl⟩
  change fullClosedPointGrading25Two.divisorDegree (projectivePrincipalDivisor f) = 0
  exact projectivePrincipalDivisor_degree_eq_zero f

/-- Degree on the actual full divisor-class quotient, with its principal
degree-zero requirement discharged by the product formula. -/
def fullProjectiveClassDegree25Two :
    fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two →+ ℤ :=
  fullClosedPointGrading25Two.classDegree fullProjectivePrincipalSubgroup25Two
    fullProjectivePrincipalSubgroup25Two_le_degree_ker

@[simp]
theorem fullProjectiveClassDegree25Two_classOf (D : fullClosedPointGrading25Two.Divisor) :
    fullProjectiveClassDegree25Two
      (fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D) =
      fullClosedPointGrading25Two.divisorDegree D := rfl

/-- Equality in the concrete full Picard quotient means that the difference
is the divisor of an actual nonzero function in the fixed curve field. -/
theorem fullProjectiveClassOf_eq_iff_exists_principal
    (D E : fullClosedPointGrading25Two.Divisor) :
    fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D =
      fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two E ↔
      ∃ f : Additive CurveFieldˣ, projectivePrincipalDivisor f = D - E := by
  change ((D : fullClosedPointGrading25Two.Divisor ⧸ fullProjectivePrincipalSubgroup25Two) = E) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl

end MazurProof.N25F_FullPicardDegree
