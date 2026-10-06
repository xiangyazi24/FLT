import FLT.Assumptions.MazurProof.N25F_SectionPrincipalTransport
import FLT.Assumptions.MazurProof.CurveZetaClassNumber

/-! The true full effective-class map has the proved complete-linear-system
cardinality, with rank taken from the actual bounded-pole vector spaces. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_FullPicardSectionRank
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_RiemannRochSpace N25F_FullPicardDegree
open N25F_SectionClassFiber N25F_SectionPrincipalTransport

/-- The actual section dimension on each degree fibre of the full Picard group. -/
def fullPicardSectionRank25Two (n : ℤ)
    (c : fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker n) : ℕ :=
  fullClassSectionRank25Two c.1

/-- A representative of a Picard class identifies the existing effectiveClass
fibre with the effective-divisor fibre already identified with actual sections. -/
def fullEffectiveClassFiberEquiv25Two (n : ℕ)
    (c : fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker n)
    (D : ProjectiveDivisor25Two)
    (hD : fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D = c.1) :
    {E : fullClosedPointGrading25Two.EffDivOfDegree n //
      fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker n E = c} ≃
    FullEffectiveClassFiber25Two D := by
  have hdeg : fullClosedPointGrading25Two.divisorDegree D = (n : ℤ) := by
    have h := congrArg fullProjectiveClassDegree25Two hD
    rw [fullProjectiveClassDegree25Two_classOf] at h
    exact h.trans c.2
  have hn : (fullClosedPointGrading25Two.divisorDegree D).toNat = n := by
    rw [hdeg, Int.toNat_natCast]
  refine {
    toFun := fun E => ⟨⟨E.1.1, E.1.2.trans hn.symm⟩, ?_⟩
    invFun := fun E => ⟨⟨E.1.1, E.1.2.trans hn⟩, ?_⟩
    left_inv := fun E => rfl
    right_inv := fun E => rfl }
  · exact (congrArg Subtype.val E.2).trans hD.symm
  · exact Subtype.ext (E.2.trans hD)

/-- The existing full effectiveClass map has the exact section-rank fibre count. -/
theorem fullEffectiveClass_fiber_card25Two (n : ℕ)
    (c : fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker n) :
    Nat.card {E : fullClosedPointGrading25Two.EffDivOfDegree n //
      fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker n E = c} =
      2 ^ fullPicardSectionRank25Two n c - 1 := by
  let D : ProjectiveDivisor25Two := Quotient.out c.1
  have hD : fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D = c.1 :=
    Quotient.out_eq c.1
  rw [Nat.card_congr (fullEffectiveClassFiberEquiv25Two n c D hD),
    fullEffectiveClassFiber25Two_card]
  have hr := congrArg fullClassSectionRank25Two hD
  rw [fullClassSectionRank25Two_classOf] at hr
  exact congrArg (fun r : ℕ => 2 ^ r - 1) hr

/-- This is the exact full-grading fibre formula expected by the middle-degree count. -/
theorem fullEffectiveClass_fiber_linearSystemCard25Two (n : ℕ)
    (c : fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker n) :
    Nat.card {E : fullClosedPointGrading25Two.EffDivOfDegree n //
      fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker n E = c} =
      CurveZetaClassNumber.linearSystemCard 2 (fullPicardSectionRank25Two n c) := by
  rw [fullEffectiveClass_fiber_card25Two]
  symm
  simpa only [CurveZetaClassNumber.linearSystemCard, Nat.reduceSub, Nat.div_one] using
    (Nat.geomSum_eq (by decide : 1 < (2 : ℕ)) (fullPicardSectionRank25Two n c))

end MazurProof.N25F_FullPicardSectionRank
