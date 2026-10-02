import FLT.Assumptions.MazurProof.N25F_FullPicardDegree
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree

/-! The actual rational X-boundary point supplies a degree-one class on
the full Picard quotient and identifies every degree fibre with degree zero. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_FullPicardBasePoint
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectiveDivisorDegree N25F_FullPicardDegree

/-- The degree-one class of the existing actual X-boundary closed point. -/
def fullProjectiveBaseClass25Two :
    fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two :=
  fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
    (Finsupp.single (fullBoundaryAtomOfTag .X) 1)

@[simp]
theorem fullProjectiveBaseClass25Two_degree :
    fullProjectiveClassDegree25Two fullProjectiveBaseClass25Two = 1 := by
  classical
  rw [fullProjectiveBaseClass25Two, fullProjectiveClassDegree25Two_classOf]
  simp [ClosedPointGrading.divisorDegree]

/-- Every integer occurs as the degree of an actual full divisor class. -/
theorem fullProjectiveClassDegree25Two_surjective :
    Function.Surjective fullProjectiveClassDegree25Two := by
  intro n
  refine ⟨n • fullProjectiveBaseClass25Two, ?_⟩
  rw [map_zsmul, fullProjectiveBaseClass25Two_degree]
  simp

/-- Translation by minus n copies of the actual X-boundary class identifies
the true degree-n Picard fibre with its degree-zero fibre. -/
def fullProjectivePicDegreeEquivZero25Two (n : ℤ) :
    fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker n ≃
      fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker 0 :=
  fullClosedPointGrading25Two.picDegreeEquivZero fullProjectivePrincipalSubgroup25Two
    fullProjectivePrincipalSubgroup25Two_le_degree_ker fullProjectiveBaseClass25Two
    fullProjectiveBaseClass25Two_degree n

end MazurProof.N25F_FullPicardBasePoint
