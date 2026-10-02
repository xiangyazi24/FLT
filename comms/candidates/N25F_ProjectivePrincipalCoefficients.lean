import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalDivisor

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ProjectivePrincipalCoefficients
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_NonBoundaryPrincipalDivisor
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open N25F_XBoundaryOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

@[simp]
theorem projectivePrincipalDivisor_apply_X (f : Additive CurveFieldˣ) :
    projectivePrincipalDivisor f (fullBoundaryAtomOfTag .X) = xBoundaryOrder f :=
  congrArg (fun D => D.1.1) (projectivePrincipalDivisor_split f)

@[simp]
theorem projectivePrincipalDivisor_apply_YZ (f : Additive CurveFieldˣ) :
    projectivePrincipalDivisor f (fullBoundaryAtomOfTag .YZ) = yzBoundaryOrder f :=
  congrArg (fun D => D.1.2.1) (projectivePrincipalDivisor_split f)

@[simp]
theorem projectivePrincipalDivisor_apply_Z (f : Additive CurveFieldˣ) :
    projectivePrincipalDivisor f (fullBoundaryAtomOfTag .Z) = zBoundaryOrder f :=
  congrArg (fun D => D.1.2.2) (projectivePrincipalDivisor_split f)

@[simp]
theorem projectivePrincipalDivisor_apply_nonBoundary (f : Additive CurveFieldˣ)
    (A : FullNonBoundaryAtom25Two) :
    projectivePrincipalDivisor f A.1 = nonBoundaryPrincipalDivisor f A := by
  have h := congrArg (fun D => (nonBoundaryDivisorEquivWChart.symm D.2) A)
    (projectivePrincipalDivisor_split f)
  change (nonBoundaryDivisorEquivWChart.symm
      (nonBoundaryDivisorEquivWChart
        (fullDivisorEquivBoundaryNonBoundary (projectivePrincipalDivisor f)).2)) A =
    (nonBoundaryDivisorEquivWChart.symm
      (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f))) A at h
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at h
  exact h

end MazurProof.N25F_ProjectivePrincipalCoefficients
