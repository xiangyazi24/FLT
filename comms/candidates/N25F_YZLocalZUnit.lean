import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryYZLocal

-- Full-module imports make instance search slower than in dot's selective-import check.
set_option synthInstance.maxHeartbeats 200000

/-! The actual YZ-boundary point lies in the overlap with the Z chart: the
germ Z/Y is a unit in its existing local ring. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_YZLocalZUnit

open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal

local instance : yzPrime.IsPrime := yzPrime_isMaximal.isPrime

/-- The actual germ of Z/Y at the boundary point [0:1:1:0]. -/
def yzZGerm : YZLocalRing := algebraMap YChartRing YZLocalRing yZ

/-- Z/Y is invertible in the existing YZ-boundary local ring. -/
theorem yzZGerm_isUnit : IsUnit yzZGerm := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff YZLocalRing yzPrime yZ).2
  apply Ideal.mem_primeCompl_iff.mpr
  intro h
  have hzero : yzPointEval yZ = 0 := RingHom.mem_ker.mp h
  rw [yzPointEval_yZ] at hzero
  exact one_ne_zero hzero

end MazurProof.N25F_YZLocalZUnit
