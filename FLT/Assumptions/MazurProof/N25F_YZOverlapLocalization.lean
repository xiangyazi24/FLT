import FLT.Assumptions.MazurProof.N25F_YZOverlapMap
import Mathlib.RingTheory.Localization.Away.Basic

/-! Extend the actual Z-chart map across the Y/Z overlap by inverting Y/Z.
The inverse coordinate maps back to the existing germ Z/Y. -/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_YZOverlapLocalization

open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open N25F_ZChartWChartEquiv N25F_YZLocalZUnit N25F_YZOverlapMap

private theorem zChartToYZLocal_isUnit_of_powers (s : Submonoid.powers zY) :
    IsUnit (zChartToYZLocal (s : ZChartRing) : YZLocalRing) := by
  obtain ⟨n, hn⟩ := s.2
  rw [← hn, map_pow]
  exact zChartToYZLocal_zY_isUnit.pow n

/-- The actual Z-chart Y-nonzero overlap maps to the existing YZ local ring. -/
def zYOpenToYZLocal : Localization.Away zY →ₐ[ZMod 2] YZLocalRing :=
  IsLocalization.liftAlgHom
    (A := ZMod 2) (R := ZChartRing) (S := Localization.Away zY)
    (P := YZLocalRing) (M := Submonoid.powers zY) (f := zChartToYZLocal)
    zChartToYZLocal_isUnit_of_powers

@[simp]
theorem zYOpenToYZLocal_algebraMap (a : ZChartRing) :
    zYOpenToYZLocal (algebraMap ZChartRing (Localization.Away zY) a) =
      (zChartToYZLocal a : YZLocalRing) := by
  exact IsLocalization.lift_eq zChartToYZLocal_isUnit_of_powers a

/-- The inverted Y/Z coordinate maps to the actual local germ Z/Y. -/
theorem zYOpenToYZLocal_invSelf :
    zYOpenToYZLocal (IsLocalization.Away.invSelf zY : Localization.Away zY) =
      yzZGerm := by
  have h := congrArg zYOpenToYZLocal
    (IsLocalization.Away.mul_invSelf zY (S := Localization.Away zY))
  rw [map_mul, map_one, zYOpenToYZLocal_algebraMap, zChartToYZLocal_zY] at h
  simpa using (Units.inv_mul_eq_iff_eq_mul yzZUnit).1 h

end MazurProof.N25F_YZOverlapLocalization
