from pathlib import Path
import hashlib
r=Path('/workspace/shared/flt-n25-yz-local-dedekind')
g=(r/'GenericLocalDedekindCheck.lean').read_text();a=g.index('namespace N25LocalDedekindCheck');s='''import YZAffineOverlapEquivCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
'''+g[a:]+'''
namespace N25ActualCurvePointCheck
open MazurProof
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ZChartWChartEquiv N25F_YZAffineOverlapEquiv

variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]

local instance (f : YChartRing →ₐ[ZMod 2] ZMod 2) :
    (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom

/-- Specialization to the actual Y/Z charts, with only the source point's
already-proved Z/Y=1 condition supplied explicitly. -/
theorem curve_point_local_isDedekind
    (f : YChartRing →ₐ[ZMod 2] ZMod 2) (hf : f yZ = 1) :
    IsDedekindDomain (Localization.AtPrime (RingHom.ker f.toRingHom)) := by
  have ht : yZ ∉ RingHom.ker f.toRingHom := by
    intro h
    have hzero : f yZ = 0 := RingHom.mem_ker.mp h
    rw [hf] at hzero
    exact one_ne_zero hzero
  exact N25LocalDedekindCheck.local_dedekind_of_away_equiv
    (RingHom.ker f.toRingHom) yZ ht zY yzAffineOverlapEquiv.toRingEquiv

#check @curve_point_local_isDedekind
#print axioms curve_point_local_isDedekind
end N25ActualCurvePointCheck
'''
(r/'CurvePointLocalDedekindCheck.lean').write_text(s);print(len(s),hashlib.sha256(s.encode()).hexdigest())
