from pathlib import Path
r=Path('/workspace/shared/flt-n25-yz-local-dvr')
g=(r/'GenericLocalNonzero.lean').read_text();g=g[g.index('theorem local_nonzero'):g.index('#print axioms')].strip()
header='''import FLT.Assumptions.MazurProof.N25F_YZLocalDedekind
import FLT.Assumptions.MazurProof.N25F_ZBoundaryOrder
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! The actual YZ boundary germ is nonzero, and its already-proved order one
makes the existing Dedekind local ring a discrete valuation ring. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_YZLocalDVR

open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ZChartWChartEquiv N25F_YZAffineOverlapEquiv
open N25F_YZLocalDedekind N25F_ZBoundaryOrder

'''
body='''
local instance : yzPrime.IsPrime := yzPrime_isMaximal.isPrime

private theorem yZ_not_mem_yzPrime : yZ ∉ yzPrime := by
  intro h
  have hzero : yzPointEval yZ = 0 := RingHom.mem_ker.mp h
  rw [yzPointEval_yZ] at hzero
  exact one_ne_zero hzero

/-- The genuine germ W/Y is nonzero in the actual local ring at [0:1:1:0]. -/
theorem yzWGerm_ne_zero : yzWGerm ≠ 0 := by
  apply local_nonzero_of_away_equiv yzPrime yZ yZ_not_mem_yzPrime zY
    yzAffineOverlapEquiv.toRingEquiv yzW zW zW_ne_zero
  change yzAffineOverlapEquiv (algebraMap YChartRing YZOpen yzW) *
    algebraMap ZChartRing ZYOpen zY = algebraMap ZChartRing ZYOpen zW
  rw [yzAffineOverlapEquiv_algebraMap, yChartToZYOpen_yzW]
  calc
    _ = (algebraMap ZChartRing ZYOpen zY * IsLocalization.Away.invSelf zY) *
        algebraMap ZChartRing ZYOpen zW := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_mul]

/-- A nonzero element of positive order rules out a field. -/
theorem yzLocalRing_not_isField : ¬ IsField YZLocalRing := by
  intro h
  letI : Field YZLocalRing := h.toField
  have hz : Ring.ord YZLocalRing yzWGerm = 0 :=
    Ring.ord_of_isUnit (isUnit_iff_ne_zero.mpr yzWGerm_ne_zero)
  rw [yzWGerm_ord_eq_one] at hz
  exact one_ne_zero hz

/-- The existing local ring at [0:1:1:0] is a discrete valuation ring. -/
instance yzLocalRing_isDiscreteValuationRing : IsDiscreteValuationRing YZLocalRing :=
  ((IsDiscreteValuationRing.TFAE YZLocalRing yzLocalRing_not_isField).out 0 2).mpr
    (inferInstance : IsDedekindDomain YZLocalRing)

end MazurProof.N25F_YZLocalDVR
'''
(r/'N25F_YZLocalDVR.lean').write_text(header+'private '+g+'\n\n'+body)
# Exact curve-algebra specialization. The named point and source order fact
# remain explicit in this selective-import microcheck.
old=Path('/workspace/shared/flt-n25-yz-local-dedekind/CurvePointLocalDedekindCheck.lean').read_text()
old=old.replace('import Mathlib.RingTheory.Localization.LocalizationLocalization','import Mathlib.RingTheory.Localization.LocalizationLocalization\nimport Mathlib.RingTheory.OrderOfVanishing.Basic')
s=old+'''\nnamespace N25LocalNonzeroCheck\n'''+g+'''\n#print axioms local_nonzero_of_away_equiv
end N25LocalNonzeroCheck
namespace N25CurvePointDVRCheck
open MazurProof
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ZChartWChartEquiv N25F_YZAffineOverlapEquiv N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [IsDedekindDomain W] [Module.IsTorsionFree (Polynomial (ZMod 2)) W]
variable (f : YChartRing →ₐ[ZMod 2] ZMod 2) (hf : f yZ = 1)
local notation "p" => RingHom.ker f.toRingHom
local notation "T" => Localization.AtPrime p
local instance : (p).IsPrime := RingHom.ker_isPrime f.toRingHom

private theorem zW_ne_zero : (zW : ZChartRing) ≠ 0 := by
  intro h
  have heq := congrArg zChartToFraction h
  rw [zChartToFraction_zW, map_zero] at heq
  exact (one_div_ne_zero fraction_qz_ne_zero) heq

include hf in
theorem curve_point_germ_ne_zero : algebraMap YChartRing T yzW ≠ 0 := by
  have ht : yZ ∉ p := by
    intro h
    have hzero : f yZ = 0 := RingHom.mem_ker.mp h
    rw [hf] at hzero
    exact one_ne_zero hzero
  apply N25LocalNonzeroCheck.local_nonzero_of_away_equiv p yZ ht zY
    yzAffineOverlapEquiv.toRingEquiv yzW zW zW_ne_zero
  change yzAffineOverlapEquiv (algebraMap YChartRing YZOpen yzW) *
    algebraMap ZChartRing ZYOpen zY = algebraMap ZChartRing ZYOpen zW
  rw [yzAffineOverlapEquiv_algebraMap, yChartToZYOpen_yzW]
  calc
    _ = (algebraMap ZChartRing ZYOpen zY * IsLocalization.Away.invSelf zY) *
        algebraMap ZChartRing ZYOpen zW := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_mul]

include hf in
theorem curve_point_not_isField
    (hord : Ring.ord T (algebraMap YChartRing T yzW) = 1) : ¬ IsField T := by
  intro h
  letI : Field T := h.toField
  have hz : Ring.ord T (algebraMap YChartRing T yzW) = 0 :=
    Ring.ord_of_isUnit (isUnit_iff_ne_zero.mpr (curve_point_germ_ne_zero f hf))
  rw [hord] at hz
  exact one_ne_zero hz

include hf in
theorem curve_point_isDVR
    (hord : Ring.ord T (algebraMap YChartRing T yzW) = 1) :
    letI : IsDedekindDomain T := N25ActualCurvePointCheck.curve_point_local_isDedekind f hf
    IsDiscreteValuationRing T := by
  letI : IsDedekindDomain T := N25ActualCurvePointCheck.curve_point_local_isDedekind f hf
  exact ((IsDiscreteValuationRing.TFAE T (curve_point_not_isField f hf hord)).out 0 2).mpr
    (inferInstance : IsDedekindDomain T)

#check @curve_point_germ_ne_zero
#check @curve_point_isDVR
#print axioms curve_point_germ_ne_zero
#print axioms curve_point_not_isField
#print axioms curve_point_isDVR
end N25CurvePointDVRCheck
'''
(r/'CurvePointLocalDVRCheck.lean').write_text(s)
