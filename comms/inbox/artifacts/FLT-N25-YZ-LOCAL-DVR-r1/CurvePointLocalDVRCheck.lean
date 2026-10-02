import YZAffineOverlapEquivCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Basic
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25LocalDedekindCheck

/-- If a neighborhood of a point is isomorphic to an open of a Dedekind
domain, its actual prime-local ring is Dedekind. -/
theorem local_dedekind_of_away_equiv
    {R Z : Type*} [CommRing R] [CommRing Z] [IsDedekindDomain Z]
    (p : Ideal R) [p.IsPrime] (t : R) (ht : t ∉ p) (s : Z)
    (e : Localization.Away t ≃+* Localization.Away s) :
    IsDedekindDomain (Localization.AtPrime p) := by
  let A := Localization.Away t
  let B := Localization.Away s
  let T := Localization.AtPrime p
  let M := Submonoid.powers t
  let N := p.primeCompl
  have hMN : M ≤ N := by
    intro a ha
    obtain ⟨n, rfl⟩ := ha
    exact N.pow_mem (Ideal.mem_primeCompl_iff.mpr ht) n
  letI : Nontrivial T := IsLocalization.AtPrime.nontrivial T p
  letI : Algebra A T := IsLocalization.localizationAlgebraOfSubmonoidLe A T M N hMN
  letI : IsScalarTower R A T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A T M N hMN
  letI : Nontrivial A := (algebraMap A T).domain_nontrivial
  letI : Nontrivial B := e.symm.toRingHom.domain_nontrivial
  have hS : Submonoid.powers s ≤ nonZeroDivisors Z := by
    intro a ha
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    have hu : IsUnit (algebraMap Z B a) := IsLocalization.map_units B ⟨a, ha⟩
    exact hu.ne_zero (by simp [hzero])
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hS
  letI : IsDedekindDomain B := IsLocalization.isDedekindDomain Z hS B
  letI : IsDomain A := e.toMulEquiv.isDomain B
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv B e.symm
  letI : Ring.DimensionLEOne A := Ring.DimensionLEOne.of_ringEquiv e
  letI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.symm
  letI : IsDedekindDomain A := { }
  let N' := N.map (algebraMap R A)
  letI : IsLocalization N' T := IsLocalization.isLocalization_of_submonoid_le A T M N hMN
  have hN' : N' ≤ nonZeroDivisors A := by
    intro a ha
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    have hu : IsUnit (algebraMap A T a) := IsLocalization.map_units T ⟨a, ha⟩
    exact hu.ne_zero (by simp [hzero])
  letI : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hN'
  exact IsLocalization.isDedekindDomain A hN' T

#print axioms local_dedekind_of_away_equiv
end N25LocalDedekindCheck

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

namespace N25LocalNonzeroCheck
theorem local_nonzero_of_away_equiv
    {R Z : Type*} [CommRing R] [CommRing Z] [IsDomain Z]
    (p : Ideal R) [p.IsPrime] (t : R) (ht : t ∉ p) (s : Z)
    (e : Localization.Away t ≃+* Localization.Away s)
    (a : R) (b : Z) (hb : b ≠ 0)
    (he : e (algebraMap R (Localization.Away t) a) *
      algebraMap Z (Localization.Away s) s =
      algebraMap Z (Localization.Away s) b) :
    algebraMap R (Localization.AtPrime p) a ≠ 0 := by
  let A := Localization.Away t
  let B := Localization.Away s
  let T := Localization.AtPrime p
  let M := Submonoid.powers t
  let N := p.primeCompl
  have hMN : M ≤ N := by
    intro a ha
    obtain ⟨n, rfl⟩ := ha
    exact N.pow_mem (Ideal.mem_primeCompl_iff.mpr ht) n
  letI : Nontrivial T := IsLocalization.AtPrime.nontrivial T p
  letI : Algebra A T := IsLocalization.localizationAlgebraOfSubmonoidLe A T M N hMN
  letI : IsScalarTower R A T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A T M N hMN
  letI : Nontrivial A := (algebraMap A T).domain_nontrivial
  letI : Nontrivial B := e.symm.toRingHom.domain_nontrivial
  have hS : Submonoid.powers s ≤ nonZeroDivisors Z := by
    intro x hx
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    have hu : IsUnit (algebraMap Z B x) := IsLocalization.map_units B ⟨x, hx⟩
    exact hu.ne_zero (by simp [hzero])
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hS
  letI : IsDomain A := e.toMulEquiv.isDomain B
  let N' := N.map (algebraMap R A)
  letI : IsLocalization N' T := IsLocalization.isLocalization_of_submonoid_le A T M N hMN
  have hN' : N' ≤ nonZeroDivisors A := by
    intro x hx
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    have hu : IsUnit (algebraMap A T x) := IsLocalization.map_units T ⟨x, hx⟩
    exact hu.ne_zero (by simp [hzero])
  intro hzero
  have hA : algebraMap R A a = 0 :=
    (IsLocalization.injective T hN') (by
      rw [← IsScalarTower.algebraMap_apply R A T, map_zero]
      exact hzero)
  have hB : algebraMap Z B b = 0 := by
    rw [hA, map_zero, zero_mul] at he
    exact he.symm
  exact hb ((IsLocalization.injective B hS) (hB.trans (map_zero _).symm))
#print axioms local_nonzero_of_away_equiv
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
