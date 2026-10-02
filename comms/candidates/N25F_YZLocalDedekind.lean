import FLT.Assumptions.MazurProof.N25F_YZAffineOverlapEquiv
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The actual YZ local ring is Dedekind. The proved Y/Z affine-overlap
isomorphism identifies a neighborhood of the point with an open of the
established Z-chart Dedekind domain. Localization preserves the structure. -/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_YZLocalDedekind

open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ZChartWChartEquiv N25F_YZAffineOverlapEquiv

private theorem local_dedekind_of_away_equiv
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


local instance : yzPrime.IsPrime := yzPrime_isMaximal.isPrime

private theorem yZ_not_mem_yzPrime : yZ ∉ yzPrime := by
  intro h
  have hzero : yzPointEval yZ = 0 := RingHom.mem_ker.mp h
  rw [yzPointEval_yZ] at hzero
  exact one_ne_zero hzero

/-- The existing local ring at [0:1:1:0] is a Dedekind domain, through the
actual Y/Z overlap equivalence. No substitute point or local ring is used. -/
instance yzLocalRing_isDedekindDomain : IsDedekindDomain YZLocalRing :=
  local_dedekind_of_away_equiv yzPrime yZ yZ_not_mem_yzPrime zY
    yzAffineOverlapEquiv.toRingEquiv

end MazurProof.N25F_YZLocalDedekind
