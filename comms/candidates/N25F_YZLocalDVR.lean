import FLT.Assumptions.MazurProof.N25F_YZLocalDedekind
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

private theorem local_nonzero_of_away_equiv
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
