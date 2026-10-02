import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
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
