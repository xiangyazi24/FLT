import Mathlib.RingTheory.Localization.LocalizationLocalization
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace N25FractionExtensionCheck

theorem exists_atPrime_fraction_map
    {R K : Type*} [CommRing R] [Field K]
    (p : Ideal R) [p.IsPrime] (t : R) (ht : t ∉ p)
    (f : Localization.Away t →+* K) (hf : Function.Injective f)
    (hfrac : letI := f.toAlgebra; IsFractionRing (Localization.Away t) K) :
    ∃ g : Localization.AtPrime p →+* K,
      Function.Injective g ∧
      (letI := g.toAlgebra; IsFractionRing (Localization.AtPrime p) K) ∧
      ∀ r : R, g (algebraMap R (Localization.AtPrime p) r) =
        f (algebraMap R (Localization.Away t) r) := by
  let A := Localization.Away t
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
  letI : Algebra A K := f.toAlgebra
  letI : IsFractionRing A K := hfrac
  letI : IsDomain A := hf.isDomain f
  let N' := N.map (algebraMap R A)
  letI : IsLocalization N' T := IsLocalization.isLocalization_of_submonoid_le A T M N hMN
  have hN' : N' ≤ nonZeroDivisors A := by
    intro a ha
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    have hu : IsUnit (algebraMap A T a) := IsLocalization.map_units T ⟨a, ha⟩
    exact hu.ne_zero (by simp [hzero])
  have hu : ∀ a : N', IsUnit (f a) := by
    intro a
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff f hf).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (hN' a.2)))
  let g : T →+* K := IsLocalization.lift hu
  have hg (a : A) : g (algebraMap A T a) = f a := IsLocalization.lift_eq hu a
  letI : Algebra T K := g.toAlgebra
  letI : IsScalarTower A T K := IsScalarTower.of_algebraMap_eq' (RingHom.ext hg).symm
  have hgfrac : IsFractionRing T K :=
    IsFractionRing.isFractionRing_of_isLocalization N' T K hN'
  refine ⟨g, ?_, hgfrac, ?_⟩
  · exact IsFractionRing.injective T K
  · intro r
    rw [IsScalarTower.algebraMap_apply R A T, hg]

#print axioms exists_atPrime_fraction_map
end N25FractionExtensionCheck
