import AwayFractionCheck
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

namespace N25CurvePointFractionCheck
open MazurProof
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open N25F_ZChartWChartEquiv N25F_ZChartFractionMap N25F_ZChartFractionInjective
open N25F_YZOverlapMap N25F_YZAffineOverlapEquiv N25F_YZLocalFractionEmbedding
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
variable (f : YChartRing →ₐ[ZMod 2] ZMod 2) (hf : f yZ = 1)
include hf
local instance : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom

private theorem yZ_not_mem : yZ ∉ RingHom.ker f.toRingHom := by
  intro h
  have hzero : f yZ = 0 := RingHom.mem_ker.mp h
  rw [hf] at hzero
  exact one_ne_zero hzero

private theorem zY_ne_zero : zY ≠ 0 := by
  let p := RingHom.ker f.toRingHom
  let T := Localization.AtPrime p
  letI : Nontrivial T := IsLocalization.AtPrime.nontrivial T p
  let M := Submonoid.powers yZ
  have hMN : M ≤ p.primeCompl := by
    rintro a ⟨n, rfl⟩
    exact p.primeCompl.pow_mem (Ideal.mem_primeCompl_iff.mpr (yZ_not_mem f hf)) n
  letI : Algebra YZOpen T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe YZOpen T M p.primeCompl hMN
  letI : Nontrivial YZOpen := (algebraMap YZOpen T).domain_nontrivial
  letI : Nontrivial ZYOpen := yzAffineOverlapEquiv.symm.toRingHom.domain_nontrivial
  intro hzero
  have hu : IsUnit (algebraMap ZChartRing ZYOpen zY) :=
    IsLocalization.map_units ZYOpen ⟨zY, Submonoid.mem_powers zY⟩
  exact hu.ne_zero (by simp [hzero])

private theorem exists_yzLocalToFraction :
    ∃ g : Localization.AtPrime (RingHom.ker f.toRingHom) →+* FractionRing W,
      Function.Injective g ∧
      (letI := g.toAlgebra;
        IsFractionRing (Localization.AtPrime (RingHom.ker f.toRingHom)) (FractionRing W)) ∧
      ∀ r : YChartRing,
        g (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) r) =
          yZOpenToFraction (zY_ne_zero f hf) (algebraMap YChartRing YZOpen r) :=
  N25FractionExtensionCheck.exists_atPrime_fraction_map
    (RingHom.ker f.toRingHom) yZ (yZ_not_mem f hf)
    (yZOpenToFraction (zY_ne_zero f hf)).toRingHom
    (yZOpenToFraction_injective (zY_ne_zero f hf))
    (yZOpenToFraction_isFractionRing (zY_ne_zero f hf))

private def yzLocalToFractionRingHom :
    Localization.AtPrime (RingHom.ker f.toRingHom) →+* FractionRing W :=
  Classical.choose (exists_yzLocalToFraction f hf)

private theorem yzLocalToFractionRingHom_algebraMap (r : YChartRing) :
    yzLocalToFractionRingHom f hf
      (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) r) =
      yZOpenToFraction (zY_ne_zero f hf) (algebraMap YChartRing YZOpen r) :=
  (Classical.choose_spec (exists_yzLocalToFraction f hf)).2.2 r

/-- The coordinate-rigid embedding of the prime-local Y chart into the common field. -/
def yzLocalToFraction :
    Localization.AtPrime (RingHom.ker f.toRingHom) →ₐ[ZMod 2] FractionRing W where
  __ := yzLocalToFractionRingHom f hf
  commutes' c := by
    change yzLocalToFractionRingHom f hf
      (algebraMap (ZMod 2) (Localization.AtPrime (RingHom.ker f.toRingHom)) c) = _
    rw [IsScalarTower.algebraMap_apply (ZMod 2) YChartRing
      (Localization.AtPrime (RingHom.ker f.toRingHom)),
      yzLocalToFractionRingHom_algebraMap,
      ← IsScalarTower.algebraMap_apply (ZMod 2) YChartRing YZOpen]
    exact (yZOpenToFraction (zY_ne_zero f hf)).commutes c

@[simp] theorem yzLocalToFraction_algebraMap (r : YChartRing) :
    yzLocalToFraction f hf
      (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) r) =
      zYOpenToFraction (zY_ne_zero f hf) (yChartToZYOpen r) := by
  change yzLocalToFractionRingHom f hf _ = _
  rw [yzLocalToFractionRingHom_algebraMap]
  change zYOpenToFraction (zY_ne_zero f hf)
    (yzAffineOverlapEquiv (algebraMap YChartRing YZOpen r)) = _
  rw [yzAffineOverlapEquiv_algebraMap]

theorem yzLocalToFraction_injective : Function.Injective (yzLocalToFraction f hf) :=
  (Classical.choose_spec (exists_yzLocalToFraction f hf)).1

theorem yzLocalToFraction_isFractionRing :
    letI := (yzLocalToFraction f hf).toRingHom.toAlgebra
    IsFractionRing (Localization.AtPrime (RingHom.ker f.toRingHom)) (FractionRing W) :=
  (Classical.choose_spec (exists_yzLocalToFraction f hf)).2.1

theorem fraction_qy_ne_zero : algebraMap W (FractionRing W) qy ≠ 0 := by
  intro hzero
  have hy : zChartToFraction zY ≠ 0 :=
    (map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr (zY_ne_zero f hf)
  apply hy
  rw [zChartToFraction_zY, hzero, zero_div]

@[simp] theorem yzLocalToFraction_yZ :
    yzLocalToFraction f hf
      (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yZ) =
      algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qy := by
  rw [yzLocalToFraction_algebraMap, yChartToZYOpen_yZ,
    zYOpenToFraction_invSelf, zChartToFraction_zY, inv_div]

@[simp] theorem yzLocalToFraction_yzW :
    yzLocalToFraction f hf
      (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW) =
      1 / algebraMap W (FractionRing W) qy := by
  rw [yzLocalToFraction_algebraMap, yChartToZYOpen_yzW, map_mul,
    zYOpenToFraction_invSelf, zYOpenToFraction_algebraMap,
    zChartToFraction_zY, zChartToFraction_zW]
  field_simp [fraction_qz_ne_zero, fraction_qy_ne_zero f hf]
  exact div_self fraction_qz_ne_zero

@[simp] theorem yzLocalToFraction_yX :
    yzLocalToFraction f hf
      (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yX) =
      algebraMap W (FractionRing W) qx / algebraMap W (FractionRing W) qy := by
  rw [yzLocalToFraction_algebraMap, yChartToZYOpen_yX, map_mul,
    zYOpenToFraction_invSelf, zYOpenToFraction_algebraMap,
    zChartToFraction_zY, zChartToFraction_zX]
  field_simp [fraction_qz_ne_zero, fraction_qy_ne_zero f hf]
  exact mul_div_cancel_left₀ _ fraction_qz_ne_zero

theorem yzLocalToFraction_unique
    (g : Localization.AtPrime (RingHom.ker f.toRingHom) →ₐ[ZMod 2] FractionRing W)
    (hg : ∀ r : YChartRing,
      g (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) r) =
      zYOpenToFraction (zY_ne_zero f hf) (yChartToZYOpen r)) :
    g = yzLocalToFraction f hf := by
  apply IsLocalization.algHom_ext (RingHom.ker f.toRingHom).primeCompl
  ext r
  exact (hg r).trans (yzLocalToFraction_algebraMap f hf r).symm

#print axioms yzLocalToFraction_yX
#print axioms yzLocalToFraction_unique
#print axioms yzLocalToFraction
#print axioms yzLocalToFraction_injective
#print axioms yzLocalToFraction_isFractionRing
#print axioms fraction_qy_ne_zero
#print axioms yzLocalToFraction_yZ
#print axioms yzLocalToFraction_yzW
end N25CurvePointFractionCheck
