import FLT.Assumptions.MazurProof.N25F_YZAffineOverlapEquiv
import FLT.Assumptions.MazurProof.N25F_ZChartFractionEquiv
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The actual YZ local ring embeds coordinate-rigidly into the fixed W-chart
function field, which is its fraction field. The construction uses the proved
Y/Z affine-overlap equivalence and the canonical localization at the actual
point. No Y-chart domain, local-ring isomorphism, or field-map premise is added. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace MazurProof.N25F_YZLocalFractionEmbedding

open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open N25F_ZChartWChartEquiv N25F_ZChartFractionMap N25F_ZChartFractionInjective
open N25F_ZChartFractionEquiv N25F_YZLocalZUnit N25F_YZOverlapMap
open N25F_YZAffineOverlapEquiv
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local instance : yzPrime.IsPrime := yzPrime_isMaximal.isPrime

private theorem exists_atPrime_fraction_map
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

private theorem yZ_not_mem : yZ ∉ yzPrime := by
  intro h
  have hzero : yzPointEval yZ = 0 := RingHom.mem_ker.mp h
  rw [yzPointEval_yZ] at hzero
  exact one_ne_zero hzero

private theorem zY_ne_zero : zY ≠ 0 := by
  let p := yzPrime
  let T := Localization.AtPrime p
  letI : Nontrivial T := IsLocalization.AtPrime.nontrivial T p
  let M := Submonoid.powers yZ
  have hMN : M ≤ p.primeCompl := by
    rintro a ⟨n, rfl⟩
    exact p.primeCompl.pow_mem (Ideal.mem_primeCompl_iff.mpr (yZ_not_mem)) n
  letI : Algebra YZOpen T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe YZOpen T M p.primeCompl hMN
  letI : Nontrivial YZOpen := (algebraMap YZOpen T).domain_nontrivial
  letI : Nontrivial ZYOpen := yzAffineOverlapEquiv.symm.toRingHom.domain_nontrivial
  intro hzero
  have hu : IsUnit (algebraMap ZChartRing ZYOpen zY) :=
    IsLocalization.map_units ZYOpen ⟨zY, Submonoid.mem_powers zY⟩
  exact hu.ne_zero (by simp [hzero])

private theorem zY_powers_nonZeroDivisors :
    Submonoid.powers zY ≤ nonZeroDivisors ZChartRing := by
  rintro a ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n zY_ne_zero)

private theorem zY_powers_map_units (s : Submonoid.powers zY) :
    IsUnit (zChartToFraction (s : ZChartRing)) := by
  exact isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (zY_powers_nonZeroDivisors s.2)))

def zYOpenToFraction : ZYOpen →ₐ[ZMod 2] FractionRing W :=
  IsLocalization.liftAlgHom (zY_powers_map_units)

@[simp] theorem zYOpenToFraction_algebraMap (a : ZChartRing) :
    zYOpenToFraction (algebraMap ZChartRing ZYOpen a) = zChartToFraction a :=
  IsLocalization.lift_eq (zY_powers_map_units) a

theorem zYOpenToFraction_isFractionRing :
    letI := (zYOpenToFraction).toRingHom.toAlgebra
    IsFractionRing ZYOpen (FractionRing W) := by
  letI : Algebra ZChartRing (FractionRing W) := zChartToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZChartRing (FractionRing W) := zChartToFraction_isFractionRing
  letI : Algebra ZYOpen (FractionRing W) := (zYOpenToFraction).toRingHom.toAlgebra
  letI : IsScalarTower ZChartRing ZYOpen (FractionRing W) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext (zYOpenToFraction_algebraMap)).symm
  exact IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers zY) ZYOpen (FractionRing W) (zY_powers_nonZeroDivisors)

theorem zYOpenToFraction_injective : Function.Injective (zYOpenToFraction) := by
  letI := (zYOpenToFraction).toRingHom.toAlgebra
  letI := zYOpenToFraction_isFractionRing
  exact IsFractionRing.injective ZYOpen (FractionRing W)

@[simp] theorem zYOpenToFraction_invSelf :
    zYOpenToFraction (IsLocalization.Away.invSelf zY : ZYOpen) =
      (zChartToFraction zY)⁻¹ := by
  apply (mul_left_cancel₀ ((map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr zY_ne_zero))
  rw [mul_inv_cancel₀ ((map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr zY_ne_zero)]
  rw [← zYOpenToFraction_algebraMap, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

def yZOpenToFraction : YZOpen →ₐ[ZMod 2] FractionRing W :=
  (zYOpenToFraction).comp yzAffineOverlapEquiv.toAlgHom

theorem yZOpenToFraction_injective : Function.Injective (yZOpenToFraction) :=
  (zYOpenToFraction_injective).comp yzAffineOverlapEquiv.injective

theorem yZOpenToFraction_isFractionRing :
    letI := (yZOpenToFraction).toRingHom.toAlgebra
    IsFractionRing YZOpen (FractionRing W) := by
  letI := (zYOpenToFraction).toRingHom.toAlgebra
  letI := zYOpenToFraction_isFractionRing
  letI := (yZOpenToFraction).toRingHom.toAlgebra
  exact IsFractionRing.of_ringEquiv_left yzAffineOverlapEquiv.toRingEquiv (fun _ => rfl)

private theorem exists_yzLocalToFraction :
    ∃ g : YZLocalRing →+* FractionRing W,
      Function.Injective g ∧
      (letI := g.toAlgebra;
        IsFractionRing (YZLocalRing) (FractionRing W)) ∧
      ∀ r : YChartRing,
        g (algebraMap YChartRing (YZLocalRing) r) =
          yZOpenToFraction (algebraMap YChartRing YZOpen r) :=
  exists_atPrime_fraction_map
    (yzPrime) yZ (yZ_not_mem)
    (yZOpenToFraction).toRingHom
    (yZOpenToFraction_injective)
    (yZOpenToFraction_isFractionRing)

private def yzLocalToFractionRingHom :
    YZLocalRing →+* FractionRing W :=
  Classical.choose (exists_yzLocalToFraction)

private theorem yzLocalToFractionRingHom_algebraMap (r : YChartRing) :
    yzLocalToFractionRingHom
      (algebraMap YChartRing (YZLocalRing) r) =
      yZOpenToFraction (algebraMap YChartRing YZOpen r) :=
  (Classical.choose_spec (exists_yzLocalToFraction)).2.2 r

/-- The coordinate-rigid embedding of the existing YZ local ring into the common W-chart function field. -/
def yzLocalToFraction :
    YZLocalRing →ₐ[ZMod 2] FractionRing W where
  __ := yzLocalToFractionRingHom
  commutes' c := by
    change yzLocalToFractionRingHom
      (algebraMap (ZMod 2) (YZLocalRing) c) = _
    rw [IsScalarTower.algebraMap_apply (ZMod 2) YChartRing
      (YZLocalRing),
      yzLocalToFractionRingHom_algebraMap,
      ← IsScalarTower.algebraMap_apply (ZMod 2) YChartRing YZOpen]
    exact (yZOpenToFraction).commutes c

@[simp] theorem yzLocalToFraction_algebraMap (r : YChartRing) :
    yzLocalToFraction
      (algebraMap YChartRing (YZLocalRing) r) =
      zYOpenToFraction (yChartToZYOpen r) := by
  change yzLocalToFractionRingHom _ = _
  rw [yzLocalToFractionRingHom_algebraMap]
  change zYOpenToFraction
    (yzAffineOverlapEquiv (algebraMap YChartRing YZOpen r)) = _
  rw [yzAffineOverlapEquiv_algebraMap]

theorem yzLocalToFraction_injective : Function.Injective (yzLocalToFraction) :=
  (Classical.choose_spec (exists_yzLocalToFraction)).1

theorem yzLocalToFraction_isFractionRing :
    letI := (yzLocalToFraction).toRingHom.toAlgebra
    IsFractionRing (YZLocalRing) (FractionRing W) :=
  (Classical.choose_spec (exists_yzLocalToFraction)).2.1

theorem fraction_qy_ne_zero : algebraMap W (FractionRing W) qy ≠ 0 := by
  intro hzero
  have hy : zChartToFraction zY ≠ 0 :=
    (map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr (zY_ne_zero)
  apply hy
  rw [zChartToFraction_zY, hzero, zero_div]

@[simp] theorem yzLocalToFraction_yZ :
    yzLocalToFraction
      (algebraMap YChartRing (YZLocalRing) yZ) =
      algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qy := by
  rw [yzLocalToFraction_algebraMap, yChartToZYOpen_yZ,
    zYOpenToFraction_invSelf, zChartToFraction_zY, inv_div]

@[simp] theorem yzLocalToFraction_yzW :
    yzLocalToFraction
      (algebraMap YChartRing (YZLocalRing) yzW) =
      1 / algebraMap W (FractionRing W) qy := by
  rw [yzLocalToFraction_algebraMap, yChartToZYOpen_yzW, map_mul,
    zYOpenToFraction_invSelf, zYOpenToFraction_algebraMap,
    zChartToFraction_zY, zChartToFraction_zW]
  field_simp [fraction_qz_ne_zero, fraction_qy_ne_zero]
  exact div_self fraction_qz_ne_zero

@[simp] theorem yzLocalToFraction_yX :
    yzLocalToFraction
      (algebraMap YChartRing (YZLocalRing) yX) =
      algebraMap W (FractionRing W) qx / algebraMap W (FractionRing W) qy := by
  rw [yzLocalToFraction_algebraMap, yChartToZYOpen_yX, map_mul,
    zYOpenToFraction_invSelf, zYOpenToFraction_algebraMap,
    zChartToFraction_zY, zChartToFraction_zX]
  field_simp [fraction_qz_ne_zero, fraction_qy_ne_zero]
  exact mul_div_cancel_left₀ _ fraction_qz_ne_zero

theorem yzLocalToFraction_unique
    (g : YZLocalRing →ₐ[ZMod 2] FractionRing W)
    (hg : ∀ r : YChartRing,
      g (algebraMap YChartRing (YZLocalRing) r) =
      zYOpenToFraction (yChartToZYOpen r)) :
    g = yzLocalToFraction := by
  apply IsLocalization.algHom_ext (yzPrime).primeCompl
  ext r
  exact (hg r).trans (yzLocalToFraction_algebraMap r).symm


/-- The existing Z/Y germ has its prescribed homogeneous-coordinate image. -/
@[simp] theorem yzLocalToFraction_yzZGerm :
    yzLocalToFraction yzZGerm =
      algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qy :=
  yzLocalToFraction_yZ

/-- The existing W/Y germ has its prescribed homogeneous-coordinate image. -/
@[simp] theorem yzLocalToFraction_yzWGerm :
    yzLocalToFraction yzWGerm = 1 / algebraMap W (FractionRing W) qy :=
  yzLocalToFraction_yzW

end MazurProof.N25F_YZLocalFractionEmbedding
