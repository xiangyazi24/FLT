import YZAffineOverlapEquivCheck
import Mathlib.RingTheory.Localization.LocalizationLocalization
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace MazurProof.N25F_YZLocalFractionEmbedding
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open N25F_ZChartWChartEquiv N25F_ZChartFractionMap N25F_ZChartFractionInjective
open N25F_ZChartFractionEquiv N25F_YZAffineOverlapEquiv
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
variable (hs : zY ≠ 0)
include hs
private theorem zY_powers_nonZeroDivisors :
    Submonoid.powers zY ≤ nonZeroDivisors ZChartRing := by
  rintro a ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hs)

private theorem zY_powers_map_units (s : Submonoid.powers zY) :
    IsUnit (zChartToFraction (s : ZChartRing)) := by
  exact isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (zY_powers_nonZeroDivisors hs s.2)))

def zYOpenToFraction : ZYOpen →ₐ[ZMod 2] FractionRing W :=
  IsLocalization.liftAlgHom (zY_powers_map_units hs)

@[simp] theorem zYOpenToFraction_algebraMap (a : ZChartRing) :
    zYOpenToFraction hs (algebraMap ZChartRing ZYOpen a) = zChartToFraction a :=
  IsLocalization.lift_eq (zY_powers_map_units hs) a

theorem zYOpenToFraction_isFractionRing :
    letI := (zYOpenToFraction hs).toRingHom.toAlgebra
    IsFractionRing ZYOpen (FractionRing W) := by
  letI : Algebra ZChartRing (FractionRing W) := zChartToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZChartRing (FractionRing W) := zChartToFraction_isFractionRing
  letI : Algebra ZYOpen (FractionRing W) := (zYOpenToFraction hs).toRingHom.toAlgebra
  letI : IsScalarTower ZChartRing ZYOpen (FractionRing W) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext (zYOpenToFraction_algebraMap hs)).symm
  exact IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers zY) ZYOpen (FractionRing W) (zY_powers_nonZeroDivisors hs)

theorem zYOpenToFraction_injective : Function.Injective (zYOpenToFraction hs) := by
  letI := (zYOpenToFraction hs).toRingHom.toAlgebra
  letI := zYOpenToFraction_isFractionRing hs
  exact IsFractionRing.injective ZYOpen (FractionRing W)

@[simp] theorem zYOpenToFraction_invSelf :
    zYOpenToFraction hs (IsLocalization.Away.invSelf zY : ZYOpen) =
      (zChartToFraction zY)⁻¹ := by
  apply (mul_left_cancel₀ ((map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr hs))
  rw [mul_inv_cancel₀ ((map_ne_zero_iff zChartToFraction zChartToFraction_injective).mpr hs)]
  rw [← zYOpenToFraction_algebraMap hs, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

def yZOpenToFraction : YZOpen →ₐ[ZMod 2] FractionRing W :=
  (zYOpenToFraction hs).comp yzAffineOverlapEquiv.toAlgHom

theorem yZOpenToFraction_injective : Function.Injective (yZOpenToFraction hs) :=
  (zYOpenToFraction_injective hs).comp yzAffineOverlapEquiv.injective

theorem yZOpenToFraction_isFractionRing :
    letI := (yZOpenToFraction hs).toRingHom.toAlgebra
    IsFractionRing YZOpen (FractionRing W) := by
  letI := (zYOpenToFraction hs).toRingHom.toAlgebra
  letI := zYOpenToFraction_isFractionRing hs
  letI := (yZOpenToFraction hs).toRingHom.toAlgebra
  exact IsFractionRing.of_ringEquiv_left yzAffineOverlapEquiv.toRingEquiv (fun _ => rfl)

#print axioms zYOpenToFraction_isFractionRing
#print axioms yZOpenToFraction_isFractionRing
#print axioms yZOpenToFraction_injective
end MazurProof.N25F_YZLocalFractionEmbedding
