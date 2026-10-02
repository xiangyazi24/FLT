import CurvePointFractionCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.OrderOfVanishing.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace N25YZBoundaryPointCheck
open MazurProof
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
private theorem ordFrac_image_eq_exp
    {R L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L]
    (a : R) (ha : a ≠ 0) (n : ℕ) (hord : Ring.ord R a = n) :
    Ring.ordFrac R (algebraMap R L a) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl


variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
variable {f : YChartRing →ₐ[ZMod 2] ZMod 2} {hf : f yZ = 1}
local instance : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
variable [IsDedekindDomain (Localization.AtPrime (RingHom.ker f.toRingHom))]
variable [Fact (Ring.ord (Localization.AtPrime (RingHom.ker f.toRingHom)) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW) = 1)]

include hf in
private theorem yzWGerm_ne_zero : (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW) ≠ 0 := by
  intro hzero
  have h := congrArg (N25CurvePointFractionCheck.yzLocalToFraction f hf) hzero
  rw [N25CurvePointFractionCheck.yzLocalToFraction_yzW, map_zero] at h
  exact (one_div_ne_zero (N25CurvePointFractionCheck.fraction_qy_ne_zero f hf)) h

include hf in
private theorem yzZGerm_isUnit : IsUnit (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yZ) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (RingHom.ker f.toRingHom)) (RingHom.ker f.toRingHom) yZ).2
  apply Ideal.mem_primeCompl_iff.mpr
  intro h
  have hzero : f yZ = 0 := RingHom.mem_ker.mp h
  rw [hf] at hzero
  exact one_ne_zero hzero

/-- The actual YZ-local length order extended to the fixed function field. -/
def yzLocalFractionOrder : K →*₀ WithZero (Multiplicative ℤ) := by
  letI : Algebra (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction f hf).toRingHom.toAlgebra
  letI : IsFractionRing (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction_isFractionRing f hf)
  exact Ring.ordFrac (Localization.AtPrime (RingHom.ker f.toRingHom))

/-- The genuine signed boundary coefficient of a nonzero function at [0:1:1:0]. -/
def yzBoundaryOrder : Additive Kˣ →+ ℤ where
  toFun u := WithZero.log ((yzLocalFractionOrder (f := f) (hf := hf)) (u.toMul : K))
  map_zero' := by change WithZero.log ((yzLocalFractionOrder (f := f) (hf := hf)) (1 : K)) = 0; simp
  map_add' u v := by
    change WithZero.log ((yzLocalFractionOrder (f := f) (hf := hf)) ((u.toMul : K) * (v.toMul : K))) = _
    rw [map_mul]
    exact WithZero.log_mul
      ((Units.isUnit u.toMul).map (yzLocalFractionOrder (f := f) (hf := hf))).ne_zero
      ((Units.isUnit v.toMul).map (yzLocalFractionOrder (f := f) (hf := hf))).ne_zero

/-- The common-field image of the existing W/Y germ has order one. -/
theorem yzLocalFractionOrder_yzWGerm :
    (yzLocalFractionOrder (f := f) (hf := hf)) ((N25CurvePointFractionCheck.yzLocalToFraction f hf) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW)) = WithZero.exp (1 : ℤ) := by
  letI : Algebra (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction f hf).toRingHom.toAlgebra
  letI : IsFractionRing (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction_isFractionRing f hf)
  exact ordFrac_image_eq_exp (L := K) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW) (yzWGerm_ne_zero (f := f) (hf := hf)) 1 (Fact.out : Ring.ord (Localization.AtPrime (RingHom.ker f.toRingHom)) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW) = 1)

/-- The common-field image of the existing unit Z/Y has order zero. -/
theorem yzLocalFractionOrder_yzZGerm :
    (yzLocalFractionOrder (f := f) (hf := hf)) ((N25CurvePointFractionCheck.yzLocalToFraction f hf) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yZ)) = 1 := by
  letI : Algebra (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction f hf).toRingHom.toAlgebra
  letI : IsFractionRing (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction_isFractionRing f hf)
  change Ring.ordFrac (Localization.AtPrime (RingHom.ker f.toRingHom)) (algebraMap (Localization.AtPrime (RingHom.ker f.toRingHom)) K (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yZ)) = 1
  simpa only [Nat.cast_zero, WithZero.exp_zero] using ordFrac_image_eq_exp (L := K) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yZ) (yzZGerm_isUnit (f := f) (hf := hf)).ne_zero 0
    (Ring.ord_of_isUnit (yzZGerm_isUnit (f := f) (hf := hf)))

/-- Y/W has a pole of order one, with positive-zero/negative-pole convention. -/
theorem yzBoundaryOrder_qy :
    (yzBoundaryOrder (f := f) (hf := hf)) (Additive.ofMul (Units.mk0
      (algebraMap W K qy) (N25CurvePointFractionCheck.fraction_qy_ne_zero f hf))) = -1 := by
  change WithZero.log ((yzLocalFractionOrder (f := f) (hf := hf)) (algebraMap W K qy)) = -1
  have h : algebraMap W K qy = ((N25CurvePointFractionCheck.yzLocalToFraction f hf) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW))⁻¹ := by
    rw [(N25CurvePointFractionCheck.yzLocalToFraction_yzW f hf), one_div, inv_inv]
  rw [h, map_inv₀, WithZero.log_inv, (yzLocalFractionOrder_yzWGerm (f := f) (hf := hf)), WithZero.log_exp]

/-- Z/W has a pole of order one, since Z/Y is a unit at this boundary point. -/
theorem yzBoundaryOrder_qz :
    (yzBoundaryOrder (f := f) (hf := hf)) (Additive.ofMul (Units.mk0
      (algebraMap W K qz) fraction_qz_ne_zero)) = -1 := by
  change WithZero.log ((yzLocalFractionOrder (f := f) (hf := hf)) (algebraMap W K qz)) = -1
  have h : algebraMap W K qz =
      (N25CurvePointFractionCheck.yzLocalToFraction f hf) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yZ) * ((N25CurvePointFractionCheck.yzLocalToFraction f hf) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW))⁻¹ := by
    rw [(N25CurvePointFractionCheck.yzLocalToFraction_yZ f hf), (N25CurvePointFractionCheck.yzLocalToFraction_yzW f hf), one_div, inv_inv]
    exact (div_mul_cancel₀ _ (N25CurvePointFractionCheck.fraction_qy_ne_zero f hf)).symm
  rw [h, map_mul, (yzLocalFractionOrder_yzZGerm (f := f) (hf := hf)), one_mul, map_inv₀,
    WithZero.log_inv, (yzLocalFractionOrder_yzWGerm (f := f) (hf := hf)), WithZero.log_exp]


#check @yzLocalFractionOrder
#print axioms yzLocalFractionOrder
#check @yzBoundaryOrder
#print axioms yzBoundaryOrder
#check @yzLocalFractionOrder_yzWGerm
#print axioms yzLocalFractionOrder_yzWGerm
#check @yzLocalFractionOrder_yzZGerm
#print axioms yzLocalFractionOrder_yzZGerm
#check @yzBoundaryOrder_qy
#print axioms yzBoundaryOrder_qy
#check @yzBoundaryOrder_qz
#print axioms yzBoundaryOrder_qz
end N25YZBoundaryPointCheck
