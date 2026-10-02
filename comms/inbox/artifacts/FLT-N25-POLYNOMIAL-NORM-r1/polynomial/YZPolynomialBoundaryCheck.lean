import CurvePointFractionCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.Tactic.NormNum
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



private theorem ordFrac_aeval_at_pole
    {k R L : Type*} [Field k] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field L] [Algebra k R] [Algebra R L] [Algebra k L] [IsScalarTower k R L]
    [IsFractionRing R L] (z : L) (n : ℕ) (hn : 0 < n)
    (hz : Ring.ordFrac R z = WithZero.exp (-(n : ℤ)))
    (p : Polynomial k) (hp : p ≠ 0) :
    Ring.ordFrac R (p.aeval z) = WithZero.exp (-(n * p.natDegree : ℤ)) := by
  let v := (IsDiscreteValuationRing.maximalIdeal R).valuation L
  letI : v.IsTrivialOn k := ⟨by
    intro a ha
    have hu : IsUnit (algebraMap k R a) :=
      (isUnit_iff_ne_zero.mpr ha).map (algebraMap k R)
    have ho : Ring.ordFrac R (algebraMap R L (algebraMap k R a)) = 1 :=
      Ring.ordFrac_of_isUnit hu
    rw [← IsScalarTower.algebraMap_apply k R L, Ring.ordFrac_eq_valuation_inv] at ho
    exact inv_eq_one.mp ho⟩
  have hvz : v z = WithZero.exp (n : ℤ) := by
    have hi := congrArg Inv.inv hz
    simpa [Ring.ordFrac_eq_valuation_inv, v] using hi
  have hvpos : 1 < v z := by
    rw [hvz, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact_mod_cast hn
  have he := Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    (v := v) z hvpos hp
  rw [Ring.ordFrac_eq_valuation_inv, he, hvz, ← WithZero.exp_nsmul, ← WithZero.exp_neg]
  congr 1
  simp only [nsmul_eq_mul]
  ring



/-- The actual YZ boundary order of p(Z/W) is minus 1 times its degree. -/
theorem yzLocalFractionOrder_aeval_qz (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    (yzLocalFractionOrder (f := f) (hf := hf)) (p.aeval (algebraMap W K qz)) =
      WithZero.exp (-(1 * p.natDegree : ℤ)) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker f.toRingHom)) := by
    have hn : ¬ IsField (Localization.AtPrime (RingHom.ker f.toRingHom)) := by
      intro hfield
      letI : Field (Localization.AtPrime (RingHom.ker f.toRingHom)) := hfield.toField
      have hu := Ring.ord_of_isUnit (isUnit_iff_ne_zero.mpr (yzWGerm_ne_zero (f := f) (hf := hf)))
      have ho : Ring.ord (Localization.AtPrime (RingHom.ker f.toRingHom)) (algebraMap YChartRing (Localization.AtPrime (RingHom.ker f.toRingHom)) yzW) = 1 := Fact.out
      rw [ho] at hu
      exact one_ne_zero hu
    exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime (RingHom.ker f.toRingHom)) hn).out 0 2).mpr
      (inferInstance : IsDedekindDomain (Localization.AtPrime (RingHom.ker f.toRingHom)))
  letI : Algebra (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction f hf).toRingHom.toAlgebra
  letI : IsFractionRing (Localization.AtPrime (RingHom.ker f.toRingHom)) K := (N25CurvePointFractionCheck.yzLocalToFraction_isFractionRing f hf)
  letI : IsScalarTower (ZMod 2) (Localization.AtPrime (RingHom.ker f.toRingHom)) K :=
    IsScalarTower.of_algebraMap_eq fun a => ((N25CurvePointFractionCheck.yzLocalToFraction f hf).commutes a).symm
  have hzlog : WithZero.log ((yzLocalFractionOrder (f := f) (hf := hf)) (algebraMap W K qz)) = -1 :=
    (yzBoundaryOrder_qz (f := f) (hf := hf))
  have hz : (yzLocalFractionOrder (f := f) (hf := hf)) (algebraMap W K qz) = WithZero.exp (-(1 : ℤ)) :=
    (WithZero.exp_log (((isUnit_iff_ne_zero.mpr fraction_qz_ne_zero).map
      (yzLocalFractionOrder (f := f) (hf := hf))).ne_zero)).symm.trans (congrArg WithZero.exp hzlog)
  exact ordFrac_aeval_at_pole (R := (Localization.AtPrime (RingHom.ker f.toRingHom))) (algebraMap W K qz) 1
    (by decide) hz p hp

#check @yzLocalFractionOrder_aeval_qz
#print axioms yzLocalFractionOrder_aeval_qz
end N25YZBoundaryPointCheck
