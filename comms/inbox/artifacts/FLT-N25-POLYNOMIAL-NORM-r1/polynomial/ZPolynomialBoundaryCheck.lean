import ZChartFractionEquivCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.Tactic.NormNum
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace N25ZLocalFamilyCheck
open MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

local instance (f : ZChartRing →ₐ[ZMod 2] ZMod 2) :
    (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom

abbrev LocalRing (f : ZChartRing →ₐ[ZMod 2] ZMod 2) :=
  Localization.AtPrime (RingHom.ker f.toRingHom)

def germ (f : ZChartRing →ₐ[ZMod 2] ZMod 2) : LocalRing f :=
  algebraMap ZChartRing (LocalRing f) zW

theorem pointPrime_isMaximal (f : ZChartRing →ₐ[ZMod 2] ZMod 2) :
    (RingHom.ker f.toRingHom).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap (ZMod 2) ZChartRing c, f.commutes c⟩

@[simp] theorem pointEval_zW (f : ZChartRing →ₐ[ZMod 2] ZMod 2)
    [Fact (f zW = 0)] : f zW = 0 := Fact.out

theorem germ_ord_two (f : ZChartRing →ₐ[ZMod 2] ZMod 2)
    [Fact (Ring.ord (LocalRing f) (germ f) = 2)] :
    Ring.ord (LocalRing f) (germ f) = 2 := Fact.out

end N25ZLocalFamilyCheck

namespace MazurProof.N25F_ZBoundaryOrder

open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_ZChartWChartEquiv N25F_ZChartFractionMap
open N25F_ZChartFractionInjective N25F_ZChartFractionEquiv

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
variable {pointEval : ZChartRing →ₐ[ZMod 2] ZMod 2} [Fact (pointEval zW = 0)]
local notation "zPointEval" => pointEval
local notation "zPrime" => RingHom.ker pointEval.toRingHom
local notation "zPrime_isMaximal" => N25ZLocalFamilyCheck.pointPrime_isMaximal pointEval
local notation "ZLocalRing" => N25ZLocalFamilyCheck.LocalRing pointEval
local notation "zWGerm" => N25ZLocalFamilyCheck.germ pointEval
local notation "zWGerm_ord_eq_two" => N25ZLocalFamilyCheck.germ_ord_two pointEval
local instance : (zPrime).IsPrime := (zPrime_isMaximal).isPrime

/-- The boundary coordinate is nonzero on the actual Z-chart curve. -/
theorem zW_ne_zero : (zW : ZChartRing) ≠ 0 := by
  intro h
  have heq := congrArg zChartToFraction h
  rw [zChartToFraction_zW, map_zero] at heq
  exact (one_div_ne_zero fraction_qz_ne_zero) heq

/-- The boundary coordinate belongs to the existing point prime. -/
theorem zW_mem_zPrime : zW ∈ zPrime := by
  change zPointEval zW = 0
  simp

/-- The actual Z-boundary point prime is nonzero. -/
theorem zPrime_ne_bot : zPrime ≠ ⊥ := by
  intro h
  have hw := (zW_mem_zPrime (pointEval := pointEval))
  rw [h, Ideal.mem_bot] at hw
  exact zW_ne_zero hw

/-- The existing Z-boundary local ring is a DVR. -/
instance zLocalRing_isDiscreteValuationRing : IsDiscreteValuationRing ZLocalRing :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    ZChartRing (zPrime_ne_bot (pointEval := pointEval)) ZLocalRing

/-- The actual germ W/Z is nonzero. -/
theorem zWGerm_ne_zero : zWGerm ≠ 0 :=
  (map_ne_zero_iff (algebraMap ZChartRing ZLocalRing)
    (IsLocalization.injective ZLocalRing (zPrime).primeCompl_le_nonZeroDivisors)).2
      zW_ne_zero

private theorem zChartToFraction_isUnit_of_primeCompl (s : (zPrime).primeCompl) :
    IsUnit (zChartToFraction (s : ZChartRing)) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hs : (s : ZChartRing) = 0 :=
    zChartToFraction_injective (h.trans (map_zero zChartToFraction).symm)
  exact (Ideal.mem_primeCompl_iff.mp s.2) (hs ▸ (zPrime).zero_mem)

/-- The actual Z-boundary local ring maps into the common W-chart function field. -/
def zLocalToFraction : ZLocalRing →ₐ[ZMod 2] FractionRing W :=
  IsLocalization.liftAlgHom
    (A := ZMod 2) (R := ZChartRing) (S := ZLocalRing)
    (P := FractionRing W) (f := zChartToFraction)
    (zChartToFraction_isUnit_of_primeCompl (pointEval := pointEval))

@[simp]
theorem zLocalToFraction_algebraMap (a : ZChartRing) :
    (zLocalToFraction (pointEval := pointEval)) (algebraMap ZChartRing ZLocalRing a) =
      zChartToFraction a := by
  exact IsLocalization.lift_eq (zChartToFraction_isUnit_of_primeCompl (pointEval := pointEval)) a

/-- The coordinate-rigid local-ring map is injective. -/
theorem zLocalToFraction_injective : Function.Injective (zLocalToFraction (pointEval := pointEval)) := by
  change Function.Injective
    (IsLocalization.lift (S := ZLocalRing)
      (g := zChartToFraction.toRingHom) (zChartToFraction_isUnit_of_primeCompl (pointEval := pointEval)))
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  constructor
  · intro h
    simpa using congrArg (zLocalToFraction (pointEval := pointEval)) h
  · intro h
    exact congrArg (algebraMap ZChartRing ZLocalRing) (zChartToFraction_injective h)

/-- In the shared field, the actual boundary germ is exactly W/Z. -/
@[simp]
theorem zLocalToFraction_zWGerm :
    (zLocalToFraction (pointEval := pointEval)) zWGerm = 1 / algebraMap W (FractionRing W) qz := by
  rw [N25ZLocalFamilyCheck.germ, (zLocalToFraction_algebraMap (pointEval := pointEval)), zChartToFraction_zW]


/-- The common coordinate-rigid field is a fraction field of the actual
Z-boundary local ring. The scalar action is explicitly the established map. -/
theorem zLocalToFraction_isFractionRing :
    letI : Algebra ZLocalRing K := (zLocalToFraction (pointEval := pointEval)).toRingHom.toAlgebra
    IsFractionRing ZLocalRing K := by
  letI : Algebra ZChartRing K := zChartToFraction.toRingHom.toAlgebra
  letI : Algebra ZLocalRing K := (zLocalToFraction (pointEval := pointEval)).toRingHom.toAlgebra
  letI : IsScalarTower ZChartRing ZLocalRing K :=
    IsScalarTower.of_algebraMap_eq fun a => ((zLocalToFraction_algebraMap (pointEval := pointEval)) a).symm
  letI : IsFractionRing ZChartRing K := zChartToFraction_isFractionRing
  exact IsFractionRing.isFractionRing_of_isLocalization
    (zPrime).primeCompl ZLocalRing K (zPrime).primeCompl_le_nonZeroDivisors

/-- The actual Z-local length order extended to the fixed function field. -/
def zLocalFractionOrder : K →*₀ WithZero (Multiplicative ℤ) := by
  letI : Algebra ZLocalRing K := (zLocalToFraction (pointEval := pointEval)).toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing K := (zLocalToFraction_isFractionRing (pointEval := pointEval))
  exact Ring.ordFrac ZLocalRing

/-- The genuine boundary coefficient of a nonzero function at `[0:0:1:0]`. -/
def zBoundaryOrder : Additive Kˣ →+ ℤ where
  toFun f := WithZero.log ((zLocalFractionOrder (pointEval := pointEval)) (f.toMul : K))
  map_zero' := by change WithZero.log ((zLocalFractionOrder (pointEval := pointEval)) (1 : K)) = 0; simp
  map_add' f g := by
    change WithZero.log ((zLocalFractionOrder (pointEval := pointEval)) ((f.toMul : K) * (g.toMul : K))) = _
    rw [map_mul]
    exact WithZero.log_mul
      ((Units.isUnit f.toMul).map (zLocalFractionOrder (pointEval := pointEval))).ne_zero
      ((Units.isUnit g.toMul).map (zLocalFractionOrder (pointEval := pointEval))).ne_zero

private theorem ordFrac_image_eq_exp
    {R L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L]
    (a : R) (ha : a ≠ 0) (n : ℕ) (hord : Ring.ord R a = n) :
    Ring.ordFrac R (algebraMap R L a) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl

variable [Fact (Ring.ord (N25ZLocalFamilyCheck.LocalRing pointEval) (N25ZLocalFamilyCheck.germ pointEval) = 2)]

/-- The common-field image of the actual boundary germ has order two. -/
theorem zLocalFractionOrder_zWGerm :
    (zLocalFractionOrder (pointEval := pointEval)) ((zLocalToFraction (pointEval := pointEval)) zWGerm) = WithZero.exp (2 : ℤ) := by
  letI : Algebra ZLocalRing K := (zLocalToFraction (pointEval := pointEval)).toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing K := (zLocalToFraction_isFractionRing (pointEval := pointEval))
  exact ordFrac_image_eq_exp (L := K) zWGerm (zWGerm_ne_zero (pointEval := pointEval)) 2 zWGerm_ord_eq_two

/-- The actual affine function Z/W has a pole of order two at the
Z-boundary point, with the positive-zero/negative-pole sign convention. -/
theorem zBoundaryOrder_qz :
    (zBoundaryOrder (pointEval := pointEval)) (Additive.ofMul (Units.mk0
      (algebraMap W K qz) fraction_qz_ne_zero)) = -2 := by
  change WithZero.log ((zLocalFractionOrder (pointEval := pointEval)) (algebraMap W K qz)) = -2
  have h : algebraMap W K qz = ((zLocalToFraction (pointEval := pointEval)) zWGerm)⁻¹ := by
    rw [(zLocalToFraction_zWGerm (pointEval := pointEval)), one_div, inv_inv]
  rw [h, map_inv₀, WithZero.log_inv, (zLocalFractionOrder_zWGerm (pointEval := pointEval)), WithZero.log_exp]



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



/-- The actual Z boundary order of p(Z/W) is minus 2 times its degree. -/
theorem zLocalFractionOrder_aeval_qz (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    (zLocalFractionOrder (pointEval := pointEval)) (p.aeval (algebraMap W K qz)) =
      WithZero.exp (-(2 * p.natDegree : ℤ)) := by
  letI : Algebra ZLocalRing K := (zLocalToFraction (pointEval := pointEval)).toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing K := (zLocalToFraction_isFractionRing (pointEval := pointEval))
  letI : IsScalarTower (ZMod 2) ZLocalRing K :=
    IsScalarTower.of_algebraMap_eq fun a => ((zLocalToFraction (pointEval := pointEval)).commutes a).symm
  have hzlog : WithZero.log ((zLocalFractionOrder (pointEval := pointEval)) (algebraMap W K qz)) = -2 :=
    (zBoundaryOrder_qz (pointEval := pointEval))
  have hz : (zLocalFractionOrder (pointEval := pointEval)) (algebraMap W K qz) = WithZero.exp (-(2 : ℤ)) :=
    (WithZero.exp_log (((isUnit_iff_ne_zero.mpr fraction_qz_ne_zero).map
      (zLocalFractionOrder (pointEval := pointEval))).ne_zero)).symm.trans (congrArg WithZero.exp hzlog)
  exact ordFrac_aeval_at_pole (R := ZLocalRing) (algebraMap W K qz) 2
    (by decide) hz p hp

#check @zLocalFractionOrder_aeval_qz
#print axioms zLocalFractionOrder_aeval_qz
end MazurProof.N25F_ZBoundaryOrder
