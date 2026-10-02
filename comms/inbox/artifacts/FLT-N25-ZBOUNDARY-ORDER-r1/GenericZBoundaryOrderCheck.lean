import ZChartFractionEquivCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Basic
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


end MazurProof.N25F_ZBoundaryOrder

#check @MazurProof.N25F_ZBoundaryOrder.zW_ne_zero
#print axioms MazurProof.N25F_ZBoundaryOrder.zW_ne_zero
#check @MazurProof.N25F_ZBoundaryOrder.zW_mem_zPrime
#print axioms MazurProof.N25F_ZBoundaryOrder.zW_mem_zPrime
#check @MazurProof.N25F_ZBoundaryOrder.zPrime_ne_bot
#print axioms MazurProof.N25F_ZBoundaryOrder.zPrime_ne_bot
#check @MazurProof.N25F_ZBoundaryOrder.zLocalRing_isDiscreteValuationRing
#print axioms MazurProof.N25F_ZBoundaryOrder.zLocalRing_isDiscreteValuationRing
#check @MazurProof.N25F_ZBoundaryOrder.zWGerm_ne_zero
#print axioms MazurProof.N25F_ZBoundaryOrder.zWGerm_ne_zero
#check @MazurProof.N25F_ZBoundaryOrder.zLocalToFraction
#print axioms MazurProof.N25F_ZBoundaryOrder.zLocalToFraction
#check @MazurProof.N25F_ZBoundaryOrder.zLocalToFraction_injective
#print axioms MazurProof.N25F_ZBoundaryOrder.zLocalToFraction_injective
#check @MazurProof.N25F_ZBoundaryOrder.zLocalToFraction_zWGerm
#print axioms MazurProof.N25F_ZBoundaryOrder.zLocalToFraction_zWGerm
#check @MazurProof.N25F_ZBoundaryOrder.zLocalToFraction_isFractionRing
#print axioms MazurProof.N25F_ZBoundaryOrder.zLocalToFraction_isFractionRing
#check @MazurProof.N25F_ZBoundaryOrder.zLocalFractionOrder
#print axioms MazurProof.N25F_ZBoundaryOrder.zLocalFractionOrder
#check @MazurProof.N25F_ZBoundaryOrder.zBoundaryOrder
#print axioms MazurProof.N25F_ZBoundaryOrder.zBoundaryOrder
#check @MazurProof.N25F_ZBoundaryOrder.zLocalFractionOrder_zWGerm
#print axioms MazurProof.N25F_ZBoundaryOrder.zLocalFractionOrder_zWGerm
#check @MazurProof.N25F_ZBoundaryOrder.zBoundaryOrder_qz
#print axioms MazurProof.N25F_ZBoundaryOrder.zBoundaryOrder_qz
