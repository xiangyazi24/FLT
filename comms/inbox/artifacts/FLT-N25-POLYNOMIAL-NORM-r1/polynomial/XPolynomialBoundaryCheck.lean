import XChartFractionEquivCheck
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic.NormNum
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoWBoundaryChartArtin
local notation "k₂" => ZMod 2

abbrev XAffineRing := AffineChart (0 : Fin 4)

private def xAffineEval : XAffineRing →+* k₂ :=
  MvPolynomial.eval₂Hom (RingHom.id k₂) (fun _ => 0)

private noncomputable def xAffineEvalAlg : XAffineRing →ₐ[k₂] k₂ where
  __ := xAffineEval
  commutes' c := by simp [xAffineEval]

private theorem xAffineEval_quadric :
    xAffineEval (chartAffineQuadric (0 : Fin 4)) = 0 := by
  simp [xAffineEval, chartAffineQuadric, ambientDehomogenize,
    dehomogenizedVariable, canonicalQuadricPolynomial25Two]

private theorem xAffineEval_cubic :
    xAffineEval (chartAffineCubic (0 : Fin 4)) = 0 := by
  simp [xAffineEval, chartAffineCubic, ambientDehomogenize,
    dehomogenizedVariable, canonicalCubicPolynomial25Two]

private theorem xEquationIdeal_le_ker :
    chartAffineEquationIdeal (0 : Fin 4) ≤ RingHom.ker xAffineEval := by
  rw [chartAffineEquationIdeal, Ideal.span_le]
  rintro f ⟨r, rfl⟩
  fin_cases r
  · exact RingHom.mem_ker.mpr xAffineEval_quadric
  · exact RingHom.mem_ker.mpr xAffineEval_cubic

noncomputable def xChartEval : XChartRing →ₐ[k₂] k₂ :=
  Ideal.Quotient.liftₐ
    (chartAffineEquationIdeal (0 : Fin 4)) xAffineEvalAlg
    (fun _ ha => RingHom.mem_ker.mp (xEquationIdeal_le_ker ha))

theorem xChartEval_surjective : Function.Surjective xChartEval := by
  intro c
  refine ⟨algebraMap k₂ XChartRing c, ?_⟩
  simp [xChartEval]

def xPrime : Ideal XChartRing := RingHom.ker xChartEval.toRingHom

theorem xPrime_isMaximal : xPrime.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    xChartEval.toRingHom xChartEval_surjective

local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

@[simp] theorem xChartEval_xW : xChartEval xW = 0 := by
  simp [xChartEval, xAffineEvalAlg, xAffineEval, xW, chartMap,
    ambientDehomogenize, dehomogenizedVariable]

@[simp] theorem xChartEval_xY : xChartEval xY = 0 := by
  simp [xChartEval, xAffineEvalAlg, xAffineEval, xY, chartMap,
    ambientDehomogenize, dehomogenizedVariable]

@[simp] theorem xChartEval_xZ : xChartEval xZ = 0 := by
  simp [xChartEval, xAffineEvalAlg, xAffineEval, xZ, chartMap,
    ambientDehomogenize, dehomogenizedVariable]


abbrev XLocalRing := Localization.AtPrime xPrime

noncomputable def xWGerm : XLocalRing :=
  algebraMap XChartRing XLocalRing xW

end MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal

namespace MazurProof.N25F_XLocalDVR

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_XChartWChartEquiv
open N25F_XChartFractionMap

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [IsDedekindDomain W]

/-- The actual X chart inherits Dedekind structure through its explicit
algebra equivalence with the established W chart. -/
instance xChartRing_isDedekindDomain : IsDedekindDomain XChartRing := by
  letI : IsNoetherianRing XChartRing :=
    isNoetherianRing_of_ringEquiv W xChartAlgEquivWChart.symm.toRingEquiv
  letI : Ring.DimensionLEOne XChartRing :=
    Ring.DimensionLEOne.of_ringEquiv xChartAlgEquivWChart.toRingEquiv
  letI : IsIntegrallyClosed XChartRing :=
    IsIntegrallyClosed.of_equiv xChartAlgEquivWChart.symm.toRingEquiv
  exact { }

/-- The actual coordinate `W/X` is nonzero, since its image is `1/(X/W)`
in the W-chart fraction field. No injectivity of the chart map is needed. -/
theorem xW_ne_zero : (xW : XChartRing) ≠ 0 := by
  intro h
  have heq := congrArg xChartToFraction h
  rw [xChartToFraction_xW, map_zero] at heq
  exact (one_div_ne_zero fraction_qx_ne_zero) heq

/-- The boundary coordinate vanishes at the actual X-boundary point. -/
theorem xW_mem_xPrime : xW ∈ xPrime :=
  RingHom.mem_ker.mpr xChartEval_xW

/-- The prime of `[1:0:0:0]` is a nonzero prime of the actual X chart. -/
theorem xPrime_ne_bot : xPrime ≠ ⊥ := by
  intro h
  have hw := xW_mem_xPrime
  rw [h, Ideal.mem_bot] at hw
  exact xW_ne_zero hw

local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

/-- The actual curve local ring at `[1:0:0:0]` is a DVR. -/
instance xLocalRing_isDiscreteValuationRing : IsDiscreteValuationRing XLocalRing :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    XChartRing xPrime_ne_bot XLocalRing

/-- The actual germ of `W/X` stays nonzero in the boundary local ring. -/
theorem xWGerm_ne_zero : xWGerm ≠ 0 :=
  (map_ne_zero_iff (algebraMap XChartRing XLocalRing)
    (IsLocalization.injective XLocalRing xPrime.primeCompl_le_nonZeroDivisors)).2
      xW_ne_zero

end MazurProof.N25F_XLocalDVR



namespace MazurProof.N25F_XCoordinateOrders

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoConormal
open N25F_XLocalDVR
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [IsDedekindDomain W]

private theorem coordinate_orders
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (y z w u v : R) (hwne : w ≠ 0)
    (hy : ¬ IsUnit y) (hz : ¬ IsUnit z) (hu : IsUnit u) (hv : IsUnit v)
    (hw : Ring.ord R w = 3)
    (hc : y * z = -(w * u)) (hq : z * v = -(w + y ^ 2)) :
    Ring.ord R y = 1 ∧ Ring.ord R z = 2 := by
  have hp : y * z ≠ 0 := by
    rw [hc]
    exact neg_ne_zero.mpr (mul_ne_zero hwne hu.ne_zero)
  have hyne : y ≠ 0 := left_ne_zero_of_mul hp
  have hzne : z ≠ 0 := right_ne_zero_of_mul hp
  have hs : Ring.ord R y + Ring.ord R z = 3 := by
    rw [← Ring.ord_mul R (mem_nonZeroDivisors_iff_ne_zero.mpr hzne), hc,
      Ring.ord_neg, Ring.ord_mul_of_isUnit_right hu, hw]
  have hqord : Ring.ord R (w + y ^ 2) = Ring.ord R z := by
    rw [← Ring.ord_neg (w + y ^ 2), ← hq, Ring.ord_mul_of_isUnit_right hv]
  have hi := Ring.ord_add w (y ^ 2)
  rw [hqord, hw, Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hyne)] at hi
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := R) (mem_nonZeroDivisors_iff_ne_zero.mpr hyne))
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := R) (mem_nonZeroDivisors_iff_ne_zero.mpr hzne))
  have hnpos : n ≠ 0 := by
    intro hnzero
    apply hy
    apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
    rw [← Ring.ord_eq_addVal, ← hn, hnzero]
    rfl
  have hmpos : m ≠ 0 := by
    intro hmzero
    apply hz
    apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
    rw [← Ring.ord_eq_addVal, ← hm, hmzero]
    rfl
  rw [← hn, ← hm] at hs hi ⊢
  have hsum : n + m = 3 := by exact_mod_cast hs
  have hmin : min 3 (2 * n) ≤ m := by
    simp only [nsmul_eq_mul, ← Nat.cast_mul] at hi
    rcases min_le_iff.mp hi with h | h
    · exact (min_le_left _ _).trans (by exact_mod_cast h)
    · exact (min_le_right _ _).trans (by exact_mod_cast h)
  have hn1 : n = 1 := by omega
  have hm2 : m = 2 := by omega
  simp [hn1, hm2]

/-- The actual germ Y/X at the X-boundary point. -/
def xYGerm : XLocalRing := algebraMap XChartRing XLocalRing xY

/-- The actual germ Z/X at the X-boundary point. -/
def xZGerm : XLocalRing := algebraMap XChartRing XLocalRing xZ

private def cubicFactor : XChartRing :=
  1 + xY + xZ + xY * xZ + xZ ^ 2 + xZ * xW

private def quadricFactor : XChartRing := 1 + xY + xW

private theorem x_quadric_relation : xZ + xW + xY ^ 2 + xY * xZ + xZ * xW = 0 := by
  have h := chartQuotientPoint_quadric (0 : Fin 4)
  simpa [canonicalQuadric25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, xY, xZ, xW, chartMap_X_pivot] using h

private theorem x_cubic_relation :
    xW + xY * xZ + xY * xW + xZ * xW + xY * xZ * xW +
      xZ ^ 2 * xW + xZ * xW ^ 2 = 0 := by
  have h := chartQuotientPoint_cubic (0 : Fin 4)
  simpa [canonicalCubic25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, xY, xZ, xW, chartMap_X_pivot] using h

local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

private theorem germ_isUnit_of_eval_one (a : XChartRing) (ha : xChartEval a = 1) :
    IsUnit (algebraMap XChartRing XLocalRing a) := by
  apply IsLocalization.map_units XLocalRing (⟨a, ?_⟩ : xPrime.primeCompl)
  apply Ideal.mem_primeCompl_iff.mpr
  intro hp
  have hzero : xChartEval a = 0 := RingHom.mem_ker.mp hp
  rw [ha] at hzero
  exact one_ne_zero hzero

private theorem xYGerm_not_isUnit : ¬ IsUnit xYGerm := by
  intro hu
  have h := (IsLocalization.AtPrime.isUnit_to_map_iff XLocalRing xPrime xY).mp hu
  exact (Ideal.mem_primeCompl_iff.mp h) (RingHom.mem_ker.mpr xChartEval_xY)

private theorem xZGerm_not_isUnit : ¬ IsUnit xZGerm := by
  intro hu
  have h := (IsLocalization.AtPrime.isUnit_to_map_iff XLocalRing xPrime xZ).mp hu
  exact (Ideal.mem_primeCompl_iff.mp h) (RingHom.mem_ker.mpr xChartEval_xZ)

variable (xWGerm_ord_eq_three : Ring.ord XLocalRing xWGerm = 3)
include xWGerm_ord_eq_three in
private theorem xCoordinateGermOrders :
    Ring.ord XLocalRing xYGerm = 1 ∧ Ring.ord XLocalRing xZGerm = 2 := by
  apply coordinate_orders xYGerm xZGerm xWGerm
    (algebraMap XChartRing XLocalRing cubicFactor)
    (algebraMap XChartRing XLocalRing quadricFactor)
    xWGerm_ne_zero xYGerm_not_isUnit xZGerm_not_isUnit
  · exact germ_isUnit_of_eval_one cubicFactor (by simp [cubicFactor])
  · exact germ_isUnit_of_eval_one quadricFactor (by simp [quadricFactor])
  · exact xWGerm_ord_eq_three
  · have hc : xY * xZ = -(xW * cubicFactor) := by
      apply eq_neg_of_add_eq_zero_left
      dsimp [cubicFactor]
      linear_combination x_cubic_relation
    simpa only [xYGerm, xZGerm, xWGerm, map_mul, map_neg] using congrArg (algebraMap XChartRing XLocalRing) hc
  · have hq : xZ * quadricFactor = -(xW + xY ^ 2) := by
      apply eq_neg_of_add_eq_zero_left
      dsimp [quadricFactor]
      linear_combination x_quadric_relation
    simpa only [xYGerm, xZGerm, xWGerm, map_mul, map_neg, map_add, map_pow] using
      congrArg (algebraMap XChartRing XLocalRing) hq

include xWGerm_ord_eq_three in
/-- The actual Y/X germ is a uniformizing function at [1:0:0:0]. -/
theorem xYGerm_ord_eq_one : Ring.ord XLocalRing xYGerm = 1 :=
  (xCoordinateGermOrders xWGerm_ord_eq_three).1

include xWGerm_ord_eq_three in
/-- The actual Z/X germ vanishes to order two at [1:0:0:0]. -/
theorem xZGerm_ord_eq_two : Ring.ord XLocalRing xZGerm = 2 :=
  (xCoordinateGermOrders xWGerm_ord_eq_three).2

#check @xYGerm_ord_eq_one
#check @xZGerm_ord_eq_two
#print axioms xYGerm_ord_eq_one
#print axioms xZGerm_ord_eq_two
end MazurProof.N25F_XCoordinateOrders

namespace MazurProof.N25F_XLocalFractionEmbedding

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_XChartFractionMap
open N25F_XChartFractionInjective

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [IsDedekindDomain W]
local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

private theorem xChartToFraction_isUnit_of_primeCompl (s : xPrime.primeCompl) :
    IsUnit (xChartToFraction (s : XChartRing)) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hs : (s : XChartRing) = 0 :=
    xChartToFraction_injective (h.trans (map_zero xChartToFraction).symm)
  exact (Ideal.mem_primeCompl_iff.mp s.2) (hs ▸ xPrime.zero_mem)

/-- The actual X-boundary local ring maps into the common W-chart function field. -/
def xLocalToFraction : XLocalRing →ₐ[ZMod 2] FractionRing W :=
  IsLocalization.liftAlgHom
    (A := ZMod 2) (R := XChartRing) (S := XLocalRing)
    (P := FractionRing W) (f := xChartToFraction)
    xChartToFraction_isUnit_of_primeCompl

@[simp]
theorem xLocalToFraction_algebraMap (a : XChartRing) :
    xLocalToFraction (algebraMap XChartRing XLocalRing a) =
      xChartToFraction a := by
  exact IsLocalization.lift_eq xChartToFraction_isUnit_of_primeCompl a

/-- The coordinate-rigid local-ring map is injective. -/
theorem xLocalToFraction_injective : Function.Injective xLocalToFraction := by
  change Function.Injective
    (IsLocalization.lift (S := XLocalRing)
      (g := xChartToFraction.toRingHom) xChartToFraction_isUnit_of_primeCompl)
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  constructor
  · intro h
    simpa using congrArg xLocalToFraction h
  · intro h
    exact congrArg (algebraMap XChartRing XLocalRing) (xChartToFraction_injective h)

/-- In the shared field, the actual boundary germ is exactly W/X. -/
@[simp]
theorem xLocalToFraction_xWGerm :
    xLocalToFraction xWGerm = 1 / algebraMap W (FractionRing W) qx := by
  rw [xWGerm, xLocalToFraction_algebraMap, xChartToFraction_xW]

end MazurProof.N25F_XLocalFractionEmbedding


namespace MazurProof.N25F_XBoundaryOrder

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_XChartFractionMap N25F_XChartFractionEquiv
open N25F_XLocalFractionEmbedding N25F_XLocalDVR

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [IsDedekindDomain W]
local notation "K" => FractionRing W
local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

/-- The common coordinate-rigid field is a fraction field of the actual
X-boundary local ring. The scalar action is explicitly the established map. -/
theorem xLocalToFraction_isFractionRing :
    letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
    IsFractionRing XLocalRing K := by
  letI : Algebra XChartRing K := xChartToFraction.toRingHom.toAlgebra
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsScalarTower XChartRing XLocalRing K :=
    IsScalarTower.of_algebraMap_eq fun a => (xLocalToFraction_algebraMap a).symm
  letI : IsFractionRing XChartRing K := xChartToFraction_isFractionRing
  exact IsFractionRing.isFractionRing_of_isLocalization
    xPrime.primeCompl XLocalRing K xPrime.primeCompl_le_nonZeroDivisors

/-- The actual X-local length order extended to the fixed function field. -/
def xLocalFractionOrder : K →*₀ WithZero (Multiplicative ℤ) := by
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
  exact Ring.ordFrac XLocalRing

/-- The genuine boundary coefficient of a nonzero function at `[1:0:0:0]`. -/
def xBoundaryOrder : Additive Kˣ →+ ℤ where
  toFun f := WithZero.log (xLocalFractionOrder (f.toMul : K))
  map_zero' := by change WithZero.log (xLocalFractionOrder (1 : K)) = 0; simp
  map_add' f g := by
    change WithZero.log (xLocalFractionOrder ((f.toMul : K) * (g.toMul : K))) = _
    rw [map_mul]
    exact WithZero.log_mul
      ((Units.isUnit f.toMul).map xLocalFractionOrder).ne_zero
      ((Units.isUnit g.toMul).map xLocalFractionOrder).ne_zero

private theorem ordFrac_image_eq_exp
    {R L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L]
    (a : R) (ha : a ≠ 0) (n : ℕ) (hord : Ring.ord R a = n) :
    Ring.ordFrac R (algebraMap R L a) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl

variable (xWGerm_ord_eq_three : Ring.ord XLocalRing xWGerm = 3)
include xWGerm_ord_eq_three

/-- The common-field image of the actual boundary germ has order three. -/
theorem xLocalFractionOrder_xWGerm :
    xLocalFractionOrder (xLocalToFraction xWGerm) = WithZero.exp (3 : ℤ) := by
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
  exact ordFrac_image_eq_exp (L := K) xWGerm xWGerm_ne_zero 3 xWGerm_ord_eq_three

/-- The actual affine function X/W has a pole of order three at the
X-boundary point, with the positive-zero/negative-pole sign convention. -/
theorem xBoundaryOrder_qx :
    xBoundaryOrder (Additive.ofMul (Units.mk0
      (algebraMap W K qx) fraction_qx_ne_zero)) = -3 := by
  change WithZero.log (xLocalFractionOrder (algebraMap W K qx)) = -3
  have h : algebraMap W K qx = (xLocalToFraction xWGerm)⁻¹ := by
    rw [xLocalToFraction_xWGerm, one_div, inv_inv]
  rw [h, map_inv₀, WithZero.log_inv, xLocalFractionOrder_xWGerm xWGerm_ord_eq_three, WithZero.log_exp]

end MazurProof.N25F_XBoundaryOrder


namespace MazurProof.N25F_XBoundaryZOrder

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_XLocalDVR N25F_XLocalFractionEmbedding N25F_XChartFractionMap
open N25F_XCoordinateOrders N25F_XBoundaryOrder

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
variable [IsDedekindDomain W]
variable (xWGerm_ord_eq_three : Ring.ord XLocalRing xWGerm = 3)
variable (fraction_qz_ne_zero : algebraMap W K qz ≠ 0)


@[simp]
theorem xLocalToFraction_xZGerm :
    xLocalToFraction xZGerm = algebraMap W K qz / algebraMap W K qx := by
  rw [xZGerm, xLocalToFraction_algebraMap, xChartToFraction_xZ]

include fraction_qz_ne_zero in
theorem xZGerm_ne_zero : xZGerm ≠ 0 := by
  intro hzero
  have h := congrArg xLocalToFraction hzero
  rw [xLocalToFraction_xZGerm, map_zero] at h
  exact (div_ne_zero fraction_qz_ne_zero fraction_qx_ne_zero) h

private theorem ordFrac_image_eq_exp
    {R L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L]
    (a : R) (ha : a ≠ 0) (n : ℕ) (hord : Ring.ord R a = n) :
    Ring.ordFrac R (algebraMap R L a) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl

include xWGerm_ord_eq_three fraction_qz_ne_zero in
theorem xLocalFractionOrder_xZGerm :
    xLocalFractionOrder (xLocalToFraction xZGerm) = WithZero.exp (2 : ℤ) := by
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
  exact ordFrac_image_eq_exp (L := K) xZGerm (xZGerm_ne_zero fraction_qz_ne_zero) 2 (xZGerm_ord_eq_two xWGerm_ord_eq_three)

include xWGerm_ord_eq_three in
/-- Z/W = (Z/X)/(W/X) has signed order 2 - 3 = -1 at [1:0:0:0]. -/
theorem xBoundaryOrder_qz :
    xBoundaryOrder (Additive.ofMul (Units.mk0
      (algebraMap W K qz) fraction_qz_ne_zero)) = -1 := by
  change WithZero.log (xLocalFractionOrder (algebraMap W K qz)) = -1
  have h : algebraMap W K qz = xLocalToFraction xZGerm / xLocalToFraction xWGerm := by
    rw [xLocalToFraction_xZGerm, xLocalToFraction_xWGerm, one_div, div_inv_eq_mul]
    exact (div_mul_cancel₀ _ fraction_qx_ne_zero).symm
  rw [h, map_div₀, xLocalFractionOrder_xZGerm xWGerm_ord_eq_three fraction_qz_ne_zero, xLocalFractionOrder_xWGerm xWGerm_ord_eq_three,
    WithZero.log_div (by simp) (by simp), WithZero.log_exp, WithZero.log_exp]
  norm_num

#check @xBoundaryOrder_qz
#print axioms xLocalToFraction_xZGerm
#print axioms xZGerm_ne_zero
#print axioms xLocalFractionOrder_xZGerm
#print axioms xBoundaryOrder_qz
end MazurProof.N25F_XBoundaryZOrder

namespace MazurProof.N25F_PolynomialBoundaryOrders
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder N25F_XBoundaryZOrder
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W

variable [IsDedekindDomain W]
variable (hord : Ring.ord XLocalRing xWGerm = 3)
variable (fraction_qz_ne_zero : algebraMap W K qz ≠ 0)
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


include hord fraction_qz_ne_zero in
/-- The actual X boundary order of p(Z/W) is minus 1 times its degree. -/
theorem xLocalFractionOrder_aeval_qz (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    xLocalFractionOrder (p.aeval (algebraMap W K qz)) =
      WithZero.exp (-(1 * p.natDegree : ℤ)) := by
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
  letI : IsScalarTower (ZMod 2) XLocalRing K :=
    IsScalarTower.of_algebraMap_eq fun a => (xLocalToFraction.commutes a).symm
  have hzlog : WithZero.log (xLocalFractionOrder (algebraMap W K qz)) = -1 :=
    xBoundaryOrder_qz hord fraction_qz_ne_zero
  have hz : xLocalFractionOrder (algebraMap W K qz) = WithZero.exp (-(1 : ℤ)) :=
    (WithZero.exp_log (((isUnit_iff_ne_zero.mpr fraction_qz_ne_zero).map
      xLocalFractionOrder).ne_zero)).symm.trans (congrArg WithZero.exp hzlog)
  exact ordFrac_aeval_at_pole (R := XLocalRing) (algebraMap W K qz) 1
    (by decide) hz p hp

#check @xLocalFractionOrder_aeval_qz
#print axioms xLocalFractionOrder_aeval_qz
end MazurProof.N25F_PolynomialBoundaryOrders
