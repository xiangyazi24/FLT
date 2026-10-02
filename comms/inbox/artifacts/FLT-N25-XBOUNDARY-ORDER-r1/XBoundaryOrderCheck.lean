import XChartFractionEquivCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Basic
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

#check @MazurProof.N25F_XBoundaryOrder.xLocalToFraction_isFractionRing
#print axioms MazurProof.N25F_XBoundaryOrder.xLocalToFraction_isFractionRing
#check @MazurProof.N25F_XBoundaryOrder.xLocalFractionOrder
#print axioms MazurProof.N25F_XBoundaryOrder.xLocalFractionOrder
#check @MazurProof.N25F_XBoundaryOrder.xBoundaryOrder
#print axioms MazurProof.N25F_XBoundaryOrder.xBoundaryOrder
#check @MazurProof.N25F_XBoundaryOrder.xLocalFractionOrder_xWGerm
#print axioms MazurProof.N25F_XBoundaryOrder.xLocalFractionOrder_xWGerm
#check @MazurProof.N25F_XBoundaryOrder.xBoundaryOrder_qx
#print axioms MazurProof.N25F_XBoundaryOrder.xBoundaryOrder_qx
