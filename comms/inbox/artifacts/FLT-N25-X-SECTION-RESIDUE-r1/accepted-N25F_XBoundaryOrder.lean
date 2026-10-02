import FLT.Assumptions.MazurProof.N25F_XChartFractionEquiv
import FLT.Assumptions.MazurProof.N25F_XLocalFractionEmbedding
import FLT.Assumptions.MazurProof.N25F_XLocalDVR
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# The actual X-boundary order on the fixed function field

The coordinate-rigid common field is a fraction field of the actual X-local
DVR. Extend its genuine length order using `Ring.ordFrac`, then restrict its
logarithm to nonzero functions. The previously proved local order of W/X is
three, so the actual function X/W has pole order three at this point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_XBoundaryOrder

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_XChartFractionMap N25F_XChartFractionEquiv
open N25F_XLocalFractionEmbedding N25F_XLocalDVR

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

set_option synthInstance.maxHeartbeats 200000 in
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
  rw [h, map_inv₀, WithZero.log_inv, xLocalFractionOrder_xWGerm, WithZero.log_exp]

end MazurProof.N25F_XBoundaryOrder
