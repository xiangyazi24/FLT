import FLT.Assumptions.MazurProof.N25F_YZLocalFractionEmbedding
import FLT.Assumptions.MazurProof.N25F_YZLocalDVR
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! Signed orders at the actual YZ-boundary point [0:1:1:0]. The existing
length order extends through the coordinate-rigid map to the fixed W-chart
function field. Both Y/W and Z/W have genuine pole order one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace MazurProof.N25F_YZBoundaryOrder

open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open N25F_YZLocalZUnit N25F_YZLocalDVR N25F_YZLocalFractionEmbedding
open N25F_ZChartFractionMap

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W

/-- The actual YZ-local length order extended to the fixed function field. -/
def yzLocalFractionOrder : K →*₀ WithZero (Multiplicative ℤ) := by
  letI : Algebra YZLocalRing K := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing K := yzLocalToFraction_isFractionRing
  exact Ring.ordFrac YZLocalRing

/-- The genuine signed boundary coefficient of a nonzero function at [0:1:1:0]. -/
def yzBoundaryOrder : Additive Kˣ →+ ℤ where
  toFun u := WithZero.log (yzLocalFractionOrder (u.toMul : K))
  map_zero' := by change WithZero.log (yzLocalFractionOrder (1 : K)) = 0; simp
  map_add' u v := by
    change WithZero.log (yzLocalFractionOrder ((u.toMul : K) * (v.toMul : K))) = _
    rw [map_mul]
    exact WithZero.log_mul
      ((Units.isUnit u.toMul).map yzLocalFractionOrder).ne_zero
      ((Units.isUnit v.toMul).map yzLocalFractionOrder).ne_zero

private theorem ordFrac_image_eq_exp
    {R L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L]
    (a : R) (ha : a ≠ 0) (n : ℕ) (hord : Ring.ord R a = n) :
    Ring.ordFrac R (algebraMap R L a) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl

/-- The common-field image of the existing W/Y germ has order one. -/
theorem yzLocalFractionOrder_yzWGerm :
    yzLocalFractionOrder (yzLocalToFraction yzWGerm) = WithZero.exp (1 : ℤ) := by
  letI : Algebra YZLocalRing K := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing K := yzLocalToFraction_isFractionRing
  exact ordFrac_image_eq_exp (L := K) yzWGerm yzWGerm_ne_zero 1 yzWGerm_ord_eq_one

/-- The common-field image of the existing unit Z/Y has order zero. -/
theorem yzLocalFractionOrder_yzZGerm :
    yzLocalFractionOrder (yzLocalToFraction yzZGerm) = 1 := by
  letI : Algebra YZLocalRing K := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing K := yzLocalToFraction_isFractionRing
  change Ring.ordFrac YZLocalRing (algebraMap YZLocalRing K yzZGerm) = 1
  simpa only [Nat.cast_zero, WithZero.exp_zero] using ordFrac_image_eq_exp (L := K) yzZGerm yzZGerm_isUnit.ne_zero 0
    (Ring.ord_of_isUnit yzZGerm_isUnit)

/-- Y/W has a pole of order one, with positive-zero/negative-pole convention. -/
theorem yzBoundaryOrder_qy :
    yzBoundaryOrder (Additive.ofMul (Units.mk0
      (algebraMap W K qy) fraction_qy_ne_zero)) = -1 := by
  change WithZero.log (yzLocalFractionOrder (algebraMap W K qy)) = -1
  have h : algebraMap W K qy = (yzLocalToFraction yzWGerm)⁻¹ := by
    rw [yzLocalToFraction_yzWGerm, one_div, inv_inv]
  rw [h, map_inv₀, WithZero.log_inv, yzLocalFractionOrder_yzWGerm, WithZero.log_exp]

/-- Z/W has a pole of order one, since Z/Y is a unit at this boundary point. -/
theorem yzBoundaryOrder_qz :
    yzBoundaryOrder (Additive.ofMul (Units.mk0
      (algebraMap W K qz) fraction_qz_ne_zero)) = -1 := by
  change WithZero.log (yzLocalFractionOrder (algebraMap W K qz)) = -1
  have h : algebraMap W K qz =
      yzLocalToFraction yzZGerm * (yzLocalToFraction yzWGerm)⁻¹ := by
    rw [yzLocalToFraction_yzZGerm, yzLocalToFraction_yzWGerm, one_div, inv_inv]
    exact (div_mul_cancel₀ _ fraction_qy_ne_zero).symm
  rw [h, map_mul, yzLocalFractionOrder_yzZGerm, one_mul, map_inv₀,
    WithZero.log_inv, yzLocalFractionOrder_yzWGerm, WithZero.log_exp]

end MazurProof.N25F_YZBoundaryOrder
