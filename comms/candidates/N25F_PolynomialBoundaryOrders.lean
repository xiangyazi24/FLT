import FLT.Assumptions.MazurProof.N25F_XBoundaryZOrder
import FLT.Assumptions.MazurProof.N25F_YZBoundaryOrder
import FLT.Assumptions.MazurProof.N25F_ZBoundaryOrder
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Valuation.IsTrivialOn

/-! Exact boundary orders of every nonzero binary polynomial in the actual
function qz=Z/W. This is a proved subcase, not the general product formula. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_PolynomialBoundaryOrders
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder N25F_XBoundaryZOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W

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


/-- The actual X boundary order of p(Z/W) is minus 1 times its degree. -/
theorem xLocalFractionOrder_aeval_qz (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    xLocalFractionOrder (p.aeval (algebraMap W K qz)) =
      WithZero.exp (-(1 * p.natDegree : ℤ)) := by
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
  letI : IsScalarTower (ZMod 2) XLocalRing K :=
    IsScalarTower.of_algebraMap_eq fun a => (xLocalToFraction.commutes a).symm
  have hzlog : WithZero.log (xLocalFractionOrder (algebraMap W K qz)) = -1 :=
    xBoundaryOrder_qz
  have hz : xLocalFractionOrder (algebraMap W K qz) = WithZero.exp (-(1 : ℤ)) :=
    (WithZero.exp_log (((isUnit_iff_ne_zero.mpr fraction_qz_ne_zero).map
      xLocalFractionOrder).ne_zero)).symm.trans (congrArg WithZero.exp hzlog)
  exact ordFrac_aeval_at_pole (R := XLocalRing) (algebraMap W K qz) 1
    (by decide) hz p hp

/-- The actual YZ boundary order of p(Z/W) is minus 1 times its degree. -/
theorem yzLocalFractionOrder_aeval_qz (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    yzLocalFractionOrder (p.aeval (algebraMap W K qz)) =
      WithZero.exp (-(1 * p.natDegree : ℤ)) := by
  letI : Algebra YZLocalRing K := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing K := yzLocalToFraction_isFractionRing
  letI : IsScalarTower (ZMod 2) YZLocalRing K :=
    IsScalarTower.of_algebraMap_eq fun a => (yzLocalToFraction.commutes a).symm
  have hzlog : WithZero.log (yzLocalFractionOrder (algebraMap W K qz)) = -1 :=
    yzBoundaryOrder_qz
  have hz : yzLocalFractionOrder (algebraMap W K qz) = WithZero.exp (-(1 : ℤ)) :=
    (WithZero.exp_log (((isUnit_iff_ne_zero.mpr fraction_qz_ne_zero).map
      yzLocalFractionOrder).ne_zero)).symm.trans (congrArg WithZero.exp hzlog)
  exact ordFrac_aeval_at_pole (R := YZLocalRing) (algebraMap W K qz) 1
    (by decide) hz p hp

/-- The actual Z boundary order of p(Z/W) is minus 2 times its degree. -/
theorem zLocalFractionOrder_aeval_qz (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    zLocalFractionOrder (p.aeval (algebraMap W K qz)) =
      WithZero.exp (-(2 * p.natDegree : ℤ)) := by
  letI : Algebra ZLocalRing K := zLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing K := zLocalToFraction_isFractionRing
  letI : IsScalarTower (ZMod 2) ZLocalRing K :=
    IsScalarTower.of_algebraMap_eq fun a => (zLocalToFraction.commutes a).symm
  have hzlog : WithZero.log (zLocalFractionOrder (algebraMap W K qz)) = -2 :=
    zBoundaryOrder_qz
  have hz : zLocalFractionOrder (algebraMap W K qz) = WithZero.exp (-(2 : ℤ)) :=
    (WithZero.exp_log (((isUnit_iff_ne_zero.mpr fraction_qz_ne_zero).map
      zLocalFractionOrder).ne_zero)).symm.trans (congrArg WithZero.exp hzlog)
  exact ordFrac_aeval_at_pole (R := ZLocalRing) (algebraMap W K qz) 2
    (by decide) hz p hp

end MazurProof.N25F_PolynomialBoundaryOrders
