import FLT.Assumptions.MazurProof.N13SpecialFiniteBranchFaithfulness
import FLT.Assumptions.MazurProof.N13SpecialDivisorBranchOrders
import FLT.Assumptions.MazurProof.N13SpecialAbelCode

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Compute the four finite local point/divisor ideals, and identify the given
special divisor code with the weighted six actual point multiplicities.
-/

namespace MazurProof.N13SpecialFinitePointOrders

noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2

def finitePointOrder (a : K) (negative : Bool) : CurvePoint → ℕ
  | Sum.inl P => if P.1.1 = a ∧ P.1.2 = (if negative then 1 else 0) then 1 else 0
  | Sum.inr _ => 0

theorem affine_point_branch_ideal (a : K) (negative : Bool) (P : AffinePoint) :
    Ideal.map (finiteBranch a negative) (affinePointIdeal P) =
      Ideal.span ({PowerSeries.X ^ finitePointOrder a negative (Sum.inl P)} : Set N13SpecialInfinityBranchJets.P) := by
  have he : Ideal.map (finiteBranch a negative) (affinePointIdeal P) =
      Ideal.span ({PowerSeries.X + PowerSeries.C a - PowerSeries.C P.1.1,
        finiteBranch a negative N13GoodCoordinateRingTwo.yClass - PowerSeries.C P.1.2} :
          Set N13SpecialInfinityBranchJets.P) := by
    simp [affinePointIdeal, N13GoodCoordinateRingTwo.mumfordIdeal,
      N13GoodCoordinateRingTwo.ySubClass, Ideal.map_span, Set.image_pair, evalBase]
  rw [he]
  simp only [finitePointOrder]
  by_cases hx : P.1.1 = a
  · by_cases hy : P.1.2 = (if negative then 1 else 0)
    · rw [if_pos ⟨hx, hy⟩, pow_one, hx, add_sub_cancel_right]
      apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
      apply PowerSeries.X_dvd_iff.mpr
      simp only [map_sub, PowerSeries.constantCoeff_C, finiteBranch_y_constant, hy, sub_self]
    · rw [if_neg (fun h => hy h.2), pow_zero, Ideal.span_singleton_one]
      have hu : IsUnit (finiteBranch a negative N13GoodCoordinateRingTwo.yClass - PowerSeries.C P.1.2) := by
        rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C, finiteBranch_y_constant]
        exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hy))
      exact (Ideal.span _).eq_top_of_isUnit_mem (Ideal.subset_span (by simp)) hu
  · rw [if_neg (fun h => hx h.1), pow_zero, Ideal.span_singleton_one]
    have hu : IsUnit (PowerSeries.X + PowerSeries.C a - PowerSeries.C P.1.1 : N13SpecialInfinityBranchJets.P) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simpa using (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx)) : IsUnit (a - P.1.1))
    exact (Ideal.span _).eq_top_of_isUnit_mem (Ideal.subset_span (by simp)) hu

theorem point_branch_ideal (a : K) (negative : Bool) (P : CurvePoint) :
    Ideal.map (finiteBranch a negative) (point P).affineIdeal =
      Ideal.span ({PowerSeries.X ^ finitePointOrder a negative P} : Set N13SpecialInfinityBranchJets.P) := by
  cases P with
  | inl P =>
    unfold point
    split <;> exact affine_point_branch_ideal a negative P
  | inr P => simp [point, infinityPoint, finitePointOrder, Ideal.map_top]

def finiteDivisorOrder (a : K) (negative : Bool) : EffectiveDivisorTwo → ℕ :=
  Sym2.lift ⟨fun P Q => finitePointOrder a negative P + finitePointOrder a negative Q,
    fun P Q => Nat.add_comm _ _⟩

@[simp] theorem finiteDivisorOrder_mk (a : K) (negative : Bool) (P Q : CurvePoint) :
    finiteDivisorOrder a negative s(P, Q) = finitePointOrder a negative P + finitePointOrder a negative Q := rfl

theorem divisor_branch_ideal (a : K) (negative : Bool) (D : EffectiveDivisorTwo) :
    Ideal.map (finiteBranch a negative) (ofDivisor D).affineIdeal =
      Ideal.span ({PowerSeries.X ^ finiteDivisorOrder a negative D} : Set N13SpecialInfinityBranchJets.P) := by
  refine Sym2.inductionOn D ?_
  intro P Q
  change Ideal.map (finiteBranch a negative) ((point P).affineIdeal * (point Q).affineIdeal) = _
  rw [Ideal.map_mul, point_branch_ideal, point_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl

def finiteTensorOrder (a : K) (negative : Bool) (D E : EffectiveDivisorTwo) : ℕ :=
  finiteDivisorOrder a negative D + finiteDivisorOrder a negative E

theorem tensor_branch_ideal (a : K) (negative : Bool) (D E : EffectiveDivisorTwo) :
    Ideal.map (finiteBranch a negative) (tensor (ofDivisor D) (ofDivisor E)).affineIdeal =
      Ideal.span ({PowerSeries.X ^ finiteTensorOrder a negative D E} : Set N13SpecialInfinityBranchJets.P) := by
  change Ideal.map (finiteBranch a negative) ((ofDivisor D).affineIdeal * (ofDivisor E).affineIdeal) = _
  rw [Ideal.map_mul, divisor_branch_ideal, divisor_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl

theorem pointCode_eq_counts (P : CurvePoint) :
    N13SpecialAbelCode.pointCode P =
      (finitePointOrder 0 false P : ZMod 19) - finitePointOrder 0 true P +
        7 * (finitePointOrder 1 false P : ZMod 19) - 7 * finitePointOrder 1 true P +
        8 * (N13SpecialDivisorBranchOrders.pointOrder false P : ZMod 19) -
        8 * N13SpecialDivisorBranchOrders.pointOrder true P := by
  cases P with
  | inl P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.1 (ZMod.pow_card P.1.1) with hx | hx <;>
      rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.2 (ZMod.pow_card P.1.2) with hy | hy <;>
      simp [N13SpecialAbelCode.pointCode, N13SpecialAbelCode.baseAmplitude,
        N13AbelFiberTwoModel.curvePointEquiv, finitePointOrder,
        N13SpecialDivisorBranchOrders.pointOrder, hx, hy]
  | inr P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1 (ZMod.pow_card P.1) with hv | hv <;>
      simp [N13SpecialAbelCode.pointCode, N13SpecialAbelCode.baseAmplitude,
        N13AbelFiberTwoModel.curvePointEquiv, finitePointOrder,
        N13SpecialDivisorBranchOrders.pointOrder, hv]

def countCode (D : EffectiveDivisorTwo) : ZMod 19 :=
  (finiteDivisorOrder 0 false D : ZMod 19) - finiteDivisorOrder 0 true D +
    7 * (finiteDivisorOrder 1 false D : ZMod 19) - 7 * finiteDivisorOrder 1 true D +
    8 * (N13SpecialDivisorBranchOrders.divisorOrder false D : ZMod 19) -
    8 * N13SpecialDivisorBranchOrders.divisorOrder true D

theorem divisorCode_eq_counts (D : EffectiveDivisorTwo) : N13SpecialAbelCode.divisorCode D = countCode D := by
  refine Sym2.inductionOn D ?_
  intro P Q
  rw [N13SpecialAbelCode.divisorCode_mk, pointCode_eq_counts, pointCode_eq_counts]
  simp only [countCode, finiteDivisorOrder_mk, N13SpecialDivisorBranchOrders.divisorOrder_mk, Nat.cast_add]
  ring

end
end MazurProof.N13SpecialFinitePointOrders
