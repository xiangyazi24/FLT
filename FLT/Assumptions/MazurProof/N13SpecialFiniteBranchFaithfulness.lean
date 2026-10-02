import FLT.Assumptions.MazurProof.N13SpecialFiniteBranchJets

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The finite Hensel maps are faithful: their product is the translated
nonzero polynomial norm. Translation by a has an explicit inverse, so the
base-polynomial evaluation cannot kill a nonzero polynomial.
-/

namespace MazurProof.N13SpecialFiniteBranchFaithfulness

noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets

abbrev R := N13GoodCoordinateRingTwo.CoordinateRing

theorem shift_comp_cancel (p : K[X]) (a : K) :
    (p.comp (X + C a)).comp (X - C a) = p := by
  rw [Polynomial.comp_assoc]
  simp

theorem evalBase_ne_zero (a : K) (p : K[X]) (hp : p ≠ 0) : evalBase a p ≠ 0 := by
  intro h
  have he : beta (p.comp (X + C a)) = 0 := (beta_comp a p).trans h
  have hpcomp : p.comp (X + C a) = 0 := by
    apply Polynomial.coe_injective K
    simpa only [beta_eq_coe, Polynomial.coe_zero] using he
  have hc := congrArg (fun q : K[X] => q.comp (X - C a)) hpcomp
  rw [shift_comp_cancel, Polynomial.zero_comp] at hc
  exact hp hc

theorem branchZero_conjugate (a : K) (z : R) :
    branchZero a (N13SpecialAffineNorm.conjugate z) = branchOne a z := by
  have hz : z = N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) :=
    (N13GoodCoordinateRingTwo.recompose z).symm
  rw [hz, N13SpecialAffineNorm.conjugate_linear]
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, map_sub, map_neg,
    branchZero_xClass, branchOne_xClass, branchZero_yClass, branchOne_yClass, rootOne]
  have hh : evalBase a N13GoodCoordinateRingTwo.hPoly = beta (hAt a) := (beta_comp a _).symm
  rw [hh]
  ring

theorem finite_branch_product (a : K) (z : R) :
    branchZero a z * branchOne a z = evalBase a (N13SpecialAffineNorm.norm z) := by
  rw [← branchZero_conjugate, ← map_mul, N13SpecialAffineNorm.mul_conjugate, branchZero_xClass]

theorem branchZero_ne_zero (a : K) (z : R) (hz : z ≠ 0) : branchZero a z ≠ 0 := by
  have hn := evalBase_ne_zero a _ (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← finite_branch_product] at hn
  exact left_ne_zero_of_mul hn

theorem branchOne_ne_zero (a : K) (z : R) (hz : z ≠ 0) : branchOne a z ≠ 0 := by
  have hn := evalBase_ne_zero a _ (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← finite_branch_product] at hn
  exact right_ne_zero_of_mul hn

def finiteBranch (a : K) (negative : Bool) : R →+* P :=
  if negative then branchOne a else branchZero a

theorem finiteBranch_ne_zero (a : K) (negative : Bool) (z : R) (hz : z ≠ 0) :
    finiteBranch a negative z ≠ 0 := by
  cases negative
  · exact branchZero_ne_zero a z hz
  · exact branchOne_ne_zero a z hz

@[simp] theorem finiteBranch_xClass (a : K) (negative : Bool) (p : K[X]) :
    finiteBranch a negative (N13GoodCoordinateRingTwo.xClass p) = evalBase a p := by
  cases negative <;> simp [finiteBranch]

theorem finiteBranch_y_constant (a : K) (negative : Bool) :
    PowerSeries.constantCoeff (finiteBranch a negative N13GoodCoordinateRingTwo.yClass) =
      (if negative then 1 else 0) := by
  cases negative <;> simp [finiteBranch, rootZero_constant, rootOne_constant]

end
end MazurProof.N13SpecialFiniteBranchFaithfulness
