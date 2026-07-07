import FLT.Assumptions.MazurProof.RealTopologyS9
import FLT.Assumptions.MazurProof.RealTopologyS8
import FLT.Assumptions.MazurProof.RealTopologyS7
import FLT.Assumptions.MazurProof.RealTopologyS6
import FLT.Assumptions.MazurProof.RealTopologyS5
import FLT.Assumptions.MazurProof.RealTopologyS4

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology
open scoped Topology

namespace MazurProof.RealTopology

noncomputable section

example
    {A B e : ℝ} {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e} :
    let K := ComponentKer (A := A) (B := B) (e := e) hroot hderiv
    (0 : WeierstrassCurve.Affine.Point (shortW A B)) ∈ K ∧
      (∀ P, P ∈ K → -P ∈ K) ∧
        ∀ P Q, P ∈ K → Q ∈ K → P + Q ∈ K := by
  let K := ComponentKer (A := A) (B := B) (e := e) hroot hderiv
  change (0 : WeierstrassCurve.Affine.Point (shortW A B)) ∈ K ∧
    (∀ P, P ∈ K → -P ∈ K) ∧ ∀ P Q, P ∈ K → Q ∈ K → P + Q ∈ K
  exact ⟨K.zero_mem, (fun _ hP => K.neg_mem hP),
    fun _ _ hP hQ => K.add_mem hP hQ⟩

example
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    rootPoint (A := A) (B := B) (e := e) hroot hderiv ∈
      ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
  componentBit_rootPoint (A := A) (B := B) (e := e) hroot hderiv

theorem audit_componentKer_branch_exhaustion
    {A B e : ℝ} {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    P = 0 ∨ P = rootKerPoint hroot hderiv ∨
      (∃ x hx, P = upperRightKerPoint hposRight x hx) ∨
        (∃ x hx, P = lowerRightKerPoint hposRight x hx) := by
  rcases P with ⟨P, hP⟩
  cases P with
  | zero => exact Or.inl (Subtype.ext rfl)
  | some x y h =>
      right
      let Ps : ComponentKer (A := A) (B := B) (e := e) hroot hderiv := ⟨_, hP⟩
      change Ps = rootKerPoint hroot hderiv ∨
        (∃ x hx, Ps = upperRightKerPoint hposRight x hx) ∨
          (∃ x hx, Ps = lowerRightKerPoint hposRight x hx)
      rcases componentKer_some_eq_or_gt Ps rfl with hxe | hx
      · exact Or.inl (componentKer_eq_rootKerPoint_of_some_x_eq_root Ps rfl hxe)
      · right
        by_cases hy : 0 ≤ y
        · exact Or.inl
            ⟨x, hx, componentKer_eq_upperRightKerPoint_of_some_nonneg
              hposRight Ps rfl hx hy⟩
        · exact Or.inr
            ⟨x, hx, componentKer_eq_lowerRightKerPoint_of_some_neg
              hposRight Ps rfl hx (not_le.mp hy)⟩

example (x y a b : ℝ) : chordM x y a b = (y - b) / (x - a) := rfl
example (A x y a b : ℝ) :
    chordX A x y a b = chordM x y a b ^ 2 - A - x - a := rfl

example {A B x y a b : ℝ} (hD : x - a ≠ 0) :
    WeierstrassCurve.Affine.slope (shortW A B) x a y b = chordM x y a b :=
  shortW_slope_eq_chordM (A := A) (B := B) hD

#check tendsto_sigma_atTop
#check tendsto_sigma_nhdsGT_root
#check sqrt_shortCubic_hasDerivAt_of_pos

-- S8 upper/positive: upper branch input, positive chordY, same defect on `s`.
#check thetaDefect_upperRight_some_const_on_of_chordY_pos
-- S8 upper/negative: upper branch input, negative chordY, same defect on `s`.
#check thetaDefect_upperRight_some_const_on_of_chordY_neg
-- S8 lower/positive: lower branch input, positive chordY, same defect on `s`.
#check thetaDefect_lowerRight_some_const_on_of_chordY_pos
-- S8 lower/negative: lower branch input, negative chordY, same defect on `s`.
#check thetaDefect_lowerRight_some_const_on_of_chordY_neg

-- S9 input: local constancy on `Set.Ioi e` plus atTop convergence to `0`.
#check upperThetaDefectOnIoi_eq_zero_of_isLocallyConstant_of_tendsto_atTop_zero

-- AUDIT FAIL: the unconditional identity is false when `x = a` and `y ≠ b`.
theorem audit_chordY_identity_of_nonvertical
    {A x y a b : ℝ} (hD : x - a ≠ 0) :
    chordY A x y a b =
      -(b + chordM x y a b * (chordX A x y a b - a)) := by
  unfold chordY chordM
  field_simp [hD]
  ring

end

end MazurProof.RealTopology
