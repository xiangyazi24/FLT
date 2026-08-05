import FLT.Assumptions.MazurProof.XDelta19GoodDescent
import FLT.Assumptions.MazurProof.XDelta19GoodDualDescent

/-!
# Weak three-descent on the good conductor-nineteen model

The flex function has cubeclass `1`, `19`, or `19²`.  Translation by the
two visible rational flexes converts the latter two cases to the cube
case.  Surjectivity of the complementary isogeny and the verified
dual-forward composition then show that every rational point is a
threefold multiple up to one of the two nonzero visible three-torsion
points.
-/

namespace MazurProof.XDelta19GoodWeakDescent

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodDescent
open MazurProof.XDelta19GoodDualDescent

noncomputable section

/-- Every rational point on the good model is a threefold multiple up to
one of the two visible rational three-torsion points. -/
theorem weak_three_descent (P : GoodPoint) :
    ∃ Q : GoodPoint,
      P = 3 • Q ∨ P = goodT + 3 • Q ∨ P = goodTNeg + 3 • Q := by
  cases P with
  | zero =>
      exact ⟨0, Or.inl (by rfl)⟩
  | some x y h =>
      have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hySq : y ^ 2 = (76 : ℚ) ^ 2 := by
          rw [hx] at hcurve
          norm_num [OnGood] at hcurve ⊢
          exact hcurve
        rcases eq_or_eq_neg_of_sq_eq_sq y 76 hySq with hy | hy
        · refine ⟨0, Or.inr (Or.inl ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h =
            goodT + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [goodT, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
        · refine ⟨0, Or.inr (Or.inr ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h =
            goodTNeg + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [goodTNeg, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
      · have hab :
            (y - (8 * x + 76)) * (y + (8 * x + 76)) = x ^ 3 := by
          calc
            (y - (8 * x + 76)) * (y + (8 * x + 76)) =
                y ^ 2 - (8 * x + 76) ^ 2 := by ring
            _ = x ^ 3 := by rw [hcurve]; ring
        obtain ⟨r, halpha | halpha | halpha⟩ :=
          good_alpha_cubeclass hcurve
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              h halpha.symm hr
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          refine ⟨Q, Or.inl ?_⟩
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                dualThreeIsogenyPoint Qd := hQd.symm
            _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
              rw [hQ]
            _ = 3 • Q := dual_comp_threeIsogenyPoint Q
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L :=
            WeierstrassCurve.Affine.slope goodCurve x 0 y 76
          let X :=
            WeierstrassCurve.Affine.addX goodCurve x 0 L
          let Y :=
            WeierstrassCurve.Affine.addY goodCurve x 0 y L
          let hns :
              WeierstrassCurve.Affine.Nonsingular goodCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h goodT_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : GoodPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodT = Pplus := by
            rw [goodT]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -76 * r / x
          have hrp : rp ≠ 0 :=
            div_ne_zero (mul_ne_zero (by norm_num) hr) hx
          have halphaP : rp ^ 3 = Y - (8 * X + 76) := by
            symm
            have hid := add_goodT_alpha_identity hx hcurve
            change Y - (8 * X + 76) =
              -23104 * (y - (8 * x + 76)) / x ^ 3 at hid
            rw [hid, halpha]
            dsimp [rp]
            field_simp [hx]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              hns halphaP hrp
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
                rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodT = 3 • Q :=
            hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inr ?_)⟩
          rw [goodTNeg_eq_neg]
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                -goodT +
                  ((WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                    goodT) := by abel
            _ = -goodT + 3 • Q := by rw [hsum]
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L :=
            WeierstrassCurve.Affine.slope goodCurve x 0 y (-76)
          let X :=
            WeierstrassCurve.Affine.addX goodCurve x 0 L
          let Y :=
            WeierstrassCurve.Affine.addY goodCurve x 0 y L
          let hns :
              WeierstrassCurve.Affine.Nonsingular goodCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h goodTNeg_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : GoodPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodTNeg = Pplus := by
            rw [goodTNeg]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -2 * x / (19 * r ^ 2)
          have hrp : rp ≠ 0 := by
            exact div_ne_zero (mul_ne_zero (by norm_num) hx)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
          have halphaP : rp ^ 3 = Y - (8 * X + 76) := by
            symm
            have hid := add_goodTNeg_alpha_identity hx hcurve
            change Y - (8 * X + 76) =
              -152 * (y + (8 * x + 76)) ^ 2 / x ^ 3 at hid
            rw [hid]
            have hbeta :
                y + (8 * x + 76) = x ^ 3 / (361 * r ^ 3) := by
              apply (eq_div_iff
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr))).2
              rw [← hab, halpha]
              ring
            rw [hbeta]
            dsimp [rp]
            field_simp [hx, hr]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              hns halphaP hrp
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
                rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodTNeg = 3 • Q :=
            hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inl ?_)⟩
          rw [goodTNeg_eq_neg] at hsum
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                goodT +
                  ((WeierstrassCurve.Affine.Point.some x y h : GoodPoint) -
                    goodT) := by abel
            _ = goodT + 3 • Q := by
              congr 1

end

end MazurProof.XDelta19GoodWeakDescent
