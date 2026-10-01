import FLT.Assumptions.MazurProof.N18AddCongrProof

/-!
# Wired add_congr: assembles the three branch proofs

Import chain: N18AddCongr ← N18AddCongrProof ← N18AddCongrWired (no cycle).
-/

open scoped Classical
open scoped WeierstrassCurve.Affine

namespace MazurProof.N18Block5Instantiation

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18Block5Instantiation.AddCongr
open MazurProof.N18Block5Instantiation.AddCongrProof

noncomputable section

private def xCoord : E0Point → L
  | .zero => 0
  | .some x _ _ => x

private theorem xCoord_ne_zero_of_ordPi_neg {x y : L}
    (_ : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : ordPi x < 0) : x ≠ 0 := by
  intro h; rw [h, ordPi_zero] at hx; omega

private theorem yCoord_ne_zero_of_ordPi_xneg {x y : L}
    (hns : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : ordPi x < 0) : y ≠ 0 := by
  have hx0 : x ≠ 0 := by intro h; rw [h, ordPi_zero] at hx; omega
  intro hy; subst hy
  have heq := (WeierstrassCurve.Affine.equation_iff x 0).mp hns.1
  simp only [E0, zero_pow, mul_zero, add_zero, zero_mul, zero_add] at heq
  -- x³-x²-5x+5 = (x-1)(x²-5), both factors nonzero when v(x)<0
  have hx1 : x - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero.mp h, ordPi_one] at hx; omega
  have hx2_5 : x ^ 2 - 5 ≠ 0 := by
    intro h
    have hvx2 : ordPi (x ^ 2) = 2 * ordPi x := by
      rw [show x ^ 2 = x * x from by ring, ordPi_mul hx0 hx0]; ring
    have : ordPi (x ^ 2 - (5 : L)) = ordPi (x ^ 2) := by
      rw [show x ^ 2 - (5 : L) = x ^ 2 + (-(5 : L)) from by ring]
      exact ordPi_add_eq_of_lt (pow_ne_zero 2 hx0) (by norm_num)
        (by rw [hvx2, ordPi_neg]
            have : 0 ≤ ordPi ((5 : ℤ) : L) := zero_le_ordPi_intCast 5
            simp only [Int.cast_ofNat] at this; omega)
    rw [h, ordPi_zero, hvx2] at this; omega
  apply mul_ne_zero hx1 hx2_5
  linear_combination -heq

/-- **Package I `add_congr`, wired from the three branch proofs.** -/
theorem add_congr_wired (P Q : E0Point)
    (hP : P = 0 ∨ ordPi (xCoord P) < 0)
    (hQ : Q = 0 ∨ ordPi (xCoord Q) < 0) :
    zParam (P + Q) - zParam P - zParam Q = 0 ∨
    v (zParam P) + v (zParam Q) ≤ v (zParam (P + Q) - zParam P - zParam Q) := by
  rcases hP with rfl | hPx
  · left; rw [zero_add Q, zParam_zero]; ring
  rcases hQ with rfl | hQx
  · left; rw [add_zero P, zParam_zero]; ring
  rcases P with _ | ⟨x₁, y₁, hns₁⟩
  · simp [xCoord] at hPx
  rcases Q with _ | ⟨x₂, y₂, hns₂⟩
  · simp [xCoord] at hQx
  simp only [xCoord] at hPx hQx
  have hx₁0 := xCoord_ne_zero_of_ordPi_neg hns₁ hPx
  have hy₁0 := yCoord_ne_zero_of_ordPi_xneg hns₁ hPx
  have hx₂0 := xCoord_ne_zero_of_ordPi_neg hns₂ hQx
  have hy₂0 := yCoord_ne_zero_of_ordPi_xneg hns₂ hQx
  -- Case split on Point.add branches and dispatch to the three sorry-free proofs.
  -- The type-matching is fiddly (dependent types in Point.neg, 2*z vs z+z);
  -- each branch is independently sorry-free in N18AddCongrProof.lean.
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = WeierstrassCurve.Affine.negY E0 x₁ y₂
    · have hy₂ : y₂ = WeierstrassCurve.Affine.negY E0 x₁ y₁ := by
        rw [hy, WeierstrassCurve.Affine.negY_negY]
      have hQnegP :
          WeierstrassCurve.Affine.Point.some x₁ y₂ hns₂ =
            -WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ := by
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨rfl, hy₂⟩
      rw [hQnegP]
      exact add_congr_inverse_branch hx₁0 hy₁0 hns₁ hPx
    · have hyEq : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne hns₁.1 hns₂.1 rfl hy
      subst y₂
      cases Subsingleton.elim hns₂ hns₁
      simpa only [two_mul, sub_sub] using
        add_congr_tangent_branch hx₁0 hy₁0 hns₁ hPx (fun h => hy h.symm)
  · exact add_congr_distinct_x_branch
      hx₁0 hy₁0 hx₂0 hy₂0 hns₁ hns₂ hx hPx hQx

end

end MazurProof.N18Block5Instantiation
