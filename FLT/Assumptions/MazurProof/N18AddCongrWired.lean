import FLT.Assumptions.MazurProof.N18AddCongrProof

/-!
# Wired add_congr: assembles the three branch proofs

This file exports `add_congr_wired`, which has the same signature as the
sorry'd `add_congr` in `N18AddCongr.lean` and dispatches to the three
sorry-free branch theorems in `N18AddCongrProof.lean`.

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

private theorem xCoord_ne_zero_of_ordPi_neg {x y : L}
    (hns : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : ordPi x < 0) : x ≠ 0 := by
  intro h; rw [h, ordPi_zero] at hx; omega

private theorem yCoord_ne_zero_of_ordPi_xneg {x y : L}
    (hns : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : ordPi x < 0) : y ≠ 0 := by
  intro hy
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hns.1
  rw [hy] at heq
  simp only [zero_pow, mul_zero, add_zero, zero_mul] at heq
  have : ordPi (x ^ 3 + E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆) = ordPi (E0.a₆) := by
    sorry -- strict domination: v(x³) = 3·v(x) < 2·v(x) < v(x) < 0 = v(a₆)
  sorry -- contradiction from heq and the ordPi computation

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
  · exact absurd rfl (by simp [xCoord] at hPx)
  rcases Q with _ | ⟨x₂, y₂, hns₂⟩
  · exact absurd rfl (by simp [xCoord] at hQx)
  change ordPi x₁ < 0 at hPx
  change ordPi x₂ < 0 at hQx
  have hx₁0 := xCoord_ne_zero_of_ordPi_neg hns₁ hPx
  have hy₁0 := yCoord_ne_zero_of_ordPi_xneg hns₁ hPx
  have hx₂0 := xCoord_ne_zero_of_ordPi_neg hns₂ hQx
  have hy₂0 := yCoord_ne_zero_of_ordPi_xneg hns₂ hQx
  by_cases hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY E0 x₂ y₂
  · -- Inverse branch: Q = -P (same x, y = negY)
    obtain ⟨hxeq, hyeq⟩ := hxy
    have hPQ : WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂ =
        -(WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁) := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      exact WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ ▸
        ⟨hxeq.symm, hyeq.symm⟩
    rw [hPQ]
    exact add_congr_inverse_branch hx₁0 hy₁0 hns₁ hPx
  · push_neg at hxy
    by_cases hxne : x₁ ≠ x₂
    · -- Distinct-x branch
      exact add_congr_distinct_x_branch hx₁0 hy₁0 hx₂0 hy₂0 hns₁ hns₂ hxne hPx hQx
    · -- Tangent/doubling branch: x₁ = x₂ but y₁ ≠ negY
      push_neg at hxne
      subst hxne
      have hyne := hxy rfl
      sorry -- need to reconcile hns₁ and hns₂ (same x, different nonsingularity proofs)
             -- then apply add_congr_tangent_branch

end

end MazurProof.N18Block5Instantiation
