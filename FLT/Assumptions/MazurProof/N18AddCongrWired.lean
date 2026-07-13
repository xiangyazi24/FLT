import FLT.Assumptions.MazurProof.N18AddCongrProof
import FLT.Assumptions.MazurProof.N18Block5Instantiation

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
  -- heq : 0 = x³ - x² - 5x + 5
  -- Factor: x³ - x² - 5x + 5 = (x-1)(x²-5)
  have hfact : x ^ 3 + (-1 : L) * x ^ 2 + (-5 : L) * x + (5 : L) = (x - 1) * (x ^ 2 - 5) := by
    ring
  -- v(x-1) = v(x) < 0 (strict domination: v(x) < 0 = v(1))
  have hx1 : x - 1 ≠ 0 := by
    intro h; have : x = 1 := by linarith
    rw [this, ordPi_one] at hx; omega
  have hvx1 : ordPi (x - 1) = ordPi x := by
    rw [show x - 1 = x + (-1 : L) from by ring]
    exact ordPi_add_eq_of_lt hx0 (by norm_num)
      (by rw [ordPi_neg, ordPi_one]; linarith)
  -- v(x²-5) = 2v(x) < 0 (strict domination: v(x²) = 2v(x) < 0 ≤ v(5))
  have hx2_5 : x ^ 2 - 5 ≠ 0 := by
    intro h
    have hvx2 : ordPi (x ^ 2) = 2 * ordPi x := by
      rw [show x ^ 2 = x * x from by ring, ordPi_mul hx0 hx0]; ring
    have : ordPi (x ^ 2 - (5 : L)) = ordPi (x ^ 2) := by
      rw [show x ^ 2 - (5 : L) = x ^ 2 + (-(5 : L)) from by ring]
      exact ordPi_add_eq_of_lt (pow_ne_zero 2 hx0) (by norm_num)
        (by rw [hvx2, ordPi_neg]; have := zero_le_ordPi_intCast 5; omega)
    rw [h, ordPi_zero, hvx2] at this; omega
  -- Product is nonzero
  have hprod : (x - 1) * (x ^ 2 - 5) ≠ 0 := mul_ne_zero hx1 hx2_5
  -- But heq says the product = 0
  exact hprod (hfact ▸ by linarith [heq])

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
  by_cases hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY E0 x₂ y₂
  · obtain ⟨hxeq, hyeq⟩ := hxy
    have hPQ : WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂ =
        -(WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁) := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      exact WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ ▸
        ⟨hxeq.symm, hyeq.symm⟩
    rw [hPQ]
    exact add_congr_inverse_branch hx₁0 hy₁0 hns₁ hPx
  · push_neg at hxy
    by_cases hxne : x₁ ≠ x₂
    · exact add_congr_distinct_x_branch hx₁0 hy₁0 hx₂0 hy₂0 hns₁ hns₂ hxne hPx hQx
    · push_neg at hxne; subst hxne
      have hyne := hxy rfl
      -- x₁ = x₂, y₁ ≠ negY. Two points on same x with same nonsingularity x-coord.
      -- Since the curve equation y²+a₁xy+a₃y = RHS(x) has at most 2 y-solutions,
      -- and negY gives the other one, y₁ = y₂ (same point, doubling case).
      have hy₁₂ : y₁ = y₂ := by
        have h1 := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp hns₁.1
        have h2 := (WeierstrassCurve.Affine.equation_iff x₁ y₂).mp hns₂.1
        have hdiff : (y₁ - y₂) * (y₁ + y₂ + E0.a₁ * x₁ + E0.a₃) = 0 := by
          linear_combination h1 - h2
        rcases mul_eq_zero.mp hdiff with h | h
        · exact sub_eq_zero.mp h
        · exfalso; apply hyne
          show y₂ = -(y₁ + E0.a₁ * x₁ + E0.a₃)
          linarith
      subst hy₁₂
      have hns_eq : hns₁ = hns₂ := Subsingleton.elim _ _
      subst hns_eq
      exact add_congr_tangent_branch hx₁0 hy₁0 hns₁ hPx hyne

end

end MazurProof.N18Block5Instantiation
