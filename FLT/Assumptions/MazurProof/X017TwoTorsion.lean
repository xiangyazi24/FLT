import FLT.Assumptions.MazurProof.X017Model
import FLT.Assumptions.MazurProof.RationalPointsN15ExactSequence

/-!
# Rational two-torsion on the standard X₀(17) model

A nonzero rational two-torsion point on

`Y² = X(X² + 30X + 289)`

has vertical coordinate zero.  Its horizontal coordinate therefore vanishes
or is a rational root of `X²+30X+289`.  The latter polynomial is
`(X+15)²+64`, so it has no rational root.  Thus the only rational
two-torsion points are the point at infinity and `(0,0)`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017TwoTorsion

open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model
open MazurProof.RationalPointsN15ExactSequence

noncomputable section

/-- Every rational two-torsion point is either the point at infinity or the
visible kernel point `(0,0)`. -/
theorem twoTorsion_value_eq_zero_or_K
    (P : TwoTorsion (Point standard)) :
    P.1 = 0 ∨ P.1 = K := by
  rcases P with ⟨P, hP⟩
  cases P with
  | zero =>
      exact Or.inl rfl
  | some x y hns =>
      right
      have h2 :
          (Point.some x y hns : Point standard) +
              Point.some x y hns = 0 := by
        simpa [two_nsmul] using hP
      have hyneg : y = negY standard x y := by
        by_contra hne
        have hs := Point.add_self_of_Y_ne
          (W := standard) (h₁ := hns) hne
        rw [h2] at hs
        exact Point.some_ne_zero _ hs.symm
      have hy : y = 0 := by
        rw [StandardTwoIsogeny.curve_negY] at hyneg
        linarith
      have hcurve := StandardTwoIsogeny.curve_equation.mp hns.left
      have hprod :
          x * (x ^ 2 + a17 * x + b17) = 0 := by
        rw [hy] at hcurve
        exact hcurve.symm
      rcases mul_eq_zero.mp hprod with hx | hquad
      · unfold K StandardTwoIsogeny.kernelPoint
        rw [Point.some.injEq]
        exact ⟨hx, hy⟩
      · exfalso
        have hpositive :
            0 < x ^ 2 + a17 * x + b17 := by
          norm_num [a17, b17, veluT]
          nlinarith [sq_nonneg (x + 15)]
        exact (ne_of_gt hpositive) hquad

/-- The visible kernel point is genuinely killed by multiplication by two. -/
theorem two_nsmul_K : 2 • K = 0 := by
  change
    2 • StandardTwoIsogeny.kernelPoint a17 b17 = 0
  simpa [two_nsmul] using
    (StandardTwoIsogeny.kernel_add_self (a := a17) (b := b17))

/-- The rational two-torsion subtype is explicitly encoded by a Boolean:
`false` denotes the point at infinity and `true` denotes `(0,0)`. -/
noncomputable def twoTorsionEquivBool :
    TwoTorsion (Point standard) ≃ Bool where
  toFun P :=
    if P.1 = 0 then false else true
  invFun b :=
    if b then
      ⟨K, two_nsmul_K⟩
    else
      ⟨0, by simp⟩
  left_inv P := by
    apply Subtype.ext
    rcases twoTorsion_value_eq_zero_or_K P with hzero | hK
    · simp [hzero]
    · simp [hK, X017Model.K_ne_zero]
  right_inv b := by
    cases b <;> simp [X017Model.K_ne_zero]

/-- The standard `X₀(17)` model has exactly two rational points killed by
multiplication by two. -/
theorem natCard_twoTorsion :
    Nat.card (TwoTorsion (Point standard)) = 2 := by
  rw [Nat.card_congr twoTorsionEquivBool]
  simp

end

end MazurProof.X017TwoTorsion
