import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.TateOrder19
import FLT.Assumptions.MazurProof.XDelta19RationalPoints

/-!
# Cyclic order 19 exclusion

## Strategy

1. `TateOrder19.exists_tate_parameters_of_order_nineteen` reduces a rational
   order-19 point to the Diophantine condition `F₁₉(b,c) = 0` with `b ≠ 0`.
2. The rational-point classification of the order-three diamond quotient
   proves that this equation has no rational solution.
3. The two together give `no_rational_point_of_order_19`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

namespace CyclicExclusion19

/-- The order-nineteen Tate residual has no rational zero away from the
degenerate boundary `b=0`. -/
theorem no_F19_rational_solution :
    ∀ b c : ℚ, b ≠ 0 → TateNFDivision.F19 b c ≠ 0 := by
  intro b c hb
  exact XDelta19RationalPoints.no_F19_rational_solution b c hb

end CyclicExclusion19

theorem no_rational_point_of_order_19
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 19 := by
  intro ⟨P, hP⟩
  obtain ⟨b, c, _, _, hb, hF19⟩ :=
    TateOrder19.exists_tate_parameters_of_order_nineteen E P hP
  exact CyclicExclusion19.no_F19_rational_solution b c hb hF19

end MazurProof
