import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.TateOrder17
import FLT.Assumptions.MazurProof.TateOrder17Quotient

/-!
# Cyclic order 17 exclusion

## Strategy

1. `TateOrder17.exists_tate_parameters_of_order_seventeen` reduces a rational
   order-17 point to the Diophantine condition `F₁₇(b,c) = 0` with `b ≠ 0`.
2. An explicit algebraic map to the concrete `X₀(17)` model and its
   rational-point classification prove that this equation has no rational
   solution.
3. The two together give `no_rational_point_of_order_17`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

namespace CyclicExclusion17

/-- The Tate order-seventeen residual has no nondegenerate rational zero. -/
theorem no_F17_rational_solution :
    ∀ b c : ℚ, b ≠ 0 → TateNFDivision.F17 b c ≠ 0 :=
  TateOrder17Quotient.no_F17_rational_solution

end CyclicExclusion17

theorem no_rational_point_of_order_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 17 := by
  intro ⟨P, hP⟩
  obtain ⟨b, c, _, _, hb, hF17⟩ :=
    TateOrder17.exists_tate_parameters_of_order_seventeen E P hP
  exact CyclicExclusion17.no_F17_rational_solution b c hb hF17

end MazurProof
